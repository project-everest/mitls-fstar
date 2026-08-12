module DH.Sample.DY.Security

(**
  Authentication and secrecy consequences of the direct DY* history model.

  Successful concrete verification is deliberately isolated behind
  `crypto_simulation`: the abstract concrete crypto interface does not claim
  EUF-CMA.  Once an accepted signature is represented by the matching DY*
  `Sign` term, the authorization-or-compromise result is derived from the
  installed DY* invariant rather than assumed.
*)

module E = Common.Protocol.Labelled
module S = Common.Protocol.System
module G = Common.Protocol.System
module I = Common.Protocol.Interpretation
module SM = DH.Sample.StateMachine
module D = DH.Sample.DY.Terms
module P = DH.Sample.DY.Profile
module M = DH.Sample.DY.Model
module Inv = DH.Sample.DY.Invariant
module C = DH.Sample.DY.Coherence
module Protocol = DH.Sample.Protocol
module Crypto = DH.Sample.Crypto
module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module T = DY.Core.Trace.Type
module TB = DY.Core.Trace.Base
module TI = DY.Core.Trace.Invariant
module AK = DY.Core.Attacker.Knowledge
module List = FStar.List.Tot

open DH.Sample.Types
open DH.Sample.Wire

let role_long_term
  (who:E.endpoint_id)
  : BT.bytes
  =
  if who = SM.initiator_endpoint
  then D.long_term_term 0
  else D.long_term_term 2

let authorization_tag
  (who:E.endpoint_id)
  : string
  =
  if who = SM.initiator_endpoint
  then D.tag_authorize_initiator
  else D.tag_authorize_responder

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let verification_keys_distinct ()
  : Lemma
      (ensures
        D.verification_key_term (D.long_term_term 0) =!=
        D.verification_key_term (D.long_term_term 2))
  =
  normalize_term_spec B.vk;
  assert (
    D.verification_key_term (D.long_term_term 0) ==
      BT.Vk (BT.Rand D.long_term_length 0));
  assert (
    D.verification_key_term (D.long_term_term 2) ==
      BT.Vk (BT.Rand D.long_term_length 2))

let signature_parts_invariant
  (trace:TB.trace)
  (private_value nonce content:BT.bytes)
  : Lemma
      (requires
        B.bytes_invariant #P.dh_crypto_invariants trace
          (D.signature_term private_value nonce content))
      (ensures
        B.bytes_invariant #P.dh_crypto_invariants trace
          private_value /\
        B.bytes_invariant #P.dh_crypto_invariants trace
          nonce /\
        B.bytes_invariant #P.dh_crypto_invariants trace
          content)
  =
  reveal_opaque (`%B.sign) B.sign;
  assert (
    D.signature_term private_value nonce content ==
      BT.Sign private_value nonce content);
  reveal_opaque
    (`%B.bytes_invariant)
    (B.bytes_invariant #P.dh_crypto_invariants)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let signature_authorized_or_corrupt
  (trace:TB.trace)
  (who:E.endpoint_id{who == SM.initiator_endpoint \/
                     who == SM.responder_endpoint})
  (nonce content:BT.bytes)
  : Lemma
      (requires
        Inv.long_term_recorded
          who trace (role_long_term who) /\
        B.bytes_invariant #P.dh_crypto_invariants trace
          (D.signature_term
            (role_long_term who)
            nonce
            content))
      (ensures
        TB.event_triggered trace
          (D.role_principal who)
          (authorization_tag who)
          content \/
        L.is_corrupt trace (D.role_label who))
  =
  let private_value = role_long_term who in
  signature_parts_invariant
    trace private_value nonce content;
  Inv.long_term_facts who trace private_value;
  B.bytes_invariant_vk
    #P.dh_crypto_invariants trace private_value;
  B.has_signkey_usage_vk
    #P.dh_crypto_usages
    trace private_value D.long_term_usage;
  B.verify_sign private_value nonce content;
  B.bytes_invariant_verify
    #P.dh_crypto_invariants
    trace
    (D.verification_key_term private_value)
    D.long_term_usage
    content
    (D.signature_term private_value nonce content);
  B.get_signkey_label_vk
    #P.dh_crypto_usages trace private_value;
  L.flow_to_public_eq trace (D.role_label who);
  verification_keys_distinct ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let matching_key_label
  (trace:TB.trace)
  (initiator_private responder_private:BT.bytes)
  : Lemma
      (requires
        Inv.scalar_recorded
          SM.initiator_endpoint trace initiator_private /\
        Inv.scalar_recorded
          SM.responder_endpoint trace responder_private)
      (ensures
        B.get_label #P.dh_crypto_usages trace
          (D.secret_term
            initiator_private
            (D.share_term responder_private)) ==
        L.join
          (D.role_label SM.initiator_endpoint)
          (D.role_label SM.responder_endpoint))
  =
  Inv.scalar_facts
    SM.initiator_endpoint trace initiator_private;
  Inv.scalar_facts
    SM.responder_endpoint trace responder_private;
  B.get_label_dh
    #P.dh_crypto_usages trace
    initiator_private
    (D.share_term responder_private);
  B.get_dh_label_dh_pk
    #P.dh_crypto_usages trace responder_private

let matching_key_knowledge_implies_compromise
  (trace:TB.trace)
  (initiator_private responder_private:BT.bytes)
  : Lemma
      (requires
        Inv.scalar_recorded
          SM.initiator_endpoint trace initiator_private /\
        Inv.scalar_recorded
          SM.responder_endpoint trace responder_private /\
        TI.trace_invariant #P.dh_protocol_invariants trace /\
        AK.attacker_knows trace
          (D.secret_term
            initiator_private
            (D.share_term responder_private)))
      (ensures
        L.is_corrupt trace
          (D.role_label SM.initiator_endpoint) \/
        L.is_corrupt trace
          (D.role_label SM.responder_endpoint))
  =
  AK.attacker_only_knows_publishable_values
    #P.dh_protocol_invariants
    trace
    (D.secret_term
      initiator_private
      (D.share_term responder_private));
  matching_key_label
    trace initiator_private responder_private;
  L.flow_to_public_eq trace
    (L.join
      (D.role_label SM.initiator_endpoint)
      (D.role_label SM.responder_endpoint));
  L.is_corrupt_join trace
    (D.role_label SM.initiator_endpoint)
    (D.role_label SM.responder_endpoint)
#pop-options

let history_matching_key_secret
  (history:list
    (S.system_effect message scalar SM.semantic_event))
  (initiator_private responder_private:BT.bytes)
  : Lemma
      (requires (
        let trace = M.dy_trace_of_history history in
        Inv.scalar_recorded
          SM.initiator_endpoint trace initiator_private /\
        Inv.scalar_recorded
          SM.responder_endpoint trace responder_private /\
        AK.attacker_knows trace
          (D.secret_term
            initiator_private
            (D.share_term responder_private))))
      (ensures (
        let trace = M.dy_trace_of_history history in
        L.is_corrupt trace
          (D.role_label SM.initiator_endpoint) \/
        L.is_corrupt trace
          (D.role_label SM.responder_endpoint)))
  =
  Inv.history_trace_invariant history;
  matching_key_knowledge_implies_compromise
    (M.dy_trace_of_history history)
    initiator_private
    responder_private

let peer_endpoint (owner:E.endpoint_id) : E.endpoint_id =
  if owner = SM.initiator_endpoint
  then SM.responder_endpoint
  else SM.initiator_endpoint

let acceptance_view
  (state:M.model)
  (owner:E.endpoint_id)
  (partner:principal)
  (transcript symbolic_signature:BT.bytes)
  : prop
  =
  exists (shadow:M.endpoint_shadow).
    M.lookup state.M.endpoints owner == Some shadow /\
    M.acceptance_transcript owner shadow partner ==
      Some transcript /\
    M.accepted_signature owner shadow ==
      Some symbolic_signature

(**
  Explicit computational-to-symbolic boundary.  Every successful concrete
  signature acceptance must map either to the peer's DY* signature term or to
  prior compromise of the peer signing state.
*)
let acceptance_simulated
  (state:M.model)
  (owner:E.endpoint_id)
  (partner:principal)
  : prop
  =
  (owner == SM.initiator_endpoint \/
   owner == SM.responder_endpoint) /\
  (exists (transcript symbolic_signature:BT.bytes).
    acceptance_view
      state owner partner transcript symbolic_signature /\
    (L.is_corrupt
       state.M.dy_trace
       (D.role_label (peer_endpoint owner)) \/
     (exists (nonce:BT.bytes).
       symbolic_signature ==
         D.signature_term
           (role_long_term (peer_endpoint owner))
           nonce transcript /\
       B.bytes_invariant #P.dh_crypto_invariants
         state.M.dy_trace
         symbolic_signature)))

let rec crypto_simulation_from
  (state:M.model)
  (events:C.history)
  : Tot prop
      (decreases events)
  =
  match events with
  | [] -> True
  | event :: rest ->
    (match event with
     | G.ProtocolEffect owner
         (SM.SignatureAccepted _ partner _ _ _) ->
       acceptance_simulated state owner partner
     | _ -> True) /\
    crypto_simulation_from
      (I.interpret_one M.history_interpreter state event)
      rest

let crypto_simulation (events:C.history) : prop =
  crypto_simulation_from M.initial_model events

let rec acceptance_free (events:C.history) : Tot prop (decreases events) =
  match events with
  | [] -> True
  | event :: rest ->
    (match event with
     | G.ProtocolEffect _
         (SM.SignatureAccepted _ _ _ _ _) -> False
     | _ -> True) /\
    acceptance_free rest

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let rec acceptance_free_is_simulated
  (state:M.model)
  (events:C.history)
  : Lemma
      (requires acceptance_free events)
      (ensures crypto_simulation_from state events)
      (decreases events)
  =
  match events with
  | [] -> ()
  | event :: rest ->
    acceptance_free_is_simulated
      (I.interpret_one M.history_interpreter state event)
      rest

let singleton_acceptance_is_simulated
  (state:M.model)
  (owner:E.endpoint_id)
  (signer partner:principal)
  (initiator_share responder_share:share)
  (concrete_signature:signature)
  : Lemma
      (requires acceptance_simulated state owner partner)
      (ensures
        crypto_simulation_from state
          [ G.ProtocolEffect owner
              (SM.SignatureAccepted
                signer partner
                initiator_share responder_share
                concrete_signature) ])
  =
  ()

let rec crypto_simulation_from_append
  (state:M.model)
  (prefix suffix:C.history)
  : Lemma
      (requires
        crypto_simulation_from state prefix /\
        crypto_simulation_from
          (I.interpret_from
            M.history_interpreter state prefix)
          suffix)
      (ensures
        crypto_simulation_from state
          (List.append prefix suffix))
      (decreases prefix)
  =
  match prefix with
  | [] -> ()
  | event :: rest ->
    crypto_simulation_from_append
      (I.interpret_one M.history_interpreter state event)
      rest suffix
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let rec crypto_simulation_at_acceptance
  (state:M.model)
  (prefix suffix:C.history)
  (owner:E.endpoint_id)
  (signer partner:principal)
  (initiator_share responder_share:share)
  (concrete_signature:signature)
  : Lemma
      (requires
        crypto_simulation_from state
          (List.append prefix
            (G.ProtocolEffect owner
              (SM.SignatureAccepted
                signer partner
                initiator_share responder_share
                concrete_signature) ::
             suffix)))
      (ensures
        acceptance_simulated
          (I.interpret_from
            M.history_interpreter state prefix)
          owner partner)
      (decreases prefix)
  =
  match prefix with
  | [] -> ()
  | event :: rest ->
    crypto_simulation_at_acceptance
      (I.interpret_one M.history_interpreter state event)
      rest suffix
      owner signer partner
      initiator_share responder_share
      concrete_signature
#pop-options

let acceptance_authentication_result
  (prefix:C.history)
  (owner:E.endpoint_id)
  (partner:principal)
  : prop
  =
  exists (transcript symbolic_signature:BT.bytes).
    acceptance_view
      (M.interpret_history prefix)
      owner partner transcript symbolic_signature /\
    (TB.event_triggered
       (M.dy_trace_of_history prefix)
       (D.role_principal (peer_endpoint owner))
       (authorization_tag (peer_endpoint owner))
       transcript \/
     L.is_corrupt
       (M.dy_trace_of_history prefix)
       (D.role_label (peer_endpoint owner)))

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let accepted_signature_authenticates
  (events:C.history)
  (prefix suffix:C.history)
  (owner:E.endpoint_id)
  (signer partner:principal)
  (initiator_share responder_share:share)
  (concrete_signature:signature)
  : Lemma
      (requires
        (owner == SM.initiator_endpoint \/
         owner == SM.responder_endpoint) /\
        crypto_simulation events /\
        events ==
          List.append prefix
            (G.ProtocolEffect owner
              (SM.SignatureAccepted
                signer partner
                initiator_share responder_share
                concrete_signature) ::
             suffix))
      (ensures
        acceptance_authentication_result
          prefix owner partner)
  =
  crypto_simulation_at_acceptance
    M.initial_model prefix suffix
    owner signer partner
    initiator_share responder_share
    concrete_signature;
  assert (
    I.interpret_from
      M.history_interpreter M.initial_model prefix ==
    M.interpret_history prefix);
  assert (
    exists (transcript symbolic_signature:BT.bytes).
      acceptance_view
        (M.interpret_history prefix)
        owner partner transcript symbolic_signature /\
      (L.is_corrupt
         (M.dy_trace_of_history prefix)
         (D.role_label (peer_endpoint owner)) \/
       (exists (nonce:BT.bytes).
         symbolic_signature ==
           D.signature_term
             (role_long_term (peer_endpoint owner))
             nonce transcript /\
         B.bytes_invariant #P.dh_crypto_invariants
           (M.dy_trace_of_history prefix)
           symbolic_signature)));
  eliminate
    exists (transcript symbolic_signature:BT.bytes).
      acceptance_view
        (M.interpret_history prefix)
        owner partner transcript symbolic_signature /\
      (L.is_corrupt
         (M.dy_trace_of_history prefix)
         (D.role_label (peer_endpoint owner)) \/
       (exists (nonce:BT.bytes).
         symbolic_signature ==
           D.signature_term
             (role_long_term (peer_endpoint owner))
             nonce transcript /\
         B.bytes_invariant #P.dh_crypto_invariants
           (M.dy_trace_of_history prefix)
           symbolic_signature))
  returns
    acceptance_authentication_result prefix owner partner
  with _.
    (eliminate
       L.is_corrupt
         (M.dy_trace_of_history prefix)
         (D.role_label (peer_endpoint owner)) \/
       (exists (nonce:BT.bytes).
         symbolic_signature ==
           D.signature_term
             (role_long_term (peer_endpoint owner))
             nonce transcript /\
         B.bytes_invariant #P.dh_crypto_invariants
           (M.dy_trace_of_history prefix)
           symbolic_signature)
     returns
       acceptance_authentication_result prefix owner partner
     with _.
       introduce
         exists (accepted_transcript accepted_signature:BT.bytes).
           acceptance_view
             (M.interpret_history prefix)
             owner partner
             accepted_transcript accepted_signature /\
           (TB.event_triggered
              (M.dy_trace_of_history prefix)
              (D.role_principal (peer_endpoint owner))
              (authorization_tag (peer_endpoint owner))
              accepted_transcript \/
            L.is_corrupt
              (M.dy_trace_of_history prefix)
              (D.role_label (peer_endpoint owner)))
         with transcript symbolic_signature and ()
     and _.
       (Inv.history_model_invariant prefix;
        eliminate
          exists (initiator responder:M.endpoint_shadow).
            (M.interpret_history prefix).M.endpoints ==
              [ initiator; responder ] /\
            Inv.shadow_valid
              SM.initiator_endpoint
              (M.dy_trace_of_history prefix)
              initiator /\
            Inv.shadow_valid
              SM.responder_endpoint
              (M.dy_trace_of_history prefix)
              responder
        returns
          acceptance_authentication_result prefix owner partner
        with _.
          (eliminate
             exists (nonce:BT.bytes).
               symbolic_signature ==
                 D.signature_term
                   (role_long_term (peer_endpoint owner))
                   nonce transcript /\
               B.bytes_invariant #P.dh_crypto_invariants
                 (M.dy_trace_of_history prefix)
                 symbolic_signature
           returns
             acceptance_authentication_result prefix owner partner
           with _.
             (if owner = SM.initiator_endpoint
              then
                signature_authorized_or_corrupt
                  (M.dy_trace_of_history prefix)
                  SM.responder_endpoint
                  nonce transcript
              else
                signature_authorized_or_corrupt
                  (M.dy_trace_of_history prefix)
                  SM.initiator_endpoint
                  nonce transcript;
              introduce
                exists
                  (accepted_transcript accepted_signature:BT.bytes).
                  acceptance_view
                    (M.interpret_history prefix)
                    owner partner
                    accepted_transcript accepted_signature /\
                  (TB.event_triggered
                     (M.dy_trace_of_history prefix)
                     (D.role_principal (peer_endpoint owner))
                     (authorization_tag (peer_endpoint owner))
                     accepted_transcript \/
                   L.is_corrupt
                     (M.dy_trace_of_history prefix)
                     (D.role_label (peer_endpoint owner)))
                with transcript symbolic_signature and ()))))
#pop-options

unfold
let completed_authentication (events:C.history) : prop =
  forall
    (owner:E.endpoint_id)
    (peer:principal)
    (key:session_key).
    C.occurs
      (G.ProtocolEffect owner (SM.Completed peer key))
      events
    ==>
    (exists
      (partner:principal)
      (initiator_share responder_share:share)
      (concrete_signature:signature)
      (prefix middle suffix:C.history).
      events ==
        List.append prefix
          (G.ProtocolEffect owner
            (SM.SignatureAccepted
              peer partner
              initiator_share responder_share
              concrete_signature) ::
           List.append middle
             (G.ProtocolEffect owner (SM.Completed peer key) ::
              suffix)) /\
      acceptance_authentication_result
        prefix owner partner)

#push-options "--fuel 8 --ifuel 2 --z3rlimit 10 --split_queries always"
let completion_authentication_one
  (events:C.history)
  (owner:E.endpoint_id)
  (peer:principal)
  (key:session_key)
  : Lemma
      (requires
        C.completion_coherent events /\
        crypto_simulation events /\
        C.occurs
          (G.ProtocolEffect owner (SM.Completed peer key))
          events)
      (ensures
        exists
          (partner:principal)
          (initiator_share responder_share:share)
          (concrete_signature:signature)
          (prefix middle suffix:C.history).
          events ==
            List.append prefix
              (G.ProtocolEffect owner
                (SM.SignatureAccepted
                  peer partner
                  initiator_share responder_share
                  concrete_signature) ::
               List.append middle
                 (G.ProtocolEffect owner (SM.Completed peer key) ::
                  suffix)) /\
          acceptance_authentication_result
            prefix owner partner)
  =
  assert (C.completion_evidence events owner peer key);
  assert (
    owner == SM.initiator_endpoint \/
    owner == SM.responder_endpoint);
  assert (
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (concrete_signature:signature).
      C.before
        (G.ProtocolEffect owner
          (SM.SignatureAccepted
            peer partner
            initiator_share responder_share
            concrete_signature))
        (G.ProtocolEffect owner (SM.Completed peer key))
        events);
  eliminate
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (concrete_signature:signature).
      C.before
        (G.ProtocolEffect owner
          (SM.SignatureAccepted
            peer partner
            initiator_share responder_share
            concrete_signature))
        (G.ProtocolEffect owner (SM.Completed peer key))
        events
  returns
    exists
      (partner:principal)
      (initiator_share responder_share:share)
      (concrete_signature:signature)
      (prefix middle suffix:C.history).
      events ==
        List.append prefix
          (G.ProtocolEffect owner
            (SM.SignatureAccepted
              peer partner
              initiator_share responder_share
              concrete_signature) ::
           List.append middle
             (G.ProtocolEffect owner (SM.Completed peer key) ::
              suffix)) /\
      acceptance_authentication_result
        prefix owner partner
  with _.
    (C.before_split
       (G.ProtocolEffect owner
         (SM.SignatureAccepted
           peer partner
           initiator_share responder_share
           concrete_signature))
       (G.ProtocolEffect owner (SM.Completed peer key))
       events;
     eliminate
       exists (prefix middle suffix:C.history).
         events ==
           List.append prefix
             (G.ProtocolEffect owner
               (SM.SignatureAccepted
                 peer partner
                 initiator_share responder_share
                 concrete_signature) ::
              List.append middle
                (G.ProtocolEffect owner (SM.Completed peer key) ::
                 suffix))
     returns
       exists
         (accepted_partner:principal)
         (gx gy:share)
         (accepted_signature:signature)
         (prefix' middle' suffix':C.history).
         events ==
           List.append prefix'
             (G.ProtocolEffect owner
               (SM.SignatureAccepted
                 peer accepted_partner
                 gx gy accepted_signature) ::
              List.append middle'
                (G.ProtocolEffect owner (SM.Completed peer key) ::
                 suffix')) /\
         acceptance_authentication_result
           prefix' owner accepted_partner
     with _.
       (accepted_signature_authenticates
          events
          prefix
          (List.append middle
            (G.ProtocolEffect owner (SM.Completed peer key) ::
             suffix))
          owner
          peer partner
          initiator_share responder_share
          concrete_signature;
        introduce
          exists
            (accepted_partner:principal)
            (gx gy:share)
            (accepted_signature:signature)
            (prefix' middle' suffix':C.history).
            events ==
              List.append prefix'
                (G.ProtocolEffect owner
                  (SM.SignatureAccepted
                    peer accepted_partner
                    gx gy accepted_signature) ::
                 List.append middle'
                   (G.ProtocolEffect owner
                     (SM.Completed peer key) ::
                    suffix')) /\
            acceptance_authentication_result
              prefix' owner accepted_partner
          with
            partner
            initiator_share responder_share
            concrete_signature
            prefix middle suffix
          and ()))

let completion_authentication
  (events:C.history)
  : Lemma
      (requires
        C.completion_coherent events /\
        crypto_simulation events)
      (ensures
        completed_authentication events)
  =
  introduce forall
    (owner:E.endpoint_id)
    (peer:principal)
    (key:session_key).
    C.occurs
      (G.ProtocolEffect owner (SM.Completed peer key))
      events
    ==>
    (exists
      (partner:principal)
      (initiator_share responder_share:share)
      (concrete_signature:signature)
      (prefix middle suffix:C.history).
      events ==
        List.append prefix
          (G.ProtocolEffect owner
            (SM.SignatureAccepted
              peer partner
              initiator_share responder_share
              concrete_signature) ::
           List.append middle
             (G.ProtocolEffect owner (SM.Completed peer key) ::
              suffix)) /\
      acceptance_authentication_result
        prefix owner partner)
  with begin
    introduce
      C.occurs
        (G.ProtocolEffect owner (SM.Completed peer key))
        events
      ==>
      (exists
        (partner:principal)
        (initiator_share responder_share:share)
        (concrete_signature:signature)
        (prefix middle suffix:C.history).
        events ==
          List.append prefix
            (G.ProtocolEffect owner
              (SM.SignatureAccepted
                peer partner
                initiator_share responder_share
                concrete_signature) ::
             List.append middle
               (G.ProtocolEffect owner (SM.Completed peer key) ::
                suffix)) /\
        acceptance_authentication_result
          prefix owner partner)
    with _.
      completion_authentication_one events owner peer key
  end
#pop-options

let reachable_completed_authentication
  (initiator responder:principal)
  (transitions:list Protocol.protocol_transition)
  (state:Protocol.protocol_state)
  : Lemma
      (requires
        Protocol.trace_reaches
          initiator responder
          (Protocol.initial initiator responder)
          transitions state /\
        crypto_simulation state.G.history)
      (ensures
        completed_authentication state.G.history)
  =
  C.reachable_completion_coherent
    initiator responder transitions state;
  completion_authentication state.G.history

let matching_session_key_agreement
  (initiator_private responder_private:BT.bytes)
  : Lemma
      (ensures
        D.secret_term
          initiator_private
          (D.share_term responder_private) ==
        D.secret_term
          responder_private
          (D.share_term initiator_private))
  =
  D.lemma_dh_agreement initiator_private responder_private

unfold
let matching_key_secrecy (events:C.history) : prop =
  forall (initiator_private responder_private:BT.bytes).
    let trace = M.dy_trace_of_history events in
    Inv.scalar_recorded
      SM.initiator_endpoint trace initiator_private /\
    Inv.scalar_recorded
      SM.responder_endpoint trace responder_private /\
    AK.attacker_knows trace
      (D.secret_term
        initiator_private
        (D.share_term responder_private))
    ==>
    (L.is_corrupt trace
       (D.role_label SM.initiator_endpoint) \/
     L.is_corrupt trace
       (D.role_label SM.responder_endpoint))

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let all_matching_keys_secret (events:C.history)
  : Lemma (ensures matching_key_secrecy events)
  =
  introduce forall
    (initiator_private responder_private:BT.bytes).
    (let trace = M.dy_trace_of_history events in
     Inv.scalar_recorded
       SM.initiator_endpoint trace initiator_private /\
     Inv.scalar_recorded
       SM.responder_endpoint trace responder_private /\
     AK.attacker_knows trace
       (D.secret_term
         initiator_private
         (D.share_term responder_private)))
    ==>
    (let trace = M.dy_trace_of_history events in
     L.is_corrupt trace
       (D.role_label SM.initiator_endpoint) \/
     L.is_corrupt trace
       (D.role_label SM.responder_endpoint))
  with begin
    introduce
      (let trace = M.dy_trace_of_history events in
       Inv.scalar_recorded
         SM.initiator_endpoint trace initiator_private /\
       Inv.scalar_recorded
         SM.responder_endpoint trace responder_private /\
       AK.attacker_knows trace
         (D.secret_term
           initiator_private
           (D.share_term responder_private)))
      ==>
      (let trace = M.dy_trace_of_history events in
       L.is_corrupt trace
         (D.role_label SM.initiator_endpoint) \/
       L.is_corrupt trace
         (D.role_label SM.responder_endpoint))
    with _.
      history_matching_key_secret
        events initiator_private responder_private
  end
#pop-options

unfold
let security_consequences (events:C.history) : prop =
  TI.trace_invariant
    #P.dh_protocol_invariants
    (M.dy_trace_of_history events) /\
  completed_authentication events /\
  matching_key_secrecy events

let reachable_security
  (initiator responder:principal)
  (transitions:list Protocol.protocol_transition)
  (state:Protocol.protocol_state)
  : Lemma
      (requires
        Protocol.trace_reaches
          initiator responder
          (Protocol.initial initiator responder)
          transitions state /\
        crypto_simulation state.G.history)
      (ensures
        security_consequences state.G.history)
  =
  Inv.history_trace_invariant state.G.history;
  reachable_completed_authentication
    initiator responder transitions state;
  all_matching_keys_secret state.G.history

let honest_responder_acceptance_prefix
  (initiator responder:principal)
  (initiator_private responder_private:scalar)
  : C.history
  =
  let initiator_share = Crypto.public_share initiator_private in
  let responder_share = Crypto.public_share responder_private in
  let responder_signature =
    Crypto.sign responder
      (Crypto.transcript
        initiator initiator_share responder_share)
  in
  [
    G.Generated SM.initiator_endpoint initiator_private;
    G.ProtocolEffect SM.initiator_endpoint
      (SM.PublicShare initiator_private initiator_share);
    G.ObservedSend SM.initiator_endpoint 0
      (Message1 initiator initiator_share);
    G.ObservedReceive SM.responder_endpoint 0
      (Message1 initiator initiator_share);
    G.Generated SM.responder_endpoint responder_private;
    G.ProtocolEffect SM.responder_endpoint
      (SM.PublicShare responder_private responder_share);
    G.ProtocolEffect SM.responder_endpoint
      (SM.SharedSecret
        responder_private initiator_share
        (Crypto.derive responder_private initiator_share));
    G.ProtocolEffect SM.responder_endpoint
      (SM.SignatureCreated
        responder initiator
        initiator_share responder_share
        responder_signature);
    G.ObservedSend SM.responder_endpoint 1
      (Message2
        responder responder_share responder_signature);
    G.ObservedReceive SM.initiator_endpoint 1
      (Message2
        responder responder_share responder_signature);
  ]

let honest_responder_acceptance_history
  (initiator responder:principal)
  (initiator_private responder_private:scalar)
  : C.history
  =
  let initiator_share = Crypto.public_share initiator_private in
  let responder_share = Crypto.public_share responder_private in
  let responder_signature =
    Crypto.sign responder
      (Crypto.transcript
        initiator initiator_share responder_share)
  in
  List.append
    (honest_responder_acceptance_prefix
      initiator responder
      initiator_private responder_private)
    [
      G.ProtocolEffect SM.initiator_endpoint
        (SM.SignatureAccepted
          responder initiator
          initiator_share responder_share
          responder_signature)
    ]

let honest_symbolic_transcript (initiator:principal) : BT.bytes =
  D.transcript_term
    (D.principal_term initiator)
    (D.share_term (D.ephemeral_term 4))
    (D.share_term (D.ephemeral_term 7))

let honest_symbolic_responder_signature
  (initiator:principal)
  : BT.bytes
  =
  D.signature_term
    (D.long_term_term 2)
    (D.signing_nonce_term 11)
    (honest_symbolic_transcript initiator)

let honest_initiator_shadow_after_msg2
  (initiator responder:principal)
  : M.endpoint_shadow
  =
  {
    M.long_term = D.long_term_term 0;
    M.private_value = Some (D.ephemeral_term 4);
    M.own_share = Some (D.share_term (D.ephemeral_term 4));
    M.peer_share = None;
    M.key = None;
    M.pending_signature = None;
    M.last_received =
      Some (
        D.SymbolicMessage2
          (D.principal_term responder)
          (D.share_term (D.ephemeral_term 7))
          (honest_symbolic_responder_signature initiator));
    M.state_position = 5;
  }

let honest_symbolic_responder_signature_genuine
  (initiator:principal)
  (trace:TB.trace)
  : Lemma
      (requires
        B.bytes_invariant #P.dh_crypto_invariants trace
          (honest_symbolic_responder_signature initiator))
      (ensures
        exists (nonce:BT.bytes).
          honest_symbolic_responder_signature initiator ==
            D.signature_term
              (D.long_term_term 2)
              nonce
              (honest_symbolic_transcript initiator) /\
          B.bytes_invariant #P.dh_crypto_invariants trace
            (honest_symbolic_responder_signature initiator))
  =
  introduce
    exists (nonce:BT.bytes).
      honest_symbolic_responder_signature initiator ==
        D.signature_term
          (D.long_term_term 2)
          nonce
          (honest_symbolic_transcript initiator) /\
      B.bytes_invariant #P.dh_crypto_invariants trace
        (honest_symbolic_responder_signature initiator)
  with (D.signing_nonce_term 11) and ()

let honest_responder_acceptance_by_genuine_signature
  (state:M.model)
  (initiator:principal)
  : Lemma
      (requires
        acceptance_view
          state
          SM.initiator_endpoint
          initiator
          (honest_symbolic_transcript initiator)
          (honest_symbolic_responder_signature initiator) /\
        B.bytes_invariant #P.dh_crypto_invariants state.M.dy_trace
          (honest_symbolic_responder_signature initiator))
      (ensures
        acceptance_simulated
          state SM.initiator_endpoint initiator)
  =
  honest_symbolic_responder_signature_genuine
    initiator state.M.dy_trace;
  introduce
    exists (transcript symbolic_signature:BT.bytes).
      acceptance_view
        state
        SM.initiator_endpoint
        initiator
        transcript
        symbolic_signature /\
      (L.is_corrupt
         state.M.dy_trace
         (D.role_label (peer_endpoint SM.initiator_endpoint)) \/
       (exists (nonce:BT.bytes).
         symbolic_signature ==
           D.signature_term
             (role_long_term
               (peer_endpoint SM.initiator_endpoint))
             nonce transcript /\
         B.bytes_invariant #P.dh_crypto_invariants
           state.M.dy_trace
           symbolic_signature))
  with
    (honest_symbolic_transcript initiator)
    (honest_symbolic_responder_signature initiator)
  and ()

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10 --split_queries always"
let honest_responder_acceptance_simulated
  (initiator responder:principal)
  (initiator_private responder_private:scalar)
  : Lemma
      (ensures
        crypto_simulation
          (honest_responder_acceptance_history
            initiator responder
            initiator_private responder_private))
  =
  Inv.history_model_invariant
    (honest_responder_acceptance_prefix
      initiator responder
      initiator_private responder_private);
  normalize_term_spec M.interpret_history;
  assert (
    M.lookup
      (M.interpret_history
        (honest_responder_acceptance_prefix
          initiator responder
          initiator_private responder_private)).M.endpoints
      SM.initiator_endpoint ==
    Some (honest_initiator_shadow_after_msg2
      initiator responder))
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.trefl ());
  assert (
    acceptance_view
      (M.interpret_history
        (honest_responder_acceptance_prefix
          initiator responder
          initiator_private responder_private))
      SM.initiator_endpoint
      initiator
      (honest_symbolic_transcript initiator)
      (honest_symbolic_responder_signature initiator));
  assert (
    B.bytes_invariant #P.dh_crypto_invariants
      (M.dy_trace_of_history
        (honest_responder_acceptance_prefix
          initiator responder
          initiator_private responder_private))
      (honest_symbolic_responder_signature initiator));
  honest_symbolic_responder_signature_genuine
    initiator
    (M.dy_trace_of_history
      (honest_responder_acceptance_prefix
        initiator responder
        initiator_private responder_private));
  honest_responder_acceptance_by_genuine_signature
    (M.interpret_history
      (honest_responder_acceptance_prefix
        initiator responder
        initiator_private responder_private))
    initiator;
  assert (
    acceptance_free
      (honest_responder_acceptance_prefix
        initiator responder
        initiator_private responder_private))
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  acceptance_free_is_simulated
    M.initial_model
    (honest_responder_acceptance_prefix
      initiator responder
      initiator_private responder_private);
  singleton_acceptance_is_simulated
    (M.interpret_history
      (honest_responder_acceptance_prefix
        initiator responder
        initiator_private responder_private))
    SM.initiator_endpoint
    responder initiator
    (Crypto.public_share initiator_private)
    (Crypto.public_share responder_private)
    (Crypto.sign responder
      (Crypto.transcript
        initiator
        (Crypto.public_share initiator_private)
        (Crypto.public_share responder_private)));
  crypto_simulation_from_append
    M.initial_model
    (honest_responder_acceptance_prefix
      initiator responder
      initiator_private responder_private)
    [
      G.ProtocolEffect SM.initiator_endpoint
        (SM.SignatureAccepted
          responder initiator
          (Crypto.public_share initiator_private)
          (Crypto.public_share responder_private)
          (Crypto.sign responder
            (Crypto.transcript
              initiator
              (Crypto.public_share initiator_private)
              (Crypto.public_share responder_private)))
        )
    ]
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let empty_crypto_simulation ()
  : Lemma (ensures crypto_simulation [])
  = ()

let initial_security
  (initiator responder:principal)
  : Lemma
      (ensures
        security_consequences
          (Protocol.initial initiator responder).G.history)
  =
  empty_crypto_simulation ();
  reachable_security
    initiator responder
    []
    (Protocol.initial initiator responder)
#pop-options
