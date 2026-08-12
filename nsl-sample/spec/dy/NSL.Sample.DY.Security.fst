module NSL.Sample.DY.Security

(**
  Direct DY* authentication and nonce-secrecy consequences for NSL.

  Concrete successful decryption crosses one explicit prefix-local simulation
  boundary.  From a genuine DY* PKE term, the core invariant derives either the
  corresponding protocol authorization event or public plaintext; honest nonce
  secrecy then turns public plaintext into endpoint compromise.
 *)

module E = Common.Protocol.Labelled
module G = Common.Protocol.System
module I = Common.Protocol.Interpretation
module SM = NSL.Sample.StateMachine
module D = NSL.Sample.DY.Terms
module P = NSL.Sample.DY.Profile
module M = NSL.Sample.DY.Model
module Inv = NSL.Sample.DY.Invariant
module C = NSL.Sample.DY.Coherence
module Protocol = NSL.Sample.Protocol
module Crypto = NSL.Sample.Crypto
module BaseSM = Common.StateMachine
module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module TB = DY.Core.Trace.Base
module TI = DY.Core.Trace.Invariant
module AK = DY.Core.Attacker.Knowledge
module List = FStar.List.Tot

open NSL.Sample.Types
open NSL.Sample.Wire

let peer_endpoint (owner:E.endpoint_id) : E.endpoint_id =
  if owner = SM.initiator_endpoint
  then SM.responder_endpoint
  else SM.initiator_endpoint

let acceptance_plaintext
  (shadow:M.endpoint_shadow)
  (concrete_plaintext:plaintext)
  : M.symbolic_plaintext
  =
  match M.received_plaintext shadow with
  | Some value -> value
  | None -> M.accepted_plaintext_term shadow concrete_plaintext

let acceptance_view
  (state:M.model)
  (owner:E.endpoint_id)
  (concrete_plaintext:plaintext)
  (symbolic_plaintext:M.symbolic_plaintext)
  (symbolic_ciphertext:BT.bytes)
  : prop
  =
  exists (shadow:M.endpoint_shadow).
    M.lookup state.M.endpoints owner == Some shadow /\
    symbolic_plaintext ==
      acceptance_plaintext shadow concrete_plaintext /\
    M.accepted_ciphertext shadow == Some symbolic_ciphertext

(**
  Computational-to-symbolic PKE boundary.  A successful concrete decryption is
  represented by the exact symbolic plaintext and either prior key compromise
  or a genuine, invariant-satisfying ciphertext under the recipient role key.
 *)
let decryption_simulated
  (state:M.model)
  (owner:E.endpoint_id)
  (concrete_plaintext:plaintext)
  : prop
  =
  (owner == SM.initiator_endpoint \/
   owner == SM.responder_endpoint) /\
  exists
    (symbolic_plaintext:M.symbolic_plaintext)
    (symbolic_ciphertext:BT.bytes).
    acceptance_view
      state owner concrete_plaintext
      symbolic_plaintext symbolic_ciphertext /\
    (L.is_corrupt state.M.dy_trace (D.role_label owner) \/
     exists (encryption_nonce:BT.bytes).
       symbolic_ciphertext ==
         D.ciphertext_term
           (D.role_public_key owner)
           encryption_nonce
           (M.flatten_plaintext symbolic_plaintext) /\
       B.bytes_invariant #P.nsl_crypto_invariants
         state.M.dy_trace symbolic_ciphertext)

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
         (SM.CiphertextAccepted _ plaintext _) ->
       decryption_simulated state owner plaintext
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
         (SM.CiphertextAccepted _ _ _) -> False
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

let rec crypto_simulation_from_append
  (state:M.model)
  (prefix suffix:C.history)
  : Lemma
      (requires
        crypto_simulation_from state prefix /\
        crypto_simulation_from
          (I.interpret_from M.history_interpreter state prefix)
          suffix)
      (ensures
        crypto_simulation_from state (List.append prefix suffix))
      (decreases prefix)
  =
  match prefix with
  | [] -> ()
  | event :: rest ->
    crypto_simulation_from_append
      (I.interpret_one M.history_interpreter state event)
      rest suffix

let rec crypto_simulation_at_acceptance
  (state:M.model)
  (prefix suffix:C.history)
  (owner:E.endpoint_id)
  (recipient:principal)
  (plaintext:plaintext)
  (ciphertext:ciphertext)
  : Lemma
      (requires
        crypto_simulation_from state
          (List.append prefix
            (G.ProtocolEffect owner
              (SM.CiphertextAccepted
                recipient plaintext ciphertext) ::
             suffix)))
      (ensures
        decryption_simulated
          (I.interpret_from
            M.history_interpreter state prefix)
          owner plaintext)
      (decreases prefix)
  =
  match prefix with
  | [] -> ()
  | event :: rest ->
    crypto_simulation_at_acceptance
      (I.interpret_one M.history_interpreter state event)
      rest suffix owner recipient plaintext ciphertext
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let genuine_decryption_authorized_or_public
  (trace:TB.trace)
  (owner:E.endpoint_id{owner == SM.initiator_endpoint \/
                       owner == SM.responder_endpoint})
  (encryption_nonce plaintext:BT.bytes)
  : Lemma
      (requires
        Inv.key_recorded owner trace (D.role_secret_key owner) /\
        B.bytes_invariant #P.nsl_crypto_invariants trace
          (D.ciphertext_term
            (D.role_public_key owner)
            encryption_nonce plaintext))
      (ensures
        P.pke_predicate
          trace (D.key_usage owner)
          (D.role_public_key owner) plaintext \/
        B.get_label #P.nsl_crypto_usages trace plaintext
          `L.can_flow trace` L.public)
  =
  Inv.key_facts owner trace (D.role_secret_key owner);
  D.lemma_decrypt_encrypt
    (D.role_secret_key owner)
    encryption_nonce plaintext;
  B.bytes_invariant_pke_dec
    #P.nsl_crypto_invariants trace
    (D.role_secret_key owner)
    (D.key_usage owner)
    (D.ciphertext_term
      (D.role_public_key owner)
      encryption_nonce plaintext)
#pop-options

let decryption_authentication_result
  (prefix:C.history)
  (owner:E.endpoint_id)
  (concrete_plaintext:plaintext)
  : prop
  =
  exists
    (symbolic_plaintext:M.symbolic_plaintext)
    (symbolic_ciphertext:BT.bytes).
    acceptance_view
      (M.interpret_history prefix)
      owner concrete_plaintext
      symbolic_plaintext symbolic_ciphertext /\
    (L.is_corrupt
       (M.dy_trace_of_history prefix)
       (D.role_label owner) \/
     P.pke_predicate
       (M.dy_trace_of_history prefix)
       (D.key_usage owner)
       (D.role_public_key owner)
       (M.flatten_plaintext symbolic_plaintext) \/
     B.get_label #P.nsl_crypto_usages
       (M.dy_trace_of_history prefix)
       (M.flatten_plaintext symbolic_plaintext)
       `L.can_flow (M.dy_trace_of_history prefix)`
       L.public)

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let accepted_ciphertext_authenticates
  (events:C.history)
  (prefix suffix:C.history)
  (owner:E.endpoint_id)
  (recipient:principal)
  (plaintext:plaintext)
  (ciphertext:ciphertext)
  : Lemma
      (requires
        (owner == SM.initiator_endpoint \/
         owner == SM.responder_endpoint) /\
        crypto_simulation events /\
        events ==
          List.append prefix
            (G.ProtocolEffect owner
              (SM.CiphertextAccepted
                recipient plaintext ciphertext) ::
             suffix))
      (ensures
        decryption_authentication_result
          prefix owner plaintext)
  =
  crypto_simulation_at_acceptance
    M.initial_model prefix suffix
    owner recipient plaintext ciphertext;
  assert (
    I.interpret_from
      M.history_interpreter M.initial_model prefix ==
    M.interpret_history prefix);
  Inv.history_model_invariant prefix;
  eliminate
    exists
      (symbolic_plaintext:M.symbolic_plaintext)
      (symbolic_ciphertext:BT.bytes).
      acceptance_view
        (M.interpret_history prefix)
        owner plaintext
        symbolic_plaintext symbolic_ciphertext /\
      (L.is_corrupt
         (M.dy_trace_of_history prefix)
         (D.role_label owner) \/
       exists (encryption_nonce:BT.bytes).
         symbolic_ciphertext ==
           D.ciphertext_term
             (D.role_public_key owner)
             encryption_nonce
             (M.flatten_plaintext symbolic_plaintext) /\
         B.bytes_invariant #P.nsl_crypto_invariants
           (M.dy_trace_of_history prefix)
           symbolic_ciphertext)
  returns
    decryption_authentication_result prefix owner plaintext
  with _.
    (eliminate
       L.is_corrupt
         (M.dy_trace_of_history prefix)
         (D.role_label owner) \/
       (exists (encryption_nonce:BT.bytes).
         symbolic_ciphertext ==
           D.ciphertext_term
             (D.role_public_key owner)
             encryption_nonce
             (M.flatten_plaintext symbolic_plaintext) /\
         B.bytes_invariant #P.nsl_crypto_invariants
           (M.dy_trace_of_history prefix)
           symbolic_ciphertext)
     returns
       decryption_authentication_result prefix owner plaintext
     with _.
       introduce
         exists
           (symbolic_plaintext':M.symbolic_plaintext)
           (symbolic_ciphertext':BT.bytes).
           acceptance_view
             (M.interpret_history prefix)
             owner plaintext
             symbolic_plaintext' symbolic_ciphertext' /\
           (L.is_corrupt
              (M.dy_trace_of_history prefix)
              (D.role_label owner) \/
            P.pke_predicate
              (M.dy_trace_of_history prefix)
              (D.key_usage owner)
              (D.role_public_key owner)
              (M.flatten_plaintext symbolic_plaintext') \/
            B.get_label #P.nsl_crypto_usages
              (M.dy_trace_of_history prefix)
              (M.flatten_plaintext symbolic_plaintext')
              `L.can_flow (M.dy_trace_of_history prefix)`
              L.public)
       with symbolic_plaintext symbolic_ciphertext and ()
     and _.
       (eliminate
          exists (encryption_nonce:BT.bytes).
            symbolic_ciphertext ==
              D.ciphertext_term
                (D.role_public_key owner)
                encryption_nonce
                (M.flatten_plaintext symbolic_plaintext) /\
            B.bytes_invariant #P.nsl_crypto_invariants
              (M.dy_trace_of_history prefix)
              symbolic_ciphertext
        returns
          decryption_authentication_result prefix owner plaintext
        with _.
          (genuine_decryption_authorized_or_public
             (M.dy_trace_of_history prefix)
             owner encryption_nonce
             (M.flatten_plaintext symbolic_plaintext);
           introduce
             exists
               (symbolic_plaintext':M.symbolic_plaintext)
               (symbolic_ciphertext':BT.bytes).
               acceptance_view
                 (M.interpret_history prefix)
                 owner plaintext
                 symbolic_plaintext' symbolic_ciphertext' /\
               (L.is_corrupt
                  (M.dy_trace_of_history prefix)
                  (D.role_label owner) \/
                P.pke_predicate
                  (M.dy_trace_of_history prefix)
                  (D.key_usage owner)
                  (D.role_public_key owner)
                  (M.flatten_plaintext symbolic_plaintext') \/
                B.get_label #P.nsl_crypto_usages
                  (M.dy_trace_of_history prefix)
                  (M.flatten_plaintext symbolic_plaintext')
                  `L.can_flow (M.dy_trace_of_history prefix)`
                  L.public)
           with symbolic_plaintext symbolic_ciphertext and ())))
#pop-options

unfold
let completed_authentication (events:C.history) : prop =
  forall
    (owner:E.endpoint_id)
    (peer:principal)
    (initiator_nonce responder_nonce:nonce).
    C.occurs
      (G.ProtocolEffect owner
        (SM.Completed peer initiator_nonce responder_nonce))
      events
    ==>
    exists
      (recipient:principal)
      (plaintext:plaintext)
      (ciphertext:ciphertext)
      (prefix middle suffix:C.history).
      events ==
        List.append prefix
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted
              recipient plaintext ciphertext) ::
           List.append middle
             (G.ProtocolEffect owner
               (SM.Completed
                 peer initiator_nonce responder_nonce) ::
              suffix)) /\
      decryption_authentication_result
        prefix owner plaintext

#push-options "--fuel 8 --ifuel 2 --z3rlimit 10 --split_queries always"
let completion_authentication_one
  (events:C.history)
  (owner:E.endpoint_id)
  (peer:principal)
  (initiator_nonce responder_nonce:nonce)
  : Lemma
      (requires
        C.completion_coherent events /\
        crypto_simulation events /\
        C.occurs
          (G.ProtocolEffect owner
            (SM.Completed peer initiator_nonce responder_nonce))
          events)
      (ensures
        exists
          (recipient:principal)
          (plaintext:plaintext)
          (ciphertext:ciphertext)
          (prefix middle suffix:C.history).
          events ==
            List.append prefix
              (G.ProtocolEffect owner
                (SM.CiphertextAccepted
                  recipient plaintext ciphertext) ::
               List.append middle
                 (G.ProtocolEffect owner
                   (SM.Completed
                     peer initiator_nonce responder_nonce) ::
                  suffix)) /\
          decryption_authentication_result
            prefix owner plaintext)
  =
  assert (
    C.completion_evidence
      events owner peer initiator_nonce responder_nonce);
  eliminate
    (owner == SM.initiator_endpoint /\
      exists
        (recipient:principal)
        (ciphertext1:ciphertext).
        C.before
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted recipient
              (PlainMessage2
                initiator_nonce responder_nonce peer)
              ciphertext1))
          (G.ProtocolEffect owner
            (SM.Completed peer initiator_nonce responder_nonce))
          events) \/
    (owner == SM.responder_endpoint /\
      exists
        (recipient:principal)
        (ciphertext2:ciphertext).
        C.before
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted recipient
              (PlainMessage3 responder_nonce)
              ciphertext2))
          (G.ProtocolEffect owner
            (SM.Completed peer initiator_nonce responder_nonce))
          events)
  returns
    exists
      (recipient:principal)
      (plaintext:plaintext)
      (ciphertext:ciphertext)
      (prefix middle suffix:C.history).
      events ==
        List.append prefix
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted
              recipient plaintext ciphertext) ::
           List.append middle
             (G.ProtocolEffect owner
               (SM.Completed
                 peer initiator_nonce responder_nonce) ::
              suffix)) /\
      decryption_authentication_result prefix owner plaintext
  with _.
    (eliminate
       exists
         (recipient:principal)
         (accepted_ciphertext:ciphertext).
         C.before
           (G.ProtocolEffect owner
             (SM.CiphertextAccepted recipient
               (PlainMessage2
                 initiator_nonce responder_nonce peer)
               accepted_ciphertext))
           (G.ProtocolEffect owner
             (SM.Completed peer initiator_nonce responder_nonce))
           events
     returns
       exists
         (recipient':principal)
         (plaintext:plaintext)
         (ciphertext':ciphertext)
         (prefix middle suffix:C.history).
         events ==
           List.append prefix
             (G.ProtocolEffect owner
               (SM.CiphertextAccepted
                 recipient' plaintext ciphertext') ::
              List.append middle
                (G.ProtocolEffect owner
                  (SM.Completed
                    peer initiator_nonce responder_nonce) ::
                 suffix)) /\
         decryption_authentication_result prefix owner plaintext
     with _.
       (C.before_split
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted recipient
              (PlainMessage2
                initiator_nonce responder_nonce peer)
              accepted_ciphertext))
          (G.ProtocolEffect owner
            (SM.Completed peer initiator_nonce responder_nonce))
          events;
        eliminate
          exists (prefix middle suffix:C.history).
            events ==
              List.append prefix
                (G.ProtocolEffect owner
                  (SM.CiphertextAccepted recipient
                    (PlainMessage2
                      initiator_nonce responder_nonce peer)
                    accepted_ciphertext) ::
                 List.append middle
                   (G.ProtocolEffect owner
                     (SM.Completed
                       peer initiator_nonce responder_nonce) ::
                    suffix))
        returns
          exists
            (recipient':principal)
            (plaintext:plaintext)
            (ciphertext':ciphertext)
            (prefix' middle' suffix':C.history).
            events ==
              List.append prefix'
                (G.ProtocolEffect owner
                  (SM.CiphertextAccepted
                    recipient' plaintext ciphertext') ::
                 List.append middle'
                   (G.ProtocolEffect owner
                     (SM.Completed
                       peer initiator_nonce responder_nonce) ::
                    suffix')) /\
            decryption_authentication_result
              prefix' owner plaintext
        with _.
          (accepted_ciphertext_authenticates
             events prefix
             (List.append middle
               (G.ProtocolEffect owner
                 (SM.Completed
                   peer initiator_nonce responder_nonce) ::
                suffix))
             owner recipient
             (PlainMessage2
               initiator_nonce responder_nonce peer)
             accepted_ciphertext;
           introduce
             exists
               (recipient':principal)
               (plaintext:plaintext)
               (ciphertext':ciphertext)
               (prefix' middle' suffix':C.history).
               events ==
                 List.append prefix'
                   (G.ProtocolEffect owner
                     (SM.CiphertextAccepted
                       recipient' plaintext ciphertext') ::
                    List.append middle'
                      (G.ProtocolEffect owner
                        (SM.Completed
                          peer initiator_nonce responder_nonce) ::
                       suffix')) /\
               decryption_authentication_result
                 prefix' owner plaintext
           with
             recipient
             (PlainMessage2
               initiator_nonce responder_nonce peer)
             accepted_ciphertext prefix middle suffix
           and ())))
  and _.
    (eliminate
       exists
         (recipient:principal)
         (accepted_ciphertext:ciphertext).
         C.before
           (G.ProtocolEffect owner
             (SM.CiphertextAccepted recipient
               (PlainMessage3 responder_nonce)
               accepted_ciphertext))
           (G.ProtocolEffect owner
             (SM.Completed peer initiator_nonce responder_nonce))
           events
     returns
       exists
         (recipient':principal)
         (plaintext:plaintext)
         (ciphertext':ciphertext)
         (prefix middle suffix:C.history).
         events ==
           List.append prefix
             (G.ProtocolEffect owner
               (SM.CiphertextAccepted
                 recipient' plaintext ciphertext') ::
              List.append middle
                (G.ProtocolEffect owner
                  (SM.Completed
                    peer initiator_nonce responder_nonce) ::
                 suffix)) /\
         decryption_authentication_result prefix owner plaintext
     with _.
       (C.before_split
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted recipient
              (PlainMessage3 responder_nonce)
              accepted_ciphertext))
          (G.ProtocolEffect owner
            (SM.Completed peer initiator_nonce responder_nonce))
          events;
        eliminate
          exists (prefix middle suffix:C.history).
            events ==
              List.append prefix
                (G.ProtocolEffect owner
                  (SM.CiphertextAccepted recipient
                    (PlainMessage3 responder_nonce)
                    accepted_ciphertext) ::
                 List.append middle
                   (G.ProtocolEffect owner
                     (SM.Completed
                       peer initiator_nonce responder_nonce) ::
                    suffix))
        returns
          exists
            (recipient':principal)
            (plaintext:plaintext)
            (ciphertext':ciphertext)
            (prefix' middle' suffix':C.history).
            events ==
              List.append prefix'
                (G.ProtocolEffect owner
                  (SM.CiphertextAccepted
                    recipient' plaintext ciphertext') ::
                 List.append middle'
                   (G.ProtocolEffect owner
                     (SM.Completed
                       peer initiator_nonce responder_nonce) ::
                    suffix')) /\
            decryption_authentication_result
              prefix' owner plaintext
        with _.
          (accepted_ciphertext_authenticates
             events prefix
             (List.append middle
               (G.ProtocolEffect owner
                 (SM.Completed
                   peer initiator_nonce responder_nonce) ::
                suffix))
             owner recipient
             (PlainMessage3 responder_nonce)
             accepted_ciphertext;
           introduce
             exists
               (recipient':principal)
               (plaintext:plaintext)
               (ciphertext':ciphertext)
               (prefix' middle' suffix':C.history).
               events ==
                 List.append prefix'
                   (G.ProtocolEffect owner
                     (SM.CiphertextAccepted
                       recipient' plaintext ciphertext') ::
                    List.append middle'
                      (G.ProtocolEffect owner
                        (SM.Completed
                          peer initiator_nonce responder_nonce) ::
                       suffix')) /\
               decryption_authentication_result
                 prefix' owner plaintext
           with
             recipient
             (PlainMessage3 responder_nonce)
             accepted_ciphertext prefix middle suffix
           and ())))
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let all_completions_authenticate
  (events:C.history)
  : Lemma
      (requires
        C.completion_coherent events /\
        crypto_simulation events)
      (ensures completed_authentication events)
  =
  introduce forall
    (owner:E.endpoint_id)
    (peer:principal)
    (initiator_nonce responder_nonce:nonce).
    C.occurs
      (G.ProtocolEffect owner
        (SM.Completed peer initiator_nonce responder_nonce))
      events
    ==>
    exists
      (recipient:principal)
      (plaintext:plaintext)
      (ciphertext:ciphertext)
      (prefix middle suffix:C.history).
      events ==
        List.append prefix
          (G.ProtocolEffect owner
            (SM.CiphertextAccepted
              recipient plaintext ciphertext) ::
           List.append middle
             (G.ProtocolEffect owner
               (SM.Completed
                 peer initiator_nonce responder_nonce) ::
              suffix)) /\
      decryption_authentication_result prefix owner plaintext
  with begin
    introduce
      C.occurs
        (G.ProtocolEffect owner
          (SM.Completed peer initiator_nonce responder_nonce))
        events
      ==>
      exists
        (recipient:principal)
        (plaintext:plaintext)
        (ciphertext:ciphertext)
        (prefix middle suffix:C.history).
        events ==
          List.append prefix
            (G.ProtocolEffect owner
              (SM.CiphertextAccepted
                recipient plaintext ciphertext) ::
             List.append middle
               (G.ProtocolEffect owner
                 (SM.Completed
                   peer initiator_nonce responder_nonce) ::
                suffix)) /\
        decryption_authentication_result prefix owner plaintext
    with _.
      completion_authentication_one
        events owner peer initiator_nonce responder_nonce
  end

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
      (ensures completed_authentication state.G.history)
  =
  C.reachable_completion_coherent
    initiator responder transitions state;
  all_completions_authenticate state.G.history
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let nonce_knowledge_implies_compromise
  (trace:TB.trace)
  (nonce:BT.bytes)
  : Lemma
      (requires
        Inv.nonce_recorded trace nonce /\
        TI.trace_invariant #P.nsl_protocol_invariants trace /\
        AK.attacker_knows trace nonce)
      (ensures
        L.is_corrupt trace
          (D.role_label SM.initiator_endpoint) \/
        L.is_corrupt trace
          (D.role_label SM.responder_endpoint))
  =
  Inv.nonce_facts trace nonce;
  AK.attacker_only_knows_publishable_values
    #P.nsl_protocol_invariants trace nonce;
  L.flow_to_public_eq trace D.session_label;
  L.is_corrupt_join trace
    (D.role_label SM.initiator_endpoint)
    (D.role_label SM.responder_endpoint)

let history_nonce_secret
  (history:C.history)
  (nonce:BT.bytes)
  : Lemma
      (requires (
        let trace = M.dy_trace_of_history history in
        Inv.nonce_recorded trace nonce /\
        AK.attacker_knows trace nonce))
      (ensures (
        let trace = M.dy_trace_of_history history in
        L.is_corrupt trace
          (D.role_label SM.initiator_endpoint) \/
        L.is_corrupt trace
          (D.role_label SM.responder_endpoint)))
  =
  Inv.history_trace_invariant history;
  nonce_knowledge_implies_compromise
    (M.dy_trace_of_history history) nonce
#pop-options

let nonce_secrecy (events:C.history) : prop =
  forall (nonce:BT.bytes).
    Inv.nonce_recorded (M.dy_trace_of_history events) nonce /\
    AK.attacker_knows (M.dy_trace_of_history events) nonce
    ==>
    L.is_corrupt
      (M.dy_trace_of_history events)
      (D.role_label SM.initiator_endpoint) \/
    L.is_corrupt
      (M.dy_trace_of_history events)
      (D.role_label SM.responder_endpoint)

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let all_nonces_secret (events:C.history)
  : Lemma (ensures nonce_secrecy events)
  =
  introduce forall (nonce:BT.bytes).
    Inv.nonce_recorded (M.dy_trace_of_history events) nonce /\
    AK.attacker_knows (M.dy_trace_of_history events) nonce
    ==>
    L.is_corrupt
      (M.dy_trace_of_history events)
      (D.role_label SM.initiator_endpoint) \/
    L.is_corrupt
      (M.dy_trace_of_history events)
      (D.role_label SM.responder_endpoint)
  with begin
    introduce
      Inv.nonce_recorded
        (M.dy_trace_of_history events) nonce /\
      AK.attacker_knows
        (M.dy_trace_of_history events) nonce
      ==>
      L.is_corrupt
        (M.dy_trace_of_history events)
        (D.role_label SM.initiator_endpoint) \/
      L.is_corrupt
        (M.dy_trace_of_history events)
        (D.role_label SM.responder_endpoint)
    with _.
      history_nonce_secret events nonce
  end
#pop-options

let security_consequences (events:C.history) : prop =
  TI.trace_invariant
    #P.nsl_protocol_invariants
    (M.dy_trace_of_history events) /\
  completed_authentication events /\
  nonce_secrecy events

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
      (ensures security_consequences state.G.history)
  =
  Inv.history_trace_invariant state.G.history;
  reachable_completed_authentication
    initiator responder transitions state;
  all_nonces_secret state.G.history

(*** Non-vacuity: a complete honest run satisfies the simulation boundary ***)

let honest_ciphertext1
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (randomness:pke_randomness)
  : ciphertext
  =
  Crypto.encrypt responder randomness
    (PlainMessage1 initiator_nonce initiator)

let honest_ciphertext2
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (randomness:pke_randomness)
  : ciphertext
  =
  Crypto.encrypt initiator randomness
    (PlainMessage2 initiator_nonce responder_nonce responder)

let honest_ciphertext3
  (responder:principal)
  (responder_nonce:nonce)
  (randomness:pke_randomness)
  : ciphertext
  =
  Crypto.encrypt responder randomness
    (PlainMessage3 responder_nonce)

let honest_message1_acceptance_prefix
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (randomness:pke_randomness)
  : C.history
  =
  let plaintext = PlainMessage1 initiator_nonce initiator in
  let ciphertext =
    honest_ciphertext1 initiator responder initiator_nonce randomness
  in
  [
    G.Generated SM.initiator_endpoint (FreshNonce initiator_nonce);
    G.Generated SM.initiator_endpoint (FreshRandomness randomness);
    G.ProtocolEffect SM.initiator_endpoint
      (SM.CiphertextCreated
        initiator responder
        (SM.EndpointKey SM.responder_endpoint)
        plaintext randomness ciphertext);
    G.ObservedSend SM.initiator_endpoint 0 (Encrypted ciphertext);
    G.ObservedReceive SM.responder_endpoint 0 (Encrypted ciphertext);
  ]

let honest_message1_acceptance
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (message1_randomness:pke_randomness)
  : C.history
  =
  let ciphertext1 =
    honest_ciphertext1
      initiator responder initiator_nonce message1_randomness
  in
  [
    G.ProtocolEffect SM.responder_endpoint
      (SM.CiphertextAccepted responder
        (PlainMessage1 initiator_nonce initiator) ciphertext1);
  ]

let honest_between_message1_and_message2
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message2_randomness:pke_randomness)
  : C.history
  =
  let plaintext2 =
    PlainMessage2 initiator_nonce responder_nonce responder
  in
  let ciphertext2 =
    honest_ciphertext2
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  [
    G.Generated SM.responder_endpoint (FreshNonce responder_nonce);
    G.Generated SM.responder_endpoint (FreshRandomness message2_randomness);
    G.ProtocolEffect SM.responder_endpoint
      (SM.CiphertextCreated
        responder initiator
        (SM.EndpointKey SM.initiator_endpoint)
        plaintext2 message2_randomness ciphertext2);
    G.ObservedSend SM.responder_endpoint 1 (Encrypted ciphertext2);
    G.ObservedReceive SM.initiator_endpoint 1 (Encrypted ciphertext2);
  ]

let honest_message2_acceptance_prefix
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness:pke_randomness)
  : C.history
  =
  List.append
    (List.append
      (honest_message1_acceptance_prefix
        initiator responder initiator_nonce message1_randomness)
      (honest_message1_acceptance
        initiator responder initiator_nonce message1_randomness))
    (honest_between_message1_and_message2
      initiator responder
      initiator_nonce responder_nonce
      message2_randomness)

let honest_message2_acceptance
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message2_randomness:pke_randomness)
  : C.history
  =
  let ciphertext2 =
    honest_ciphertext2
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  [
    G.ProtocolEffect SM.initiator_endpoint
      (SM.CiphertextAccepted initiator
        (PlainMessage2 initiator_nonce responder_nonce responder)
        ciphertext2);
  ]

let honest_between_message2_and_message3
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message3_randomness:pke_randomness)
  : C.history
  =
  let plaintext3 = PlainMessage3 responder_nonce in
  let ciphertext3 =
    honest_ciphertext3 responder responder_nonce message3_randomness
  in
  [
    G.Generated SM.initiator_endpoint
      (FreshRandomness message3_randomness);
    G.ProtocolEffect SM.initiator_endpoint
      (SM.CiphertextCreated
        initiator responder
        (SM.EndpointKey SM.responder_endpoint)
        plaintext3 message3_randomness ciphertext3);
    G.ObservedSend SM.initiator_endpoint 2 (Encrypted ciphertext3);
    G.ProtocolEffect SM.initiator_endpoint
      (SM.Completed responder initiator_nonce responder_nonce);
    G.ObservedReceive SM.responder_endpoint 2 (Encrypted ciphertext3);
  ]

let honest_message3_acceptance_prefix
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : C.history
  =
  List.append
    (List.append
      (honest_message2_acceptance_prefix
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness message2_randomness)
      (honest_message2_acceptance
        initiator responder
        initiator_nonce responder_nonce message2_randomness))
    (honest_between_message2_and_message3
      initiator responder
      initiator_nonce responder_nonce
      message3_randomness)

let honest_message3_acceptance
  (responder:principal)
  (responder_nonce:nonce)
  (message3_randomness:pke_randomness)
  : C.history
  =
  let ciphertext3 =
    honest_ciphertext3 responder responder_nonce message3_randomness
  in
  [
    G.ProtocolEffect SM.responder_endpoint
      (SM.CiphertextAccepted responder
        (PlainMessage3 responder_nonce) ciphertext3);
  ]

let honest_after_message3_acceptance
  (initiator:principal)
  (initiator_nonce responder_nonce:nonce)
  : C.history
  =
  [
    G.ProtocolEffect SM.responder_endpoint
      (SM.Completed initiator initiator_nonce responder_nonce);
  ]

let honest_full_run_history
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : C.history
  =
  List.append
    (List.append
      (honest_message3_acceptance_prefix
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness message2_randomness message3_randomness)
      (honest_message3_acceptance
        responder responder_nonce message3_randomness))
    (honest_after_message3_acceptance
      initiator initiator_nonce responder_nonce)

let honest_symbolic_plaintext1 (initiator:principal) : M.symbolic_plaintext =
  M.SymbolicPlaintext1
    (D.protocol_nonce_term 4)
    (D.principal_term initiator)

let honest_symbolic_ciphertext1 (initiator:principal) : BT.bytes =
  D.ciphertext_term
    (D.role_public_key SM.responder_endpoint)
    (D.encryption_nonce_term 6)
    (M.flatten_plaintext (honest_symbolic_plaintext1 initiator))

let honest_symbolic_plaintext2 (responder:principal) : M.symbolic_plaintext =
  M.SymbolicPlaintext2
    (D.protocol_nonce_term 4)
    (D.protocol_nonce_term 12)
    (D.principal_term responder)

let honest_symbolic_ciphertext2 (responder:principal) : BT.bytes =
  D.ciphertext_term
    (D.role_public_key SM.initiator_endpoint)
    (D.encryption_nonce_term 14)
    (M.flatten_plaintext (honest_symbolic_plaintext2 responder))

let honest_symbolic_plaintext3 : M.symbolic_plaintext =
  M.SymbolicPlaintext3 (D.protocol_nonce_term 12)

let honest_symbolic_ciphertext3 : BT.bytes =
  D.ciphertext_term
    (D.role_public_key SM.responder_endpoint)
    (D.encryption_nonce_term 20)
    (M.flatten_plaintext honest_symbolic_plaintext3)

let genuine_decryption_simulated
  (state:M.model)
  (owner:E.endpoint_id)
  (concrete_plaintext:plaintext)
  : prop
  =
  (owner == SM.initiator_endpoint \/
   owner == SM.responder_endpoint) /\
  exists
    (symbolic_plaintext:M.symbolic_plaintext)
    (symbolic_ciphertext encryption_nonce:BT.bytes).
    acceptance_view
      state owner concrete_plaintext
      symbolic_plaintext symbolic_ciphertext /\
    symbolic_ciphertext ==
      D.ciphertext_term
        (D.role_public_key owner)
        encryption_nonce
        (M.flatten_plaintext symbolic_plaintext) /\
    B.bytes_invariant #P.nsl_crypto_invariants
      state.M.dy_trace symbolic_ciphertext

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let genuine_decryption_is_simulated
  (state:M.model)
  (owner:E.endpoint_id)
  (concrete_plaintext:plaintext)
  : Lemma
      (requires
        genuine_decryption_simulated
          state owner concrete_plaintext)
      (ensures
        decryption_simulated state owner concrete_plaintext)
  =
  eliminate
    exists
      (symbolic_plaintext:M.symbolic_plaintext)
      (symbolic_ciphertext encryption_nonce:BT.bytes).
      acceptance_view
        state owner concrete_plaintext
        symbolic_plaintext symbolic_ciphertext /\
      symbolic_ciphertext ==
        D.ciphertext_term
          (D.role_public_key owner)
          encryption_nonce
          (M.flatten_plaintext symbolic_plaintext) /\
      B.bytes_invariant #P.nsl_crypto_invariants
        state.M.dy_trace symbolic_ciphertext
  returns decryption_simulated state owner concrete_plaintext
  with _.
    introduce
      exists
        (symbolic_plaintext':M.symbolic_plaintext)
        (symbolic_ciphertext':BT.bytes).
        acceptance_view
          state owner concrete_plaintext
          symbolic_plaintext' symbolic_ciphertext' /\
        (L.is_corrupt state.M.dy_trace (D.role_label owner) \/
         exists (encryption_nonce':BT.bytes).
           symbolic_ciphertext' ==
             D.ciphertext_term
               (D.role_public_key owner)
               encryption_nonce'
               (M.flatten_plaintext symbolic_plaintext') /\
           B.bytes_invariant #P.nsl_crypto_invariants
             state.M.dy_trace symbolic_ciphertext')
    with symbolic_plaintext symbolic_ciphertext and (
      introduce
        exists (encryption_nonce':BT.bytes).
          symbolic_ciphertext ==
            D.ciphertext_term
              (D.role_public_key owner)
              encryption_nonce'
              (M.flatten_plaintext symbolic_plaintext) /\
          B.bytes_invariant #P.nsl_crypto_invariants
            state.M.dy_trace symbolic_ciphertext
      with encryption_nonce and ())
#pop-options

let singleton_acceptance_is_simulated
  (state:M.model)
  (owner:E.endpoint_id)
  (recipient:principal)
  (plaintext:plaintext)
  (ciphertext:ciphertext)
  : Lemma
      (requires decryption_simulated state owner plaintext)
      (ensures
        crypto_simulation_from state [
          G.ProtocolEffect owner
            (SM.CiphertextAccepted recipient plaintext ciphertext)
        ])
  =
  ()

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10 --split_queries always"
let honest_message1_acceptance_genuine
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (randomness:pke_randomness)
  : Lemma
      (ensures
        genuine_decryption_simulated
          (M.interpret_history
            (honest_message1_acceptance_prefix
              initiator responder initiator_nonce randomness))
          SM.responder_endpoint
          (PlainMessage1 initiator_nonce initiator))
  =
  Inv.history_model_invariant
    (honest_message1_acceptance_prefix
      initiator responder initiator_nonce randomness);
  normalize_term_spec M.interpret_history;
  assert (
    acceptance_view
      (M.interpret_history
        (honest_message1_acceptance_prefix
          initiator responder initiator_nonce randomness))
      SM.responder_endpoint
      (PlainMessage1 initiator_nonce initiator)
      (honest_symbolic_plaintext1 initiator)
      (honest_symbolic_ciphertext1 initiator))
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  assert (
    B.bytes_invariant #P.nsl_crypto_invariants
      (M.dy_trace_of_history
        (honest_message1_acceptance_prefix
          initiator responder initiator_nonce randomness))
      (honest_symbolic_ciphertext1 initiator));
  introduce
    exists
      (symbolic_plaintext:M.symbolic_plaintext)
      (symbolic_ciphertext encryption_nonce:BT.bytes).
      acceptance_view
        (M.interpret_history
          (honest_message1_acceptance_prefix
            initiator responder initiator_nonce randomness))
        SM.responder_endpoint
        (PlainMessage1 initiator_nonce initiator)
        symbolic_plaintext symbolic_ciphertext /\
      symbolic_ciphertext ==
        D.ciphertext_term
          (D.role_public_key SM.responder_endpoint)
          encryption_nonce
          (M.flatten_plaintext symbolic_plaintext) /\
      B.bytes_invariant #P.nsl_crypto_invariants
        (M.dy_trace_of_history
          (honest_message1_acceptance_prefix
            initiator responder initiator_nonce randomness))
        symbolic_ciphertext
  with
    (honest_symbolic_plaintext1 initiator)
    (honest_symbolic_ciphertext1 initiator)
    (D.encryption_nonce_term 6)
  and ()

let honest_message2_acceptance_genuine
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness:pke_randomness)
  : Lemma
      (ensures
        genuine_decryption_simulated
          (M.interpret_history
            (honest_message2_acceptance_prefix
              initiator responder
              initiator_nonce responder_nonce
              message1_randomness message2_randomness))
          SM.initiator_endpoint
          (PlainMessage2 initiator_nonce responder_nonce responder))
  =
  Inv.history_model_invariant
    (honest_message2_acceptance_prefix
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness);
  normalize_term_spec M.interpret_history;
  assert (
    acceptance_view
      (M.interpret_history
        (honest_message2_acceptance_prefix
          initiator responder
          initiator_nonce responder_nonce
          message1_randomness message2_randomness))
      SM.initiator_endpoint
      (PlainMessage2 initiator_nonce responder_nonce responder)
      (honest_symbolic_plaintext2 responder)
      (honest_symbolic_ciphertext2 responder))
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  assert (
    B.bytes_invariant #P.nsl_crypto_invariants
      (M.dy_trace_of_history
        (honest_message2_acceptance_prefix
          initiator responder
          initiator_nonce responder_nonce
          message1_randomness message2_randomness))
      (honest_symbolic_ciphertext2 responder));
  introduce
    exists
      (symbolic_plaintext:M.symbolic_plaintext)
      (symbolic_ciphertext encryption_nonce:BT.bytes).
      acceptance_view
        (M.interpret_history
          (honest_message2_acceptance_prefix
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness message2_randomness))
        SM.initiator_endpoint
        (PlainMessage2 initiator_nonce responder_nonce responder)
        symbolic_plaintext symbolic_ciphertext /\
      symbolic_ciphertext ==
        D.ciphertext_term
          (D.role_public_key SM.initiator_endpoint)
          encryption_nonce
          (M.flatten_plaintext symbolic_plaintext) /\
      B.bytes_invariant #P.nsl_crypto_invariants
        (M.dy_trace_of_history
          (honest_message2_acceptance_prefix
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness message2_randomness))
        symbolic_ciphertext
  with
    (honest_symbolic_plaintext2 responder)
    (honest_symbolic_ciphertext2 responder)
    (D.encryption_nonce_term 14)
  and ()

let honest_message3_acceptance_genuine
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Lemma
      (ensures
        genuine_decryption_simulated
          (M.interpret_history
            (honest_message3_acceptance_prefix
              initiator responder
              initiator_nonce responder_nonce
              message1_randomness
              message2_randomness message3_randomness))
          SM.responder_endpoint
          (PlainMessage3 responder_nonce))
  =
  Inv.history_model_invariant
    (honest_message3_acceptance_prefix
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness message3_randomness);
  normalize_term_spec M.interpret_history;
  assert (
    acceptance_view
      (M.interpret_history
        (honest_message3_acceptance_prefix
          initiator responder
          initiator_nonce responder_nonce
          message1_randomness message2_randomness message3_randomness))
      SM.responder_endpoint
      (PlainMessage3 responder_nonce)
      honest_symbolic_plaintext3
      honest_symbolic_ciphertext3)
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  assert (
    B.bytes_invariant #P.nsl_crypto_invariants
      (M.dy_trace_of_history
        (honest_message3_acceptance_prefix
          initiator responder
          initiator_nonce responder_nonce
          message1_randomness message2_randomness message3_randomness))
      honest_symbolic_ciphertext3);
  introduce
    exists
      (symbolic_plaintext:M.symbolic_plaintext)
      (symbolic_ciphertext encryption_nonce:BT.bytes).
      acceptance_view
        (M.interpret_history
          (honest_message3_acceptance_prefix
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness message2_randomness message3_randomness))
        SM.responder_endpoint
        (PlainMessage3 responder_nonce)
        symbolic_plaintext symbolic_ciphertext /\
      symbolic_ciphertext ==
        D.ciphertext_term
          (D.role_public_key SM.responder_endpoint)
          encryption_nonce
          (M.flatten_plaintext symbolic_plaintext) /\
      B.bytes_invariant #P.nsl_crypto_invariants
        (M.dy_trace_of_history
          (honest_message3_acceptance_prefix
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness message2_randomness message3_randomness))
        symbolic_ciphertext
  with
    honest_symbolic_plaintext3
    honest_symbolic_ciphertext3
    (D.encryption_nonce_term 20)
  and ()
#pop-options

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10 --split_queries always"
let honest_full_run_simulated
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Lemma
      (ensures (
        let history =
          honest_full_run_history
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness
            message2_randomness message3_randomness
        in
        crypto_simulation history /\
        genuine_decryption_simulated
          (M.interpret_history
            (honest_message1_acceptance_prefix
              initiator responder
              initiator_nonce message1_randomness))
          SM.responder_endpoint
          (PlainMessage1 initiator_nonce initiator) /\
        genuine_decryption_simulated
          (M.interpret_history
            (honest_message2_acceptance_prefix
              initiator responder
              initiator_nonce responder_nonce
              message1_randomness message2_randomness))
          SM.initiator_endpoint
          (PlainMessage2 initiator_nonce responder_nonce responder) /\
        genuine_decryption_simulated
          (M.interpret_history
            (honest_message3_acceptance_prefix
              initiator responder
              initiator_nonce responder_nonce
              message1_randomness
              message2_randomness message3_randomness))
          SM.responder_endpoint
          (PlainMessage3 responder_nonce)))
  =
  honest_message1_acceptance_genuine
    initiator responder initiator_nonce message1_randomness;
  honest_message2_acceptance_genuine
    initiator responder
    initiator_nonce responder_nonce
    message1_randomness message2_randomness;
  honest_message3_acceptance_genuine
    initiator responder
    initiator_nonce responder_nonce
    message1_randomness message2_randomness message3_randomness;
  genuine_decryption_is_simulated
    (M.interpret_history
      (honest_message1_acceptance_prefix
        initiator responder initiator_nonce message1_randomness))
    SM.responder_endpoint
    (PlainMessage1 initiator_nonce initiator);
  genuine_decryption_is_simulated
    (M.interpret_history
      (honest_message2_acceptance_prefix
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness message2_randomness))
    SM.initiator_endpoint
    (PlainMessage2 initiator_nonce responder_nonce responder);
  genuine_decryption_is_simulated
    (M.interpret_history
      (honest_message3_acceptance_prefix
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness
        message2_randomness message3_randomness))
    SM.responder_endpoint
    (PlainMessage3 responder_nonce);
  let prefix1 =
    honest_message1_acceptance_prefix
      initiator responder initiator_nonce message1_randomness
  in
  let acceptance1 =
    honest_message1_acceptance
      initiator responder initiator_nonce message1_randomness
  in
  let between12 =
    honest_between_message1_and_message2
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  let accepted1 = List.append prefix1 acceptance1 in
  let prefix2 = List.append accepted1 between12 in
  let acceptance2 =
    honest_message2_acceptance
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  let between23 =
    honest_between_message2_and_message3
      initiator responder
      initiator_nonce responder_nonce message3_randomness
  in
  let accepted2 = List.append prefix2 acceptance2 in
  let prefix3 = List.append accepted2 between23 in
  let acceptance3 =
    honest_message3_acceptance
      responder responder_nonce message3_randomness
  in
  let after3 =
    honest_after_message3_acceptance
      initiator initiator_nonce responder_nonce
  in
  assert (acceptance_free prefix1)
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  acceptance_free_is_simulated M.initial_model prefix1;
  singleton_acceptance_is_simulated
    (M.interpret_history prefix1)
    SM.responder_endpoint responder
    (PlainMessage1 initiator_nonce initiator)
    (honest_ciphertext1
      initiator responder initiator_nonce message1_randomness);
  crypto_simulation_from_append
    M.initial_model prefix1 acceptance1;
  assert (acceptance_free between12)
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  acceptance_free_is_simulated
    (M.interpret_history accepted1) between12;
  crypto_simulation_from_append
    M.initial_model accepted1 between12;
  singleton_acceptance_is_simulated
    (M.interpret_history prefix2)
    SM.initiator_endpoint initiator
    (PlainMessage2 initiator_nonce responder_nonce responder)
    (honest_ciphertext2
      initiator responder
      initiator_nonce responder_nonce message2_randomness);
  crypto_simulation_from_append
    M.initial_model prefix2 acceptance2;
  assert (acceptance_free between23)
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  acceptance_free_is_simulated
    (M.interpret_history accepted2) between23;
  crypto_simulation_from_append
    M.initial_model accepted2 between23;
  singleton_acceptance_is_simulated
    (M.interpret_history prefix3)
    SM.responder_endpoint responder
    (PlainMessage3 responder_nonce)
    (honest_ciphertext3
      responder responder_nonce message3_randomness);
  crypto_simulation_from_append
    M.initial_model prefix3 acceptance3;
  assert (acceptance_free after3)
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  acceptance_free_is_simulated
    (M.interpret_history (List.append prefix3 acceptance3))
    after3;
  crypto_simulation_from_append
    M.initial_model
    (List.append prefix3 acceptance3)
    after3
#pop-options

let honest_rule1
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (randomness:pke_randomness)
  : SM.rule
  =
  let plaintext = PlainMessage1 initiator_nonce initiator in
  let ciphertext =
    honest_ciphertext1 initiator responder initiator_nonce randomness
  in
  {
    E.rule_payload =
      SM.InitiatorStarts initiator_nonce randomness ciphertext;
    E.rule_story = [
      E.StoryFresh (FreshNonce initiator_nonce);
      E.StoryFresh (FreshRandomness randomness);
      E.StorySemantic (
        SM.CiphertextCreated
          initiator responder
          (SM.EndpointKey SM.responder_endpoint)
          plaintext randomness ciphertext);
      E.StorySend (Encrypted ciphertext);
    ];
  }

let honest_rule2
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness:pke_randomness)
  : SM.rule
  =
  let ciphertext1 =
    honest_ciphertext1
      initiator responder initiator_nonce message1_randomness
  in
  let plaintext2 =
    PlainMessage2 initiator_nonce responder_nonce responder
  in
  let ciphertext2 =
    honest_ciphertext2
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  {
    E.rule_payload =
      SM.ResponderReplies
        responder initiator
        (SM.EndpointKey SM.initiator_endpoint)
        initiator_nonce responder_nonce
        ciphertext1 message2_randomness ciphertext2;
    E.rule_story = [
      E.StorySemantic (
        SM.CiphertextAccepted responder
          (PlainMessage1 initiator_nonce initiator) ciphertext1);
      E.StoryFresh (FreshNonce responder_nonce);
      E.StoryFresh (FreshRandomness message2_randomness);
      E.StorySemantic (
        SM.CiphertextCreated
          responder initiator
          (SM.EndpointKey SM.initiator_endpoint)
          plaintext2 message2_randomness ciphertext2);
      E.StorySend (Encrypted ciphertext2);
    ];
  }

let honest_rule3
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message2_randomness message3_randomness:pke_randomness)
  : SM.rule
  =
  let ciphertext2 =
    honest_ciphertext2
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  let plaintext3 = PlainMessage3 responder_nonce in
  let ciphertext3 =
    honest_ciphertext3 responder responder_nonce message3_randomness
  in
  {
    E.rule_payload =
      SM.InitiatorFinishes
        initiator responder initiator_nonce responder_nonce
        ciphertext2 message3_randomness ciphertext3;
    E.rule_story = [
      E.StorySemantic (
        SM.CiphertextAccepted initiator
          (PlainMessage2 initiator_nonce responder_nonce responder)
          ciphertext2);
      E.StoryFresh (FreshRandomness message3_randomness);
      E.StorySemantic (
        SM.CiphertextCreated
          initiator responder
          (SM.EndpointKey SM.responder_endpoint)
          plaintext3 message3_randomness ciphertext3);
      E.StorySend (Encrypted ciphertext3);
      E.StorySemantic (
        SM.Completed responder initiator_nonce responder_nonce);
    ];
  }

let honest_rule4
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message3_randomness:pke_randomness)
  : SM.rule
  =
  let ciphertext3 =
    honest_ciphertext3 responder responder_nonce message3_randomness
  in
  {
    E.rule_payload =
      SM.ResponderFinishes
        responder initiator initiator_nonce responder_nonce ciphertext3;
    E.rule_story = [
      E.StorySemantic (
        SM.CiphertextAccepted responder
          (PlainMessage3 responder_nonce) ciphertext3);
      E.StorySemantic (
        SM.Completed initiator initiator_nonce responder_nonce);
    ];
  }

let honest_output1
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (randomness:pke_randomness)
  : SM.output
  =
  {
    BaseSM.so_wire_outputs = [
      Encrypted (
        honest_ciphertext1
          initiator responder initiator_nonce randomness)
    ];
    BaseSM.so_local_outputs = [];
  }

let honest_output2
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (randomness:pke_randomness)
  : SM.output
  =
  {
    BaseSM.so_wire_outputs = [
      Encrypted (
        honest_ciphertext2
          initiator responder
          initiator_nonce responder_nonce randomness)
    ];
    BaseSM.so_local_outputs = [];
  }

let honest_output3
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (randomness:pke_randomness)
  : SM.output
  =
  {
    BaseSM.so_wire_outputs = [
      Encrypted (
        honest_ciphertext3 responder responder_nonce randomness)
    ];
    BaseSM.so_local_outputs = [
      SessionEstablished responder initiator_nonce responder_nonce
    ];
  }

let honest_output4
  (initiator:principal)
  (initiator_nonce responder_nonce:nonce)
  : SM.output
  =
  {
    BaseSM.so_wire_outputs = [];
    BaseSM.so_local_outputs = [
      SessionEstablished initiator initiator_nonce responder_nonce
    ];
  }

let honest_successor
  (state:Protocol.protocol_state)
  (who:E.endpoint_id)
  (trigger:E.trigger message local_event)
  (witness:SM.rule)
  (next_endpoint:endpoint_state)
  (output:SM.output)
  : Protocol.protocol_state
  =
  G.endpoint_successor
    state who next_endpoint
    (G.append_honest
      state.G.network who output.BaseSM.so_wire_outputs)
    (List.append state.G.generated
      (E.story_fresh_values witness.E.rule_story))
    (List.append state.G.history
      (G.endpoint_effects
        who trigger witness.E.rule_story
        (List.length state.G.network)))

let honest_state1
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (message1_randomness:pke_randomness)
  : Protocol.protocol_state
  =
  honest_successor
    (Protocol.initial initiator responder)
    SM.initiator_endpoint
    (E.TriggerLocal Start)
    (honest_rule1
      initiator responder initiator_nonce message1_randomness)
    {
      (initiator_initial initiator responder) with
        phase = InitiatorWaiting;
        initiator_nonce = Some initiator_nonce;
    }
    (honest_output1
      initiator responder initiator_nonce message1_randomness)

let honest_state2
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness:pke_randomness)
  : Protocol.protocol_state
  =
  let ciphertext1 =
    honest_ciphertext1
      initiator responder initiator_nonce message1_randomness
  in
  honest_successor
    (honest_state1
      initiator responder initiator_nonce message1_randomness)
    SM.responder_endpoint
    (E.TriggerReceive 0 (Encrypted ciphertext1))
    (honest_rule2
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness)
    {
      (responder_initial responder) with
        phase = ResponderWaiting;
        peer = Some initiator;
        initiator_nonce = Some initiator_nonce;
        responder_nonce = Some responder_nonce;
    }
    (honest_output2
      initiator responder
      initiator_nonce responder_nonce message2_randomness)

let honest_state3
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Protocol.protocol_state
  =
  let ciphertext2 =
    honest_ciphertext2
      initiator responder
      initiator_nonce responder_nonce message2_randomness
  in
  honest_successor
    (honest_state2
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness)
    SM.initiator_endpoint
    (E.TriggerReceive 1 (Encrypted ciphertext2))
    (honest_rule3
      initiator responder
      initiator_nonce responder_nonce
      message2_randomness message3_randomness)
    {
      (initiator_initial initiator responder) with
        phase = InitiatorComplete;
        initiator_nonce = Some initiator_nonce;
        responder_nonce = Some responder_nonce;
    }
    (honest_output3
      initiator responder
      initiator_nonce responder_nonce message3_randomness)

let honest_state4
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Protocol.protocol_state
  =
  let ciphertext3 =
    honest_ciphertext3 responder responder_nonce message3_randomness
  in
  honest_successor
    (honest_state3
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness message3_randomness)
    SM.responder_endpoint
    (E.TriggerReceive 2 (Encrypted ciphertext3))
    (honest_rule4
      initiator responder
      initiator_nonce responder_nonce message3_randomness)
    {
      (responder_initial responder) with
        phase = ResponderComplete;
        peer = Some initiator;
        initiator_nonce = Some initiator_nonce;
        responder_nonce = Some responder_nonce;
    }
    (honest_output4 initiator initiator_nonce responder_nonce)

let honest_transition1
  (initiator responder:principal)
  (initiator_nonce:nonce)
  (message1_randomness:pke_randomness)
  : Protocol.protocol_transition
  =
  {
    G.transition_action = G.Run SM.initiator_endpoint Start;
    G.transition_rule =
      G.EndpointRule (
        honest_rule1
          initiator responder initiator_nonce message1_randomness);
    G.transition_next =
      honest_state1
        initiator responder initiator_nonce message1_randomness;
    G.transition_output =
      honest_output1
        initiator responder initiator_nonce message1_randomness;
  }

let honest_transition2
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness:pke_randomness)
  : Protocol.protocol_transition
  =
  {
    G.transition_action = G.Deliver 0 SM.responder_endpoint;
    G.transition_rule =
      G.EndpointRule (
        honest_rule2
          initiator responder
          initiator_nonce responder_nonce
          message1_randomness message2_randomness);
    G.transition_next =
      honest_state2
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness message2_randomness;
    G.transition_output =
      honest_output2
        initiator responder
        initiator_nonce responder_nonce message2_randomness;
  }

let honest_transition3
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Protocol.protocol_transition
  =
  {
    G.transition_action = G.Deliver 1 SM.initiator_endpoint;
    G.transition_rule =
      G.EndpointRule (
        honest_rule3
          initiator responder
          initiator_nonce responder_nonce
          message2_randomness message3_randomness);
    G.transition_next =
      honest_state3
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness message2_randomness message3_randomness;
    G.transition_output =
      honest_output3
        initiator responder
        initiator_nonce responder_nonce message3_randomness;
  }

let honest_transition4
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Protocol.protocol_transition
  =
  {
    G.transition_action = G.Deliver 2 SM.responder_endpoint;
    G.transition_rule =
      G.EndpointRule (
        honest_rule4
          initiator responder
          initiator_nonce responder_nonce message3_randomness);
    G.transition_next =
      honest_state4
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness message2_randomness message3_randomness;
    G.transition_output =
      honest_output4 initiator initiator_nonce responder_nonce;
  }

let honest_transitions
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : list Protocol.protocol_transition
  =
  [
    honest_transition1
      initiator responder initiator_nonce message1_randomness;
    honest_transition2
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness;
    honest_transition3
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness message3_randomness;
    honest_transition4
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness message2_randomness message3_randomness;
  ]

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10 --split_queries always"
let honest_full_run_reachable
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Lemma
      (requires
        initiator_nonce =!= responder_nonce /\
        message1_randomness =!= message2_randomness /\
        message1_randomness =!= message3_randomness /\
        message2_randomness =!= message3_randomness)
      (ensures (
        let transitions =
          honest_transitions
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness
            message2_randomness message3_randomness
        in
        let final_state =
          honest_state4
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness
            message2_randomness message3_randomness
        in
        Protocol.trace_reaches
          initiator responder
          (Protocol.initial initiator responder)
          transitions final_state /\
        final_state.G.history ==
          honest_full_run_history
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness
            message2_randomness message3_randomness))
  =
  Crypto.lemma_decrypt_encrypt responder message1_randomness
    (PlainMessage1 initiator_nonce initiator);
  Crypto.lemma_decrypt_encrypt initiator message2_randomness
    (PlainMessage2 initiator_nonce responder_nonce responder);
  Crypto.lemma_decrypt_encrypt responder message3_randomness
    (PlainMessage3 responder_nonce);
  normalize_term_spec SM.step_rule;
  assert (
    Protocol.trace_reaches
      initiator responder
      (Protocol.initial initiator responder)
      (honest_transitions
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness
        message2_randomness message3_randomness)
      (honest_state4
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness
        message2_randomness message3_randomness));
  assert (
    (honest_state4
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness
      message2_randomness message3_randomness).G.history ==
    honest_full_run_history
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness
      message2_randomness message3_randomness)
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ())
#pop-options

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10 --split_queries always"
let honest_full_run_secure
  (initiator responder:principal)
  (initiator_nonce responder_nonce:nonce)
  (message1_randomness message2_randomness message3_randomness:pke_randomness)
  : Lemma
      (requires
        initiator_nonce =!= responder_nonce /\
        message1_randomness =!= message2_randomness /\
        message1_randomness =!= message3_randomness /\
        message2_randomness =!= message3_randomness)
      (ensures (
        let final_state =
          honest_state4
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness
            message2_randomness message3_randomness
        in
        final_state.G.history ==
          honest_full_run_history
            initiator responder
            initiator_nonce responder_nonce
            message1_randomness
            message2_randomness message3_randomness /\
        C.occurs
          (G.ProtocolEffect SM.initiator_endpoint
            (SM.Completed
              responder initiator_nonce responder_nonce))
          final_state.G.history /\
        C.occurs
          (G.ProtocolEffect SM.responder_endpoint
            (SM.Completed
              initiator initiator_nonce responder_nonce))
          final_state.G.history /\
        crypto_simulation final_state.G.history /\
        security_consequences final_state.G.history))
  =
  honest_full_run_reachable
    initiator responder
    initiator_nonce responder_nonce
    message1_randomness message2_randomness message3_randomness;
  honest_full_run_simulated
    initiator responder
    initiator_nonce responder_nonce
    message1_randomness message2_randomness message3_randomness;
  let final_state =
    honest_state4
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness
      message2_randomness message3_randomness
  in
  assert (
    crypto_simulation final_state.G.history);
  reachable_security
    initiator responder
    (honest_transitions
      initiator responder
      initiator_nonce responder_nonce
      message1_randomness
      message2_randomness message3_randomness)
    final_state;
  assert (
    C.occurs
      (G.ProtocolEffect SM.initiator_endpoint
        (SM.Completed responder initiator_nonce responder_nonce))
      (honest_full_run_history
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness
        message2_randomness message3_randomness))
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  assert (
    C.occurs
      (G.ProtocolEffect SM.responder_endpoint
        (SM.Completed initiator initiator_nonce responder_nonce))
      (honest_full_run_history
        initiator responder
        initiator_nonce responder_nonce
        message1_randomness
        message2_randomness message3_randomness))
    by (
      FStar.Tactics.norm [delta; iota; zeta; primops];
      FStar.Tactics.smt ());
  assert (
    C.occurs
      (G.ProtocolEffect SM.initiator_endpoint
        (SM.Completed responder initiator_nonce responder_nonce))
      final_state.G.history /\
    C.occurs
      (G.ProtocolEffect SM.responder_endpoint
        (SM.Completed initiator initiator_nonce responder_nonce))
      final_state.G.history)
#pop-options
