module TLS13.Symbolic.Invariant

module DY = DY.Core
module Events = TLS13.Symbolic.Events
module Product = TLS13.Symbolic.Product
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

let signature_origin_content
  (context:Terms.session_context)
  (verification_key message:DY.bytes)
  : DY.bytes =
  Events.handshake_event_content
    context
    (DY.Concat verification_key message)

let finished_origin_content
  (context:Terms.session_context)
  (key message:DY.bytes)
  : DY.bytes =
  Events.handshake_event_content context (DY.Concat key message)

let record_origin_content
  (context:Terms.session_context)
  (direction:Events.record_direction)
  (epoch:Events.record_epoch)
  (nonce plaintext additional_data key:DY.bytes)
  : DY.bytes =
  Events.record_event_content
    context direction epoch nonce plaintext
    (Terms.protected_record key nonce plaintext additional_data)

let signature_predicate
  (tr:DY.trace)
  (key_usage:DY.usage{DY.SigKey? key_usage})
  (verification_key message:DY.bytes)
  : prop =
  exists context.
    Terms.session_context_in_profile context /\
    key_usage ==
      Usages.signing_key_usage
        context.Terms.context_server.Terms.session_principal
        verification_key /\
    message ==
      Terms.certificate_verify_input context.Terms.context_transcript /\
    DY.event_triggered
      tr
      context.Terms.context_server.Terms.session_principal
      (Events.event_tag Events.ServerCertificateVerifySigned)
      (signature_origin_content context verification_key message)

let finished_predicate
  (tr:DY.trace)
  (key_usage:DY.usage{DY.MacKey? key_usage})
  (key message:DY.bytes)
  : prop =
  exists context.
    Terms.session_context_in_profile context /\
    message == Terms.transcript_hash context.Terms.context_transcript /\
    ((key_usage ==
        DY.MacKey
          "TLS13.ServerFinishedKey"
          (Terms.transcript_hash context.Terms.context_transcript) /\
      DY.event_triggered
        tr
        context.Terms.context_server.Terms.session_principal
        (Events.event_tag Events.ServerFinishedSent)
        (finished_origin_content context key message)) \/
     (key_usage ==
        DY.MacKey
          "TLS13.ClientFinishedKey"
          (Terms.transcript_hash context.Terms.context_transcript) /\
      DY.event_triggered
        tr
        context.Terms.context_client.Terms.session_principal
        (Events.event_tag Events.ClientFinishedSent)
        (finished_origin_content context key message)))

let aead_usage_matches
  (key_usage:DY.usage{DY.AeadKey? key_usage})
  (direction:Events.record_direction)
  (epoch:Events.record_epoch)
  : prop =
  match direction, epoch with
  | Events.ClientToServer, Events.HandshakeEpoch ->
    exists data.
      key_usage == DY.AeadKey "TLS13.ClientHandshakeRecordKey" data
  | Events.ServerToClient, Events.HandshakeEpoch ->
    exists data.
      key_usage == DY.AeadKey "TLS13.ServerHandshakeRecordKey" data
  | Events.ClientToServer, Events.ApplicationEpoch ->
    exists data.
      key_usage == DY.AeadKey "TLS13.ClientApplicationRecordKey" data
  | Events.ServerToClient, Events.ApplicationEpoch ->
    exists data.
      key_usage == DY.AeadKey "TLS13.ServerApplicationRecordKey" data

let sender_for_direction
  (context:Terms.session_context)
  (direction:Events.record_direction)
  : Terms.endpoint_session =
  match direction with
  | Events.ClientToServer -> context.Terms.context_client
  | Events.ServerToClient -> context.Terms.context_server

let aead_predicate
  (tr:DY.trace)
  (key_usage:DY.usage{DY.AeadKey? key_usage})
  (key nonce plaintext additional_data:DY.bytes)
  : prop =
  exists context direction epoch.
    Terms.session_context_in_profile context /\
    aead_usage_matches key_usage direction epoch /\
    DY.event_triggered
      tr
      (sender_for_direction context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (record_origin_content
        context direction epoch nonce plaintext additional_data key)

val signature_predicate_later:
  tr1:DY.trace ->
  tr2:DY.trace ->
  key_usage:DY.usage{DY.SigKey? key_usage} ->
  verification_key:DY.bytes ->
  message:DY.bytes ->
  Lemma
    (requires
      signature_predicate tr1 key_usage verification_key message /\
      DY.bytes_well_formed tr1 verification_key /\
      DY.bytes_well_formed tr1 message /\
      DY.grows tr1 tr2)
    (ensures signature_predicate tr2 key_usage verification_key message)
let signature_predicate_later
  tr1 tr2 key_usage verification_key message =
  eliminate exists context.
    Terms.session_context_in_profile context /\
    message ==
      Terms.certificate_verify_input context.Terms.context_transcript /\
    DY.event_triggered
      tr1
      context.Terms.context_server.Terms.session_principal
      (Events.event_tag Events.ServerCertificateVerifySigned)
      (signature_origin_content context verification_key message)
  returns signature_predicate tr2 key_usage verification_key message
  with _.
    DY.event_triggered_grows
      tr1 tr2
      context.Terms.context_server.Terms.session_principal
      (Events.event_tag Events.ServerCertificateVerifySigned)
      (signature_origin_content context verification_key message)

val finished_predicate_later:
  tr1:DY.trace ->
  tr2:DY.trace ->
  key_usage:DY.usage{DY.MacKey? key_usage} ->
  key:DY.bytes ->
  message:DY.bytes ->
  Lemma
    (requires
      finished_predicate tr1 key_usage key message /\
      DY.bytes_well_formed tr1 key /\
      DY.bytes_well_formed tr1 message /\
      DY.grows tr1 tr2)
    (ensures finished_predicate tr2 key_usage key message)
let finished_predicate_later tr1 tr2 key_usage key message =
  eliminate exists context.
    Terms.session_context_in_profile context /\
    message == Terms.transcript_hash context.Terms.context_transcript /\
    ((key_usage ==
        DY.MacKey
          "TLS13.ServerFinishedKey"
          (Terms.transcript_hash context.Terms.context_transcript) /\
      DY.event_triggered
        tr1
        context.Terms.context_server.Terms.session_principal
        (Events.event_tag Events.ServerFinishedSent)
        (finished_origin_content context key message)) \/
     (key_usage ==
        DY.MacKey
          "TLS13.ClientFinishedKey"
          (Terms.transcript_hash context.Terms.context_transcript) /\
      DY.event_triggered
        tr1
        context.Terms.context_client.Terms.session_principal
        (Events.event_tag Events.ClientFinishedSent)
        (finished_origin_content context key message)))
  returns finished_predicate tr2 key_usage key message
  with _.
    if key_usage ==
        DY.MacKey
          "TLS13.ServerFinishedKey"
          (Terms.transcript_hash context.Terms.context_transcript)
    then
      DY.event_triggered_grows
        tr1 tr2
        context.Terms.context_server.Terms.session_principal
        (Events.event_tag Events.ServerFinishedSent)
        (finished_origin_content context key message)
    else
      DY.event_triggered_grows
        tr1 tr2
        context.Terms.context_client.Terms.session_principal
        (Events.event_tag Events.ClientFinishedSent)
        (finished_origin_content context key message)

val aead_predicate_later:
  tr1:DY.trace ->
  tr2:DY.trace ->
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (requires
      aead_predicate
        tr1 key_usage key nonce plaintext additional_data /\
      DY.bytes_well_formed tr1 key /\
      DY.bytes_well_formed tr1 nonce /\
      DY.bytes_well_formed tr1 plaintext /\
      DY.bytes_well_formed tr1 additional_data /\
      DY.grows tr1 tr2)
    (ensures
      aead_predicate
        tr2 key_usage key nonce plaintext additional_data)
let aead_predicate_later
  tr1 tr2 key_usage key nonce plaintext additional_data =
  eliminate exists context direction epoch.
    Terms.session_context_in_profile context /\
    aead_usage_matches key_usage direction epoch /\
    DY.event_triggered
      tr1
      (sender_for_direction context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (record_origin_content
        context direction epoch nonce plaintext additional_data key)
  returns
    aead_predicate tr2 key_usage key nonce plaintext additional_data
  with _.
    DY.event_triggered_grows
      tr1 tr2
      (sender_for_direction context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (record_origin_content
        context direction epoch nonce plaintext additional_data key)

let tls_crypto_predicates : DY.crypto_predicates = {
  DY.default_crypto_predicates with
  DY.sign_pred = {
    DY.pred = signature_predicate;
    DY.pred_later = signature_predicate_later;
  };
  DY.mac_pred = {
    DY.pred = finished_predicate;
    DY.pred_later = finished_predicate_later;
  };
  DY.aead_pred = {
    DY.pred = aead_predicate;
    DY.pred_later = aead_predicate_later;
  };
}

instance tls_crypto_invariants: DY.crypto_invariants = {
  DY.usages = Usages.tls_crypto_usages;
  DY.preds = tls_crypto_predicates;
}

let tls_state_predicate
  (tr:DY.trace)
  (principal:DY.principal)
  (state_id:DY.state_id)
  (content:DY.bytes)
  : prop =
  DY.is_knowable_by
    (DY.principal_state_content_label principal state_id content)
    tr
    content

val tls_state_predicate_later:
  tr1:DY.trace ->
  tr2:DY.trace ->
  principal:DY.principal ->
  state_id:DY.state_id ->
  content:DY.bytes ->
  Lemma
    (requires
      tls_state_predicate tr1 principal state_id content /\
      DY.grows tr1 tr2)
    (ensures tls_state_predicate tr2 principal state_id content)
let tls_state_predicate_later tr1 tr2 principal state_id content =
  DY.bytes_invariant_later tr1 tr2 content;
  DY.can_flow_later
    tr1 tr2
    (DY.get_label tr1 content)
    (DY.principal_state_content_label principal state_id content)

let tls_state_invariant : DY.state_predicate = {
  DY.pred = tls_state_predicate;
  DY.pred_later = tls_state_predicate_later;
  DY.pred_knowable = (fun tr principal state_id content -> ());
}

let tls_event_predicate
  (tr:DY.trace)
  (_principal:DY.principal)
  (_tag:string)
  (content:DY.bytes)
  : prop =
  DY.bytes_invariant tr content

let tls_trace_invariants : DY.trace_invariants = {
  DY.state_pred = tls_state_invariant;
  DY.event_pred = tls_event_predicate;
}

instance tls_protocol_invariants: DY.protocol_invariants = {
  DY.crypto_invs = tls_crypto_invariants;
  DY.trace_invs = tls_trace_invariants;
}

let rec trace_extension_hygienic
  (before after:DY.trace)
  : Tot prop (decreases after) =
  if after == before
  then True
  else
    match after with
    | DY.Nil -> False
    | DY.Snoc prefix entry ->
      trace_extension_hygienic before prefix /\
      DY.trace_entry_invariant prefix entry

val trace_extension_preserves_invariant:
  before:DY.trace ->
  after:DY.trace ->
  Lemma
    (requires
      DY.trace_invariant before /\
      trace_extension_hygienic before after)
    (ensures DY.trace_invariant after)
    (decreases after)
let rec trace_extension_preserves_invariant before after =
  if after == before
  then ()
  else
    match after with
    | DY.Nil -> ()
    | DY.Snoc prefix entry ->
      trace_extension_preserves_invariant before prefix;
      reveal_opaque (`%DY.trace_invariant) (DY.trace_invariant)

let secure_product_step
  (before:Product.product_state)
  (action:Product.product_action)
  (after:Product.product_state)
  : prop =
  Product.product_step before action after /\
  trace_extension_hygienic before.Product.product_trace after.Product.product_trace

val secure_product_step_preserves_invariant:
  before:Product.product_state ->
  action:Product.product_action ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step before action after)
    (ensures DY.trace_invariant after.Product.product_trace)
let secure_product_step_preserves_invariant before action after =
  trace_extension_preserves_invariant
    before.Product.product_trace after.Product.product_trace

val session_creation_preserves_invariant:
  before:Product.product_state ->
  shadow:Product.endpoint_shadow ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step before (Product.CreateEndpoint shadow) after)
    (ensures DY.trace_invariant after.Product.product_trace)
let session_creation_preserves_invariant before shadow after =
  secure_product_step_preserves_invariant
    before (Product.CreateEndpoint shadow) after

val honest_transition_preserves_invariant:
  before:Product.product_state ->
  action:Product.product_action{
    Product.HonestGenerate? action \/
    Product.HonestLocal? action \/
    Product.HonestCanonical? action
  } ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step before action after)
    (ensures DY.trace_invariant after.Product.product_trace)
let honest_transition_preserves_invariant before action after =
  secure_product_step_preserves_invariant before action after

val attacker_transition_preserves_invariant:
  before:Product.product_state ->
  action:Product.product_action{
    Product.AttackerInject? action \/
    Product.AttackerRoute? action \/
    Product.AttackerDrop? action \/
    Product.AttackerReplay? action
  } ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step before action after)
    (ensures DY.trace_invariant after.Product.product_trace)
let attacker_transition_preserves_invariant before action after =
  secure_product_step_preserves_invariant before action after

val corruption_transition_preserves_invariant:
  before:Product.product_state ->
  principal:DY.principal ->
  state_id:DY.state_id ->
  timestamp:DY.timestamp ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step
        before
        (Product.CorruptState principal state_id timestamp)
        after)
    (ensures DY.trace_invariant after.Product.product_trace)
let corruption_transition_preserves_invariant
  before principal state_id timestamp after =
  secure_product_step_preserves_invariant
    before (Product.CorruptState principal state_id timestamp) after

let rec secure_product_execution
  (initial:Product.product_state)
  (transitions:list Product.product_transition)
  (final:Product.product_state)
  : Tot prop (decreases transitions) =
  match transitions with
  | [] ->
    final == initial /\
    Product.product_well_formed initial
  | transition :: rest ->
    transition.Product.transition_before == initial /\
    secure_product_step
      transition.Product.transition_before
      transition.Product.transition_action
      transition.Product.transition_after /\
    secure_product_execution
      transition.Product.transition_after rest final

let securely_reachable_product_state
  (initial:Product.product_state)
  (transitions:list Product.product_transition)
  (final:Product.product_state)
  : prop =
  Product.initial_product_state initial /\
  DY.trace_invariant initial.Product.product_trace /\
  secure_product_execution initial transitions final

val secure_product_execution_is_structural:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  final:Product.product_state ->
  Lemma
    (requires secure_product_execution initial transitions final)
    (ensures Product.product_execution initial transitions final)
    (decreases (List.Tot.length transitions))
let rec secure_product_execution_is_structural initial transitions final =
  match transitions with
  | [] -> ()
  | transition :: rest ->
    secure_product_execution_is_structural
      transition.Product.transition_after rest final

val secure_product_execution_preserves_invariant:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  final:Product.product_state ->
  Lemma
    (requires
      secure_product_execution initial transitions final /\
      DY.trace_invariant initial.Product.product_trace)
    (ensures DY.trace_invariant final.Product.product_trace)
    (decreases (List.Tot.length transitions))
let rec secure_product_execution_preserves_invariant
  initial transitions final =
  match transitions with
  | [] -> ()
  | transition :: rest ->
    trace_extension_preserves_invariant
      transition.Product.transition_before.Product.product_trace
      transition.Product.transition_after.Product.product_trace;
    secure_product_execution_preserves_invariant
      transition.Product.transition_after rest final

val securely_reachable_trace_invariant:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  final:Product.product_state ->
  Lemma
    (requires securely_reachable_product_state initial transitions final)
    (ensures DY.trace_invariant final.Product.product_trace)
let securely_reachable_trace_invariant initial transitions final =
  secure_product_execution_preserves_invariant initial transitions final

val attacker_only_knows_publishable:
  state:Product.product_state ->
  message:DY.bytes ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows state.Product.product_trace message)
    (ensures DY.is_publishable state.Product.product_trace message)
let attacker_only_knows_publishable state message =
  DY.attacker_only_knows_publishable_values
    state.Product.product_trace message

let rec securely_realizable_execution
  (product_initial:Product.product_state)
  (concrete_initial:TLS13.Spec.StateMachine.connection_state)
  (concrete:list Product.concrete_transition)
  (concrete_final:TLS13.Spec.StateMachine.connection_state)
  (realizations:list Product.transition_realization)
  (product_final:Product.product_state)
  : Tot prop (decreases concrete) =
  match concrete, realizations with
  | [], [] ->
    concrete_final == concrete_initial /\
    product_final == product_initial /\
    Product.product_well_formed product_initial
  | concrete_head :: concrete_tail,
    realization_head :: realization_tail ->
    concrete_head.Product.concrete_before == concrete_initial /\
    Product.transition_realization_obligations
      product_initial concrete_head realization_head /\
    trace_extension_hygienic
      product_initial.Product.product_trace
      realization_head.Product.realization_after_state.Product.product_trace /\
    securely_realizable_execution
      realization_head.Product.realization_after_state
      concrete_head.Product.concrete_after
      concrete_tail
      concrete_final
      realization_tail
      product_final
  | _, _ -> False

val securely_realizable_execution_is_structural:
  product_initial:Product.product_state ->
  concrete_initial:TLS13.Spec.StateMachine.connection_state ->
  concrete:list Product.concrete_transition ->
  concrete_final:TLS13.Spec.StateMachine.connection_state ->
  realizations:list Product.transition_realization ->
  product_final:Product.product_state ->
  Lemma
    (requires
      securely_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final)
    (ensures
      Product.symbolically_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final)
    (decreases (List.Tot.length concrete))
let rec securely_realizable_execution_is_structural
  product_initial concrete_initial concrete concrete_final
  realizations product_final =
  match concrete, realizations with
  | [], [] -> ()
  | concrete_head :: concrete_tail,
    realization_head :: realization_tail ->
    securely_realizable_execution_is_structural
      realization_head.Product.realization_after_state
      concrete_head.Product.concrete_after
      concrete_tail
      concrete_final
      realization_tail
      product_final
  | _, _ -> ()

val complete_secure_execution_lifts:
  product_initial:Product.product_state ->
  concrete_initial:TLS13.Spec.StateMachine.connection_state ->
  concrete:list Product.concrete_transition ->
  concrete_final:TLS13.Spec.StateMachine.connection_state ->
  realizations:list Product.transition_realization ->
  product_final:Product.product_state ->
  Lemma
    (requires
      securely_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final)
    (ensures (
      let product =
        Product.lifted_product_transitions
          product_initial concrete realizations in
      Product.concrete_execution concrete_initial concrete concrete_final /\
      secure_product_execution product_initial product product_final /\
      Product.execution_projects_exactly concrete product))
    (decreases (List.Tot.length concrete))
let rec complete_secure_execution_lifts
  product_initial concrete_initial concrete concrete_final
  realizations product_final =
  match concrete, realizations with
  | [], [] -> ()
  | concrete_head :: concrete_tail,
    realization_head :: realization_tail ->
    Product.realizable_transition_lifts
      product_initial concrete_head realization_head;
    complete_secure_execution_lifts
      realization_head.Product.realization_after_state
      concrete_head.Product.concrete_after
      concrete_tail
      concrete_final
      realization_tail
      product_final
  | _, _ -> ()

val concrete_execution_has_secure_product_lift:
  product_initial:Product.product_state ->
  concrete_initial:TLS13.Spec.StateMachine.connection_state ->
  concrete:list Product.concrete_transition ->
  concrete_final:TLS13.Spec.StateMachine.connection_state ->
  realizations:list Product.transition_realization ->
  product_final:Product.product_state ->
  Lemma
    (requires
      securely_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final)
    (ensures
      exists product.
        product ==
          Product.lifted_product_transitions
            product_initial concrete realizations /\
        secure_product_execution product_initial product product_final /\
        Product.execution_projects_exactly concrete product)
let concrete_execution_has_secure_product_lift
  product_initial concrete_initial concrete concrete_final
  realizations product_final =
  complete_secure_execution_lifts
    product_initial concrete_initial concrete concrete_final
    realizations product_final

val signature_origin:
  tr:DY.trace ->
  key_usage:DY.usage{DY.SigKey? key_usage} ->
  verification_key:DY.bytes ->
  message:DY.bytes ->
  Lemma
    (requires
      DY.sign_pred.DY.pred tr key_usage verification_key message)
    (ensures
      exists context.
        Terms.session_context_in_profile context /\
        key_usage ==
          Usages.signing_key_usage
            context.Terms.context_server.Terms.session_principal
            verification_key /\
        message ==
          Terms.certificate_verify_input
            context.Terms.context_transcript /\
        DY.event_triggered
          tr
          context.Terms.context_server.Terms.session_principal
          (Events.event_tag Events.ServerCertificateVerifySigned)
          (signature_origin_content context verification_key message))
let signature_origin tr key_usage verification_key message = ()

val finished_origin:
  tr:DY.trace ->
  key_usage:DY.usage{DY.MacKey? key_usage} ->
  key:DY.bytes ->
  message:DY.bytes ->
  Lemma
    (requires DY.mac_pred.DY.pred tr key_usage key message)
    (ensures finished_predicate tr key_usage key message)
let finished_origin tr key_usage key message = ()

val aead_origin:
  tr:DY.trace ->
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (requires
      DY.aead_pred.DY.pred
        tr key_usage key nonce plaintext additional_data)
    (ensures
      aead_predicate
        tr key_usage key nonce plaintext additional_data)
let aead_origin
  tr key_usage key nonce plaintext additional_data = ()
