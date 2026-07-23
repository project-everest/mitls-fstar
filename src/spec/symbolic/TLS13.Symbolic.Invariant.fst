module TLS13.Symbolic.Invariant

(*
 * DY trace invariants and their preservation by the TLS product semantics.
 *
 * The cryptographic predicates require every honest signature, Finished MAC,
 * and AEAD encryption to have a matching protocol-origin event.  The product
 * semantics is strengthened with trace_extension_hygienic, a load-bearing
 * premise requiring each appended entry to satisfy DY.trace_entry_invariant.
 * Secure reachability therefore combines structural product execution with the
 * invariant discipline needed by the authentication and secrecy theorems.
 *)

module DY = DY.Core
module Events = TLS13.Symbolic.Events
module Product = TLS13.Symbolic.Product
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

(* Encode the origin-event payload for a server CertificateVerify signature. *)
let signature_origin_content
  (context:Terms.session_context)
  (verification_key message:DY.bytes)
  : DY.bytes =
  Events.handshake_event_content
    context
    (DY.Concat verification_key message)

(* Encode the origin-event payload for a server or client Finished MAC. *)
let finished_origin_content
  (context:Terms.session_context)
  (key message:DY.bytes)
  : DY.bytes =
  Events.handshake_event_content context (DY.Concat key message)

(* Encode the complete origin-event payload for a protected record. *)
let record_origin_content
  (context:Terms.session_context)
  (direction:Events.record_direction)
  (epoch:Events.record_epoch)
  (sequence_number nonce plaintext additional_data key:DY.bytes)
  : DY.bytes =
  Events.record_event_content
    context direction epoch sequence_number plaintext
    (Terms.protected_record key nonce plaintext additional_data)

(*
 * Signature-origin policy: the usage, verification key, message, context, and
 * ServerCertificateVerifySigned event must agree exactly.
 *)
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

(*
 * Finished-origin policy for server and client Finished MACs.
 *)
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

(* Relate an AEAD usage tag to an exact record direction and epoch. *)
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

(* Select the symbolic sending endpoint for a record direction. *)
let sender_for_direction
  (context:Terms.session_context)
  (direction:Events.record_direction)
  : Terms.endpoint_session =
  match direction with
  | Events.ClientToServer -> context.Terms.context_client
  | Events.ServerToClient -> context.Terms.context_server

(*
 * AEAD-origin policy: usage, context, direction, epoch, sequence-token nonce,
 * and ProtectedRecordSent event must agree exactly.
 *)
let aead_predicate
  (tr:DY.trace)
  (key_usage:DY.usage{DY.AeadKey? key_usage})
  (key nonce plaintext additional_data:DY.bytes)
  : prop =
  exists context direction epoch sequence_number.
    Terms.session_context_in_profile context /\
    aead_usage_matches key_usage direction epoch /\
    nonce == Terms.record_nonce_from_sequence_token sequence_number /\
    DY.event_triggered
      tr
      (sender_for_direction context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (record_origin_content
        context direction epoch sequence_number nonce
        plaintext additional_data key)

(*
 * Preserve the signature-origin predicate under trace growth.
 *
 * Requirement: the predicate and byte well-formedness hold on tr1, and tr2
 * grows tr1.
 * Guarantee: the same signature predicate holds on tr2.
 *)
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
(* Extract the origin context and transport its event with event_triggered_grows. *)
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

(*
 * Preserve the Finished-origin predicate under trace growth.
 *
 * Requirement: the predicate and byte well-formedness hold on tr1, and tr2
 * grows tr1.
 * Guarantee: the same Finished predicate holds on tr2.
 *)
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
(* Extract the context and grow the server or client origin event by usage. *)
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

(*
 * Preserve the AEAD-origin predicate under trace growth.
 *
 * Requirement: the predicate and all term invariants hold on tr1, and tr2
 * grows tr1.
 * Guarantee: the same AEAD predicate holds on tr2.
 *)
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
(* Extract the record witnesses and transport ProtectedRecordSent to tr2. *)
let aead_predicate_later
  tr1 tr2 key_usage key nonce plaintext additional_data =
  eliminate exists context direction epoch sequence_number.
    Terms.session_context_in_profile context /\
    aead_usage_matches key_usage direction epoch /\
    nonce == Terms.record_nonce_from_sequence_token sequence_number /\
    DY.event_triggered
      tr1
      (sender_for_direction context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (record_origin_content
        context direction epoch sequence_number nonce
        plaintext additional_data key)
  returns
    aead_predicate tr2 key_usage key nonce plaintext additional_data
  with _.
    DY.event_triggered_grows
      tr1 tr2
      (sender_for_direction context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (record_origin_content
        context direction epoch sequence_number nonce
        plaintext additional_data key)

(*
 * Install the TLS-specific signature, MAC, and AEAD origin predicates while
 * retaining DY defaults for cryptographic primitives not specialized here.
 *)
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

(* Bind TLS usage classification and origin predicates as DY crypto invariants. *)
instance tls_crypto_invariants: DY.crypto_invariants = {
  DY.usages = Usages.tls_crypto_usages;
  DY.preds = tls_crypto_predicates;
}

(* Require endpoint state content to flow to its principal/state-specific label. *)
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

(*
 * Preserve the endpoint-state predicate under trace growth.
 *
 * Requirement: state content satisfies tls_state_predicate on tr1 and tr2 grows
 * tr1.
 * Guarantee: it satisfies tls_state_predicate on tr2.
 *)
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
(* Grow the byte invariant and permitted label flow to the later trace. *)
let tls_state_predicate_later tr1 tr2 principal state_id content =
  DY.bytes_invariant_later tr1 tr2 content;
  DY.can_flow_later
    tr1 tr2
    (DY.get_label tr1 content)
    (DY.principal_state_content_label principal state_id content)

(* Package state validity, monotonicity, and knowability as a DY predicate. *)
let tls_state_invariant : DY.state_predicate = {
  DY.pred = tls_state_predicate;
  DY.pred_later = tls_state_predicate_later;
  DY.pred_knowable = (fun tr principal state_id content -> ());
}

(* Require every event payload to satisfy the generic DY byte invariant. *)
let tls_event_predicate
  (tr:DY.trace)
  (_principal:DY.principal)
  (_tag:string)
  (content:DY.bytes)
  : prop =
  DY.bytes_invariant tr content

(* Package TLS state and event predicates into DY trace invariants. *)
let tls_trace_invariants : DY.trace_invariants = {
  DY.state_pred = tls_state_invariant;
  DY.event_pred = tls_event_predicate;
}

(* Install the TLS crypto and trace invariants as the active protocol instance. *)
instance tls_protocol_invariants: DY.protocol_invariants = {
  DY.crypto_invs = tls_crypto_invariants;
  DY.trace_invs = tls_trace_invariants;
}

(*
 * Require every entry appended after before to be invariant-valid at its prefix.
 *
 * This is an explicit premise on secure lifting, not a consequence proved from
 * the structural Product.product_step relation alone.
 *)
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

(*
 * Preserve the global DY trace invariant across a hygienic extension.
 *
 * Requirement: before is invariant and every appended entry is prefix-valid.
 * Guarantee: after is invariant.
 *)
val trace_extension_preserves_invariant:
  before:DY.trace ->
  after:DY.trace ->
  Lemma
    (requires
      DY.trace_invariant before /\
      trace_extension_hygienic before after)
    (ensures DY.trace_invariant after)
    (decreases after)
(* Induct backward through the snoc extension and reveal trace_invariant per entry. *)
let rec trace_extension_preserves_invariant before after =
  if after == before
  then ()
  else
    match after with
    | DY.Nil -> ()
    | DY.Snoc prefix entry ->
      trace_extension_preserves_invariant before prefix;
      reveal_opaque (`%DY.trace_invariant) (DY.trace_invariant)

(*
 * Strengthen a structural product step with hygienic symbolic trace extension.
 *)
let secure_product_step
  (before:Product.product_state)
  (action:Product.product_action)
  (after:Product.product_state)
  : prop =
  Product.product_step before action after /\
  trace_extension_hygienic before.Product.product_trace after.Product.product_trace

(*
 * Preserve the DY invariant across one secure product step.
 *
 * Requirement: before's trace is invariant and secure_product_step holds.
 * Guarantee: after's trace is invariant.
 *)
val secure_product_step_preserves_invariant:
  before:Product.product_state ->
  action:Product.product_action ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step before action after)
    (ensures DY.trace_invariant after.Product.product_trace)
(* Apply trace_extension_preserves_invariant to the step's hygiene conjunct. *)
let secure_product_step_preserves_invariant before action after =
  trace_extension_preserves_invariant
    before.Product.product_trace after.Product.product_trace

(*
 * Specialized preservation theorem for endpoint creation.
 *
 * Requirement: invariant before and a secure CreateEndpoint step.
 * Guarantee: invariant after.
 *)
val session_creation_preserves_invariant:
  before:Product.product_state ->
  shadow:Product.endpoint_shadow ->
  after:Product.product_state ->
  Lemma
    (requires
      DY.trace_invariant before.Product.product_trace /\
      secure_product_step before (Product.CreateEndpoint shadow) after)
    (ensures DY.trace_invariant after.Product.product_trace)
(* Instantiate generic secure-step preservation with CreateEndpoint. *)
let session_creation_preserves_invariant before shadow after =
  secure_product_step_preserves_invariant
    before (Product.CreateEndpoint shadow) after

(*
 * Specialized preservation theorem for honest generation/local/canonical steps.
 *
 * Requirement: invariant before and the selected secure honest step.
 * Guarantee: invariant after.
 *)
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
(* Reuse generic secure-step preservation. *)
let honest_transition_preserves_invariant before action after =
  secure_product_step_preserves_invariant before action after

(*
 * Specialized preservation theorem for DY network-control steps.
 *
 * Requirement: invariant before and the selected secure attacker step.
 * Guarantee: invariant after.
 *)
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
(* Reuse generic secure-step preservation. *)
let attacker_transition_preserves_invariant before action after =
  secure_product_step_preserves_invariant before action after

(*
 * Specialized preservation theorem for state corruption.
 *
 * Requirement: invariant before and the specified secure CorruptState step.
 * Guarantee: invariant after.
 *)
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
(* Reuse generic preservation with the concrete corruption action. *)
let corruption_transition_preserves_invariant
  before principal state_id timestamp after =
  secure_product_step_preserves_invariant
    before (Product.CorruptState principal state_id timestamp) after

(*
 * Execution relation over secure_product_step rather than structural steps.
 *)
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

(*
 * Secure reachability from a security-origin-free initial state whose trace is
 * already invariant.
 *)
let securely_reachable_product_state
  (initial:Product.product_state)
  (transitions:list Product.product_transition)
  (final:Product.product_state)
  : prop =
  Product.initial_product_state initial /\
  DY.trace_invariant initial.Product.product_trace /\
  secure_product_execution initial transitions final

(*
 * Forget trace hygiene to obtain the underlying structural product execution.
 *
 * Requirement: secure_product_execution.
 * Guarantee: Product.product_execution.
 *)
val secure_product_execution_is_structural:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  final:Product.product_state ->
  Lemma
    (requires secure_product_execution initial transitions final)
    (ensures Product.product_execution initial transitions final)
    (decreases (List.Tot.length transitions))
(* Induct over transitions and project Product.product_step from each secure step. *)
let rec secure_product_execution_is_structural initial transitions final =
  match transitions with
  | [] -> ()
  | transition :: rest ->
    secure_product_execution_is_structural
      transition.Product.transition_after rest final

(*
 * Preserve the trace invariant throughout a secure product execution.
 *
 * Requirement: secure execution and invariant initial trace.
 * Guarantee: invariant final trace.
 *)
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
(* Induct over transitions using hygienic extension preservation at each step. *)
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

(*
 * Project final trace invariance from secure reachability.
 *
 * Requirement: securely_reachable_product_state.
 * Guarantee: final trace is DY.trace_invariant.
 *)
val securely_reachable_trace_invariant:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  final:Product.product_state ->
  Lemma
    (requires securely_reachable_product_state initial transitions final)
    (ensures DY.trace_invariant final.Product.product_trace)
(* Apply execution-level preservation to the reachability components. *)
let securely_reachable_trace_invariant initial transitions final =
  secure_product_execution_preserves_invariant initial transitions final

(*
 * Convert attacker knowledge into DY publishability under the invariant.
 *
 * Requirement: invariant state trace and attacker_knows message.
 * Guarantee: message is publishable on that trace.
 *)
val attacker_only_knows_publishable:
  state:Product.product_state ->
  message:DY.bytes ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows state.Product.product_trace message)
    (ensures DY.is_publishable state.Product.product_trace message)
(* Invoke the corresponding generic DY invariant theorem. *)
let attacker_only_knows_publishable state message =
  DY.attacker_only_knows_publishable_values
    state.Product.product_trace message

(*
 * Conditional concrete lifting strengthened with per-transition trace hygiene.
 *
 * Like Product.symbolically_realizable_execution, this is a supplied witness
 * relation; it does not derive realization or hygiene from concrete execution.
 *)
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

(*
 * Forget hygiene from a securely realizable concrete execution.
 *
 * Requirement: securely_realizable_execution.
 * Guarantee: Product.symbolically_realizable_execution.
 *)
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
(* Induct over concrete steps and discard each hygiene conjunct. *)
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

(*
 * Lift a securely realizable concrete execution to a secure product execution.
 *
 * Requirement: one structural realization and hygienic extension per concrete
 * step.
 * Guarantee: legal concrete execution, secure product execution, and exact
 * pointwise projection.
 *)
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
(* Induct, use Product.realizable_transition_lifts, and retain each hygiene fact. *)
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

(*
 * Package secure conditional lifting as existence of a product execution.
 *
 * Requirement: securely_realizable_execution.
 * Guarantee: the constructed product list executes securely and projects
 * exactly to the concrete execution.
 *)
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
(* Use complete_secure_execution_lifts and the canonical lifted transition list. *)
let concrete_execution_has_secure_product_lift
  product_initial concrete_initial concrete concrete_final
  realizations product_final =
  complete_secure_execution_lifts
    product_initial concrete_initial concrete concrete_final
    realizations product_final

(*
 * Expose the origin context guaranteed by the installed signature predicate.
 *
 * Requirement: DY's active sign predicate holds.
 * Guarantee: an in-profile context fixes usage, message, and the matching
 * ServerCertificateVerifySigned event.
 *)
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
(* The active predicate is definitionally signature_predicate. *)
let signature_origin tr key_usage verification_key message = ()

(*
 * Expose the installed Finished origin predicate.
 *
 * Requirement: DY's active MAC predicate holds.
 * Guarantee: finished_predicate holds for the same usage, key, and message.
 *)
val finished_origin:
  tr:DY.trace ->
  key_usage:DY.usage{DY.MacKey? key_usage} ->
  key:DY.bytes ->
  message:DY.bytes ->
  Lemma
    (requires DY.mac_pred.DY.pred tr key_usage key message)
    (ensures finished_predicate tr key_usage key message)
(* The active predicate is definitionally finished_predicate. *)
let finished_origin tr key_usage key message = ()

(*
 * Expose the installed protected-record origin predicate.
 *
 * Requirement: DY's active AEAD predicate holds.
 * Guarantee: aead_predicate holds for the same cryptographic arguments.
 *)
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
(* The active predicate is definitionally aead_predicate. *)
let aead_origin
  tr key_usage key nonce plaintext additional_data = ()
