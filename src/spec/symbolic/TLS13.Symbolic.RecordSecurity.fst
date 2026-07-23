module TLS13.Symbolic.RecordSecurity

(*
 * Symbolic integrity, replay resistance, origin, and confidentiality results
 * for TLS 1.3 protected records.
 *
 * Exact record realizations from Product connect concrete AEAD wire behavior to
 * symbolic encryption/decryption.  Successful decryption under a non-publishable
 * key yields an exact ProtectedRecordSent origin, fixing direction, epoch,
 * sequence token, nonce, key, AAD, plaintext, and protected term.  The symbolic
 * nonce is Hash(public sequence-token): an opaque injective execution identity,
 * not a claim that concrete TLS hashes sequence numbers.
 *)

module B = TLS13.Bytes
module Bridge = TLS13.Symbolic.Bridge
module Canonical = TLS13.Spec.StateMachine.Canonical
module CL = TLS13.ConnectionLog
module DY = DY.Core
module Events = TLS13.Symbolic.Events
module Invariant = TLS13.Symbolic.Invariant
module Labels = TLS13.Symbolic.Labels
module M = TLS13.Messages
module Product = TLS13.Symbolic.Product
module Secrecy = TLS13.Symbolic.Secrecy
module SM = TLS13.Spec.StateMachine
module Terms = TLS13.Symbolic.Terms

(*
 * Prove nonce inequality after a sequence-number change.
 *
 * Requirement: before_sequence differs from after_sequence.
 * Guarantee: their symbolic record nonces are unequal for the same IV.
 *)
val record_nonce_changes_with_sequence:
  static_iv:DY.bytes ->
  before_sequence:nat ->
  after_sequence:nat ->
  Lemma
    (requires before_sequence =!= after_sequence)
    (ensures
      Terms.record_nonce static_iv before_sequence =!=
      Terms.record_nonce static_iv after_sequence)
(* Contradict nonce equality using Terms.record_nonce_injective. *)
let record_nonce_changes_with_sequence
  static_iv before_sequence after_sequence =
  if Terms.record_nonce static_iv before_sequence =
     Terms.record_nonce static_iv after_sequence
  then Terms.record_nonce_injective
    static_iv before_sequence after_sequence

(*
 * Classify the non-literal symbolic record nonce at the representation boundary.
 *
 * Requirement: none.
 * Guarantee: Bridge.represents requires an execution-local explicit binding.
 *)
val record_nonce_uses_execution_binding:
  static_iv:DY.bytes ->
  sequence_number:nat ->
  Lemma
    (ensures
      Bridge.requires_explicit_binding
        (Terms.record_nonce static_iv sequence_number))
(* Reduce the nonce constructor and explicit-binding classification. *)
let record_nonce_uses_execution_binding static_iv sequence_number = ()

(*
 * Establish that the record nonce token is publicly labeled.
 *
 * Requirement: none. Guarantee: its DY label is public.
 *)
val record_nonce_is_public:
  trace:DY.trace ->
  static_iv:DY.bytes ->
  sequence_number:nat ->
  Lemma
    (ensures
      DY.get_label
        trace
        (Terms.record_nonce static_iv sequence_number) ==
      DY.public)
(* Normalize the hash-of-public-sequence-token construction and label rules. *)
let record_nonce_is_public trace static_iv sequence_number =
  normalize_term_spec Terms.record_nonce;
  normalize_term_spec Terms.record_nonce_from_sequence_token;
  normalize_term_spec Terms.encode_record_sequence_number;
  normalize_term_spec Terms.public_bytes;
  normalize_term_spec DY.get_label

(*
 * Reject decryption after substituting key, nonce, or additional data.
 *
 * Requirement: at least one selected decryption argument differs.
 * Guarantee: symbolic AEAD decryption returns None.
 *)
val protected_record_substitution_rejected:
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  substituted_key:DY.bytes ->
  substituted_nonce:DY.bytes ->
  substituted_additional_data:DY.bytes ->
  Lemma
    (requires
      substituted_key =!= key \/
      substituted_nonce =!= nonce \/
      substituted_additional_data =!= additional_data)
    (ensures
      DY.aead_dec
        substituted_key
        substituted_nonce
        (Terms.protected_record key nonce plaintext additional_data)
        substituted_additional_data ==
      None)
(* Expose the AEAD constructor and normalize symbolic encrypt/decrypt matching. *)
let protected_record_substitution_rejected
  key nonce plaintext additional_data
  substituted_key substituted_nonce substituted_additional_data =
  Terms.protected_record_definition
    key nonce plaintext additional_data;
  normalize_term_spec DY.aead_enc;
  normalize_term_spec DY.aead_dec

(*
 * Reject a protected record under a key from the opposite direction.
 *
 * Requirement: direction keys differ.
 * Guarantee: decryption under other_direction_key returns None.
 *)
val cross_direction_record_substitution_rejected:
  direction_key:DY.bytes ->
  other_direction_key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (requires direction_key =!= other_direction_key)
    (ensures
      DY.aead_dec
        other_direction_key nonce
        (Terms.protected_record
          direction_key nonce plaintext additional_data)
        additional_data ==
      None)
(* Instantiate the generic substitution theorem with only the key changed. *)
let cross_direction_record_substitution_rejected
  direction_key other_direction_key nonce plaintext additional_data =
  protected_record_substitution_rejected
    direction_key nonce plaintext additional_data
    other_direction_key nonce additional_data

(*
 * Reject a protected record under a key from another epoch.
 *
 * Requirement: epoch keys differ.
 * Guarantee: decryption under other_epoch_key returns None.
 *)
val cross_epoch_record_substitution_rejected:
  epoch_key:DY.bytes ->
  other_epoch_key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (requires epoch_key =!= other_epoch_key)
    (ensures
      DY.aead_dec
        other_epoch_key nonce
        (Terms.protected_record epoch_key nonce plaintext additional_data)
        additional_data ==
      None)
(* Instantiate the generic substitution theorem with only the key changed. *)
let cross_epoch_record_substitution_rejected
  epoch_key other_epoch_key nonce plaintext additional_data =
  protected_record_substitution_rejected
    epoch_key nonce plaintext additional_data
    other_epoch_key nonce additional_data

(*
 * Reject replay after the receiver has advanced its expected sequence number.
 *
 * Requirement: original and current sequence numbers differ.
 * Guarantee: decryption under the current symbolic nonce returns None.
 *)
val protected_record_replay_rejected_after_sequence_advance:
  key:DY.bytes ->
  static_iv:DY.bytes ->
  original_sequence:nat ->
  current_sequence:nat ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (requires original_sequence =!= current_sequence)
    (ensures
      DY.aead_dec
        key
        (Terms.record_nonce static_iv current_sequence)
        (Terms.protected_record
          key
          (Terms.record_nonce static_iv original_sequence)
          plaintext
          additional_data)
        additional_data ==
      None)
(* Derive nonce inequality and instantiate nonce substitution rejection. *)
let protected_record_replay_rejected_after_sequence_advance
  key static_iv original_sequence current_sequence
  plaintext additional_data =
  record_nonce_changes_with_sequence
    static_iv original_sequence current_sequence;
  protected_record_substitution_rejected
    key
    (Terms.record_nonce static_iv original_sequence)
    plaintext
    additional_data
    key
    (Terms.record_nonce static_iv current_sequence)
    additional_data

(*
 * Evaluate decryption of an accepted record's exact symbolic protected term.
 *
 * Requirement: none beyond the accepted-record witness.
 * Guarantee: AEAD decryption returns the witness's symbolic plaintext.
 *)
val accepted_record_symbolically_decrypts:
  record:Product.accepted_record_realization ->
  Lemma
    (ensures
      DY.aead_dec
        record.Product.accepted_record_symbolic_key
        (Product.accepted_record_symbolic_nonce record)
        (Product.accepted_record_protected_term record)
        (Terms.protected_record_additional_data
          record.Product.accepted_record_concrete_aad) ==
      Some record.Product.accepted_record_symbolic_plaintext)
(* Expose the protected-term constructor and apply DY.aead_dec_enc. *)
let accepted_record_symbolically_decrypts record =
  Product.accepted_record_protected_term_definition record;
  Terms.protected_record_definition
    record.Product.accepted_record_symbolic_key
    (Product.accepted_record_symbolic_nonce record)
    record.Product.accepted_record_symbolic_plaintext
    (Terms.protected_record_additional_data
      record.Product.accepted_record_concrete_aad);
  DY.aead_dec_enc
    record.Product.accepted_record_symbolic_key
    (Product.accepted_record_symbolic_nonce record)
    record.Product.accepted_record_symbolic_plaintext
    (Terms.protected_record_additional_data
      record.Product.accepted_record_concrete_aad)

(*
 * Prove that an AEAD usage tag uniquely identifies direction and epoch.
 *
 * Requirement: one usage matches both direction/epoch pairs.
 * Guarantee: both pairs are equal.
 *)
val aead_usage_identifies_direction_and_epoch:
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  left_direction:Events.record_direction ->
  left_epoch:Events.record_epoch ->
  right_direction:Events.record_direction ->
  right_epoch:Events.record_epoch ->
  Lemma
    (requires
      Invariant.aead_usage_matches
        key_usage left_direction left_epoch /\
      Invariant.aead_usage_matches
        key_usage right_direction right_epoch)
    (ensures
      left_direction == right_direction /\
      left_epoch == right_epoch)
(* Exhaust the four usage-tag cases encoded by Invariant.aead_usage_matches. *)
let aead_usage_identifies_direction_and_epoch
  key_usage left_direction left_epoch right_direction right_epoch =
  match left_direction, left_epoch, right_direction, right_epoch with
  | Events.ClientToServer, Events.HandshakeEpoch,
    Events.ClientToServer, Events.HandshakeEpoch
  | Events.ClientToServer, Events.ApplicationEpoch,
    Events.ClientToServer, Events.ApplicationEpoch
  | Events.ServerToClient, Events.HandshakeEpoch,
    Events.ServerToClient, Events.HandshakeEpoch
  | Events.ServerToClient, Events.ApplicationEpoch,
    Events.ServerToClient, Events.ApplicationEpoch -> ()
  | _, _, _, _ -> ()

(*
 * Derive the installed AEAD-origin predicate from successful decryption.
 *
 * Requirement: invariant/well-formed arguments, key usage, successful symbolic
 * decryption, and a non-publishable key.
 * Guarantee: Invariant.aead_predicate.
 *)
val successful_record_decryption_has_aead_origin:
  trace:DY.trace ->
  key:DY.bytes ->
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  nonce:DY.bytes ->
  ciphertext:DY.bytes ->
  additional_data:DY.bytes ->
  plaintext:DY.bytes ->
  Lemma
    (requires
      DY.trace_invariant trace /\
      DY.bytes_invariant trace key /\
      DY.bytes_invariant trace nonce /\
      DY.bytes_invariant trace ciphertext /\
      DY.bytes_invariant trace additional_data /\
      key `DY.has_usage trace` key_usage /\
      DY.aead_dec key nonce ciphertext additional_data == Some plaintext /\
      ~(DY.is_publishable trace key))
    (ensures
      Invariant.aead_predicate
        trace key_usage key nonce plaintext additional_data)
(* Apply generic DY AEAD decryption soundness under the active invariant. *)
let successful_record_decryption_has_aead_origin
  trace key key_usage nonce ciphertext additional_data plaintext =
  DY.bytes_invariant_aead_dec trace key nonce ciphertext additional_data

(*
 * Expose the exact ProtectedRecordSent event behind successful decryption.
 *
 * Requirement: the same invariant, usage, decryption, and key-secrecy facts.
 * Guarantee: an in-profile context, direction, epoch, sequence token, and exact
 * sender event satisfying the AEAD-origin predicate.
 *)
val successful_record_decryption_has_sent_event:
  trace:DY.trace ->
  key:DY.bytes ->
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  nonce:DY.bytes ->
  ciphertext:DY.bytes ->
  additional_data:DY.bytes ->
  plaintext:DY.bytes ->
  Lemma
    (requires
      DY.trace_invariant trace /\
      DY.bytes_invariant trace key /\
      DY.bytes_invariant trace nonce /\
      DY.bytes_invariant trace ciphertext /\
      DY.bytes_invariant trace additional_data /\
      key `DY.has_usage trace` key_usage /\
      DY.aead_dec key nonce ciphertext additional_data == Some plaintext /\
      ~(DY.is_publishable trace key))
    (ensures
      exists context direction epoch sequence_number.
        Terms.session_context_in_profile context /\
        Invariant.aead_usage_matches key_usage direction epoch /\
        nonce == Terms.record_nonce_from_sequence_token sequence_number /\
        DY.event_triggered
          trace
          (Invariant.sender_for_direction
            context direction).Terms.session_principal
          (Events.event_tag Events.ProtectedRecordSent)
          (Invariant.record_origin_content
            context direction epoch sequence_number
            nonce plaintext additional_data key))
(* Obtain aead_predicate, whose definition supplies the existential event. *)
let successful_record_decryption_has_sent_event
  trace key key_usage nonce ciphertext additional_data plaintext =
  successful_record_decryption_has_aead_origin
    trace key key_usage nonce ciphertext additional_data plaintext

(*
 * Complete premises needed to authenticate one accepted concrete record.
 *
 * These include exact Product realization, trace/term invariants, key usage
 * matching the witness direction and epoch, and key non-publishability.
 *)
let accepted_record_integrity_conditions
  (representation:Bridge.representation)
  (shadow:Product.endpoint_shadow)
  (event:SM.conn_event)
  (raw:B.bytes)
  (record:Product.accepted_record_realization)
  (key_usage:DY.usage{DY.AeadKey? key_usage})
  : prop =
  Product.accepted_record_realizes
    representation shadow event raw record /\
  DY.trace_invariant representation.Bridge.representation_trace /\
  DY.bytes_invariant
    representation.Bridge.representation_trace
    record.Product.accepted_record_symbolic_key /\
  DY.bytes_invariant
    representation.Bridge.representation_trace
    (Product.accepted_record_symbolic_nonce record) /\
  DY.bytes_invariant
    representation.Bridge.representation_trace
    (Product.accepted_record_protected_term record) /\
  DY.bytes_invariant
    representation.Bridge.representation_trace
    (Terms.protected_record_additional_data
      record.Product.accepted_record_concrete_aad) /\
  record.Product.accepted_record_symbolic_key
    `DY.has_usage representation.Bridge.representation_trace`
    key_usage /\
  Invariant.aead_usage_matches
    key_usage
    record.Product.accepted_record_direction
    record.Product.accepted_record_epoch /\
  ~(DY.is_publishable
    representation.Bridge.representation_trace
    record.Product.accepted_record_symbolic_key)

(*
 * Derive some symbolic sent origin for an accepted concrete record.
 *
 * Requirement: accepted_record_integrity_conditions.
 * Guarantee: an in-profile origin fixes usage, nonce token, sender, direction,
 * epoch, plaintext, AAD, and key.
 *)
val accepted_record_has_sent_origin:
  representation:Bridge.representation ->
  shadow:Product.endpoint_shadow ->
  event:SM.conn_event ->
  raw:B.bytes ->
  record:Product.accepted_record_realization ->
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  Lemma
    (requires
      accepted_record_integrity_conditions
        representation shadow event raw record key_usage)
    (ensures
      exists context direction epoch sequence_number.
        Terms.session_context_in_profile context /\
        Invariant.aead_usage_matches key_usage direction epoch /\
        Product.accepted_record_symbolic_nonce record ==
          Terms.record_nonce_from_sequence_token sequence_number /\
        DY.event_triggered
          representation.Bridge.representation_trace
          (Invariant.sender_for_direction
            context direction).Terms.session_principal
          (Events.event_tag Events.ProtectedRecordSent)
          (Invariant.record_origin_content
            context direction epoch sequence_number
            (Product.accepted_record_symbolic_nonce record)
            record.Product.accepted_record_symbolic_plaintext
            (Terms.protected_record_additional_data
              record.Product.accepted_record_concrete_aad)
            record.Product.accepted_record_symbolic_key))
(* Decrypt the exact accepted term, then invoke successful-decryption origin. *)
let accepted_record_has_sent_origin
  representation shadow event raw record key_usage =
  accepted_record_symbolically_decrypts record;
  successful_record_decryption_has_sent_event
    representation.Bridge.representation_trace
    record.Product.accepted_record_symbolic_key
    key_usage
    (Product.accepted_record_symbolic_nonce record)
    (Product.accepted_record_protected_term record)
    (Terms.protected_record_additional_data
      record.Product.accepted_record_concrete_aad)
    record.Product.accepted_record_symbolic_plaintext

(*
 * Refine an accepted record's origin to its exact direction, epoch, and sequence.
 *
 * Requirement: accepted_record_integrity_conditions.
 * Guarantee: a ProtectedRecordSent event matching every accepted-record field,
 * including the encoded accepted sequence number and exact protected term.
 *)
val accepted_record_has_matching_sent_origin:
  representation:Bridge.representation ->
  shadow:Product.endpoint_shadow ->
  event:SM.conn_event ->
  raw:B.bytes ->
  record:Product.accepted_record_realization ->
  key_usage:DY.usage{DY.AeadKey? key_usage} ->
  Lemma
    (requires
      accepted_record_integrity_conditions
        representation shadow event raw record key_usage)
    (ensures
      exists context.
        Terms.session_context_in_profile context /\
        DY.event_triggered
          representation.Bridge.representation_trace
          (Invariant.sender_for_direction
            context
            record.Product.accepted_record_direction).Terms.session_principal
          (Events.event_tag Events.ProtectedRecordSent)
          (Invariant.record_origin_content
            context
            record.Product.accepted_record_direction
            record.Product.accepted_record_epoch
            (Terms.encode_record_sequence_number
              record.Product.accepted_record_sequence_number)
            (Product.accepted_record_symbolic_nonce record)
            record.Product.accepted_record_symbolic_plaintext
            (Terms.protected_record_additional_data
              record.Product.accepted_record_concrete_aad)
            record.Product.accepted_record_symbolic_key))
(* Use usage uniqueness and injectivity of the nonce's sequence-token encoding. *)
let accepted_record_has_matching_sent_origin
  representation shadow event raw record key_usage =
  accepted_record_has_sent_origin
    representation shadow event raw record key_usage;
  eliminate exists
    (context:Terms.session_context)
    (direction:Events.record_direction)
    (epoch:Events.record_epoch)
    (origin_sequence_number:DY.bytes).
    Terms.session_context_in_profile context /\
    Invariant.aead_usage_matches key_usage direction epoch /\
    Product.accepted_record_symbolic_nonce record ==
      Terms.record_nonce_from_sequence_token origin_sequence_number /\
    DY.event_triggered
      representation.Bridge.representation_trace
      (Invariant.sender_for_direction
        context direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (Invariant.record_origin_content
        context direction epoch origin_sequence_number
        (Product.accepted_record_symbolic_nonce record)
        record.Product.accepted_record_symbolic_plaintext
        (Terms.protected_record_additional_data
          record.Product.accepted_record_concrete_aad)
        record.Product.accepted_record_symbolic_key)
  returns exists context.
    Terms.session_context_in_profile context /\
    DY.event_triggered
      representation.Bridge.representation_trace
      (Invariant.sender_for_direction
        context
        record.Product.accepted_record_direction).Terms.session_principal
      (Events.event_tag Events.ProtectedRecordSent)
      (Invariant.record_origin_content
        context
        record.Product.accepted_record_direction
        record.Product.accepted_record_epoch
        (Terms.encode_record_sequence_number
          record.Product.accepted_record_sequence_number)
        (Product.accepted_record_symbolic_nonce record)
        record.Product.accepted_record_symbolic_plaintext
        (Terms.protected_record_additional_data
          record.Product.accepted_record_concrete_aad)
        record.Product.accepted_record_symbolic_key)
  with origin_sequence_number.
    aead_usage_identifies_direction_and_epoch
      key_usage
      direction epoch
      record.Product.accepted_record_direction
      record.Product.accepted_record_epoch;
    Product.accepted_record_symbolic_nonce_definition record;
    normalize_term_spec Terms.record_nonce;
    normalize_term_spec Terms.record_nonce_from_sequence_token

(*
 * Project first-record nonce freshness from a generated-record batch.
 *
 * Requirement: protocol_event_fresh for a nonempty ProtectedRecordsGenerated
 * batch.
 * Guarantee: the first record's key/nonce pair was unused in the prior trace.
 *)
val generated_record_nonce_was_unused:
  trace:DY.trace ->
  shadow:Product.endpoint_shadow ->
  record:Product.sent_record_realization ->
  rest:list Product.sent_record_realization ->
  Lemma
    (requires
      Product.protocol_event_fresh
        trace shadow
        (Product.ProtectedRecordsGenerated (record :: rest)))
    (ensures
      ~(Product.record_nonce_used
        trace
        record.Product.sent_record_symbolic_key
        (Product.sent_record_symbolic_nonce record)))
(* The guarantee is the head conjunct of Product.sent_record_batch_fresh. *)
let generated_record_nonce_was_unused trace shadow record rest = ()

(*
 * Expose the confidential payload structure of a sent application-data record.
 *
 * Requirement: exact sent_record_realizes for TlsApplicationData.
 * Guarantee: represented content is wrapped in application_plaintext and has
 * the honest-application-data label tied to the sending endpoint/state id.
 *)
val sent_application_record_has_secret_structure:
  representation:Bridge.representation ->
  shadow:Product.endpoint_shadow ->
  sequence_number:nat ->
  content:B.bytes ->
  raw:B.bytes ->
  record:Product.sent_record_realization ->
  Lemma
    (requires
      Product.sent_record_realizes
        representation shadow sequence_number
        (M.TlsApplicationData content) raw record)
    (ensures
      exists symbolic_content.
        Bridge.represents representation content symbolic_content /\
        record.Product.sent_record_symbolic_plaintext ==
          Terms.application_plaintext symbolic_content (B.singleton 23uy) /\
        DY.get_label
          representation.Bridge.representation_trace symbolic_content ==
          Labels.honest_application_data_label
            shadow.Product.shadow_session
            shadow.Product.shadow_session.Terms.session_state_id)
(* The result is the application-data branch of sent_record_realizes. *)
let sent_application_record_has_secret_structure
  representation shadow sequence_number content raw record = ()

(*
 * Recover the full sent-record batch from any classified protected send.
 *
 * Requirement: protocol_event_realizes, nonempty raw output, and a protected
 * sent network event.
 * Guarantee: records realize the exact batch and determine its symbolic message.
 *)
val protected_send_realization_is_complete:
  representation:Bridge.representation ->
  registry:list Bridge.trusted_server ->
  shadow:Product.endpoint_shadow ->
  event:SM.conn_event ->
  raw_sent:B.bytes ->
  raw_received:B.bytes ->
  realization:Product.protocol_event_realization ->
  Lemma
    (requires
      Product.protocol_event_realizes
        representation registry shadow event
        raw_sent raw_received realization /\
      B.length raw_sent <> 0 /\
      (match event with
       | SM.ConnNetworkEvent directed ->
         directed.CL.message_direction == CL.Sent /\
         SM.network_message_is_cleartext
           directed.CL.message_direction directed.CL.message_value == false
       | _ -> False))
    (ensures
      exists records.
        Product.sent_record_batch_realizes
          representation shadow event raw_sent records /\
        Product.protocol_event_symbolic_message
          realization
          (Product.sent_record_batch_wire_term records))
(* Case-analyze realizations; only record-producing constructors satisfy premises. *)
let protected_send_realization_is_complete
  representation registry shadow event
  raw_sent raw_received realization =
  match realization with
  | Product.ServerFinishedGenerated _ _ records -> ()
  | Product.ClientFinishedGenerated _ _ records -> ()
  | Product.ProtectedRecordsGenerated records -> ()
  | Product.NoProtocolEvent -> ()
  | Product.ServerSignatureGenerated _ _ _ _ -> ()
  | Product.ProtectedRecordAccepted _ -> ()

(*
 * Project exact concrete wire and symbolic network semantics from an honest step.
 *
 * Requirement: the specified HonestCanonical Product.product_step.
 * Guarantee: canonical_wire_step and honest_network_trace_delta both hold.
 *)
val honest_canonical_transition_uses_exact_record_semantics:
  before:Product.product_state ->
  after:Product.product_state ->
  before_shadow:Product.endpoint_shadow ->
  after_shadow:Product.endpoint_shadow ->
  event:SM.conn_event ->
  raw_sent:B.bytes ->
  raw_received:B.bytes ->
  Lemma
    (requires
      Product.product_step
        before
        (Product.HonestCanonical
          before_shadow after_shadow event raw_sent raw_received)
        after)
    (ensures
      Canonical.canonical_wire_step
        before_shadow.Product.shadow_concrete
        after_shadow.Product.shadow_concrete
        event raw_sent raw_received /\
      Product.honest_network_trace_delta
        after.Product.product_representation
        before.Product.product_registry
        before.Product.product_network
        before.Product.product_trace
        before_shadow after_shadow
        event raw_sent raw_received
        after.Product.product_network
        after.Product.product_trace)
(* Both properties are direct conjuncts of the HonestCanonical product-step case. *)
let honest_canonical_transition_uses_exact_record_semantics
  before after before_shadow after_shadow
  event raw_sent raw_received = ()

(*
 * Confidentiality theorem for a labeled honest application-data content term.
 *
 * Requirement: invariant trace, attacker knowledge, and an exact
 * honest_application_data_label for the supplied session/state id.
 * Guarantee: that supplied label is corrupt.
 *)
val honest_application_data_secrecy:
  state:Product.product_state ->
  session:Terms.endpoint_session ->
  application_state_id:DY.state_id ->
  content:DY.bytes ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows state.Product.product_trace content /\
      DY.get_label state.Product.product_trace content ==
        Labels.honest_application_data_label
          session application_state_id)
    (ensures
      DY.is_corrupt
        state.Product.product_trace
        (Labels.honest_application_data_label
          session application_state_id))
(* Reuse generic attacker-knowledge-to-label-corruption reasoning. *)
let honest_application_data_secrecy
  state session application_state_id content =
  Secrecy.attacker_knowledge_implies_label_corruption
    state content
    (Labels.honest_application_data_label
      session application_state_id)

(*
 * Confidentiality theorem for content named in a sent application record event.
 *
 * Requirement: invariant trace, exact ApplicationEpoch ProtectedRecordSent
 * event, attacker knowledge, and a caller-supplied label tie for content.
 * Guarantee: the sending endpoint/state application-data label is corrupt.
 * The event supplies record provenance; the label equality remains an explicit
 * premise rather than being inferred from the event alone.
 *)
val recorded_honest_application_data_secrecy:
  state:Product.product_state ->
  context:Terms.session_context ->
  direction:Events.record_direction ->
  sequence_number:nat ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  content:DY.bytes ->
  content_type_and_padding:B.bytes ->
  additional_data:DY.bytes ->
  application_state_id:DY.state_id ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.event_triggered
        state.Product.product_trace
        (Invariant.sender_for_direction
          context direction).Terms.session_principal
        (Events.event_tag Events.ProtectedRecordSent)
        (Invariant.record_origin_content
          context direction Events.ApplicationEpoch
          (Terms.encode_record_sequence_number sequence_number)
          nonce
          (Terms.application_plaintext content content_type_and_padding)
          additional_data
          key) /\
      DY.attacker_knows state.Product.product_trace content /\
      DY.get_label state.Product.product_trace content ==
        Labels.honest_application_data_label
          (Invariant.sender_for_direction context direction)
          application_state_id)
    (ensures
      DY.is_corrupt
        state.Product.product_trace
        (Labels.honest_application_data_label
          (Invariant.sender_for_direction context direction)
          application_state_id))
(* Instantiate honest_application_data_secrecy for the event's sender. *)
let recorded_honest_application_data_secrecy
  state context direction sequence_number
  key nonce content content_type_and_padding additional_data
  application_state_id =
  honest_application_data_secrecy
    state
    (Invariant.sender_for_direction context direction)
    application_state_id
    content
