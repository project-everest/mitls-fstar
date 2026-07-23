module TLS13.Symbolic.RecordSecurity

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

val record_nonce_changes_with_sequence:
  static_iv:DY.bytes ->
  before_sequence:nat ->
  after_sequence:nat ->
  Lemma
    (requires before_sequence =!= after_sequence)
    (ensures
      Terms.record_nonce static_iv before_sequence =!=
      Terms.record_nonce static_iv after_sequence)
let record_nonce_changes_with_sequence
  static_iv before_sequence after_sequence =
  if Terms.record_nonce static_iv before_sequence =
     Terms.record_nonce static_iv after_sequence
  then Terms.record_nonce_injective
    static_iv before_sequence after_sequence

val record_nonce_uses_execution_binding:
  static_iv:DY.bytes ->
  sequence_number:nat ->
  Lemma
    (ensures
      Bridge.requires_explicit_binding
        (Terms.record_nonce static_iv sequence_number))
let record_nonce_uses_execution_binding static_iv sequence_number = ()

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
let record_nonce_is_public trace static_iv sequence_number =
  normalize_term_spec Terms.record_nonce;
  normalize_term_spec Terms.record_nonce_from_sequence_token;
  normalize_term_spec Terms.encode_record_sequence_number;
  normalize_term_spec Terms.public_bytes;
  normalize_term_spec DY.get_label

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
let protected_record_substitution_rejected
  key nonce plaintext additional_data
  substituted_key substituted_nonce substituted_additional_data =
  Terms.protected_record_definition
    key nonce plaintext additional_data;
  normalize_term_spec DY.aead_enc;
  normalize_term_spec DY.aead_dec

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
let cross_direction_record_substitution_rejected
  direction_key other_direction_key nonce plaintext additional_data =
  protected_record_substitution_rejected
    direction_key nonce plaintext additional_data
    other_direction_key nonce additional_data

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
let cross_epoch_record_substitution_rejected
  epoch_key other_epoch_key nonce plaintext additional_data =
  protected_record_substitution_rejected
    epoch_key nonce plaintext additional_data
    other_epoch_key nonce additional_data

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
let successful_record_decryption_has_aead_origin
  trace key key_usage nonce ciphertext additional_data plaintext =
  DY.bytes_invariant_aead_dec trace key nonce ciphertext additional_data

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
let successful_record_decryption_has_sent_event
  trace key key_usage nonce ciphertext additional_data plaintext =
  successful_record_decryption_has_aead_origin
    trace key key_usage nonce ciphertext additional_data plaintext

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
let generated_record_nonce_was_unused trace shadow record rest = ()

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
let sent_application_record_has_secret_structure
  representation shadow sequence_number content raw record = ()

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
let honest_canonical_transition_uses_exact_record_semantics
  before after before_shadow after_shadow
  event raw_sent raw_received = ()

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
let honest_application_data_secrecy
  state session application_state_id content =
  Secrecy.attacker_knowledge_implies_label_corruption
    state content
    (Labels.honest_application_data_label
      session application_state_id)

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
let recorded_honest_application_data_secrecy
  state context direction sequence_number
  key nonce content content_type_and_padding additional_data
  application_state_id =
  honest_application_data_secrecy
    state
    (Invariant.sender_for_direction context direction)
    application_state_id
    content
