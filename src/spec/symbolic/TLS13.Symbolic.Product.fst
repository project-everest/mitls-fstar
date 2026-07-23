module TLS13.Symbolic.Product

module B = TLS13.Bytes
module Bridge = TLS13.Symbolic.Bridge
module Canonical = TLS13.Spec.StateMachine.Canonical
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module DY = DY.Core
module Events = TLS13.Symbolic.Events
module CSL = TLS13.ConnectionState.Lemmas
module Labels = TLS13.Symbolic.Labels
module M = TLS13.Messages
module Profile = TLS13.Symbolic.Profile
module R = TLS13.Record.Spec
module RF = TLS13.Spec.StateMachine.RecordFraming
module Reach = TLS13.Spec.StateMachine.Reachability
module Seq = FStar.Seq
module SM = TLS13.Spec.StateMachine
module Terms = TLS13.Symbolic.Terms
module Sem = TLS13.Wire.Semantics
module T = TLS13.Types
module Usages = TLS13.Symbolic.Usages
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

let option_represents
  (representation:Bridge.representation)
  (concrete:option B.bytes)
  (symbolic:option DY.bytes)
  : prop =
  match concrete, symbolic with
  | None, None -> True
  | Some concrete_value, Some symbolic_value ->
    Bridge.represents representation concrete_value symbolic_value
  | _, _ -> False

let secret_option_represents
  (representation:Bridge.representation)
  (concrete:option C.secret)
  (symbolic:option DY.bytes)
  : prop =
  match concrete, symbolic with
  | None, None -> True
  | Some concrete_value, Some symbolic_value ->
    Bridge.represents representation concrete_value symbolic_value
  | _, _ -> False

noeq
type concrete_transition = {
  concrete_before: SM.connection_state;
  concrete_after: SM.connection_state;
  concrete_event: SM.conn_event;
  concrete_raw_sent: B.bytes;
  concrete_raw_received: B.bytes;
}

let concrete_transition_is_legal
  (transition:concrete_transition)
  : prop =
  SM.legal_connection_delta
    transition.concrete_before
    {
      SM.delta_event = transition.concrete_event;
      SM.delta_raw_sent = transition.concrete_raw_sent;
      SM.delta_raw_received = transition.concrete_raw_received;
    }
    transition.concrete_after

let concrete_transition_is_canonical
  (transition:concrete_transition)
  : prop =
  Canonical.canonical_wire_step
    transition.concrete_before
    transition.concrete_after
    transition.concrete_event
    transition.concrete_raw_sent
    transition.concrete_raw_received

let rec concrete_execution
  (initial:SM.connection_state)
  (transitions:list concrete_transition)
  (final:SM.connection_state)
  : Tot prop (decreases transitions) =
  match transitions with
  | [] -> final == initial
  | transition :: rest ->
    transition.concrete_before == initial /\
    concrete_transition_is_legal transition /\
    concrete_execution transition.concrete_after rest final

let rec reverse_concrete_execution
  (final:SM.connection_state)
  (reverse_transitions:list concrete_transition)
  (initial:SM.connection_state)
  : Tot prop (decreases reverse_transitions) =
  match reverse_transitions with
  | [] -> final == initial
  | transition :: rest ->
    transition.concrete_after == final /\
    concrete_transition_is_legal transition /\
    reverse_concrete_execution
      transition.concrete_before rest initial

noeq
type symbolic_traffic_material = {
  symbolic_traffic_secret: DY.bytes;
  symbolic_traffic_key: DY.bytes;
  symbolic_traffic_iv: DY.bytes;
}

noeq
type symbolic_key_schedule = {
  symbolic_early_secret: option DY.bytes;
  symbolic_shared_secret: option DY.bytes;
  symbolic_handshake_secret: option DY.bytes;
  symbolic_master_secret: option DY.bytes;
  symbolic_client_handshake_traffic: option symbolic_traffic_material;
  symbolic_server_handshake_traffic: option symbolic_traffic_material;
  symbolic_client_application_traffic: option symbolic_traffic_material;
  symbolic_server_application_traffic: option symbolic_traffic_material;
}

noeq
type symbolic_direction_state = {
  symbolic_epoch: R.epoch;
  symbolic_key: option DY.bytes;
  symbolic_static_iv: option DY.bytes;
  symbolic_sequence_number: nat;
}

noeq
type endpoint_shadow = {
  shadow_session: Terms.endpoint_session;
  shadow_origin: SM.connection_state;
  shadow_reverse_history: list concrete_transition;
  shadow_concrete: SM.connection_state;
  shadow_context: option Terms.session_context;
  shadow_transcript: DY.bytes;
  shadow_key_schedule: symbolic_key_schedule;
  shadow_record_read: symbolic_direction_state;
  shadow_record_write: symbolic_direction_state;
  shadow_authenticated_server_key: option DY.bytes;
  shadow_certificate_verify_accepted: bool;
  shadow_server_finished_accepted: bool;
  shadow_client_finished_accepted: bool;
}

let traffic_material_represents
  (representation:Bridge.representation)
  (concrete:option SM.traffic_key_material)
  (symbolic:option symbolic_traffic_material)
  : prop =
  match concrete, symbolic with
  | None, None -> True
  | Some material, Some symbolic_material ->
    Bridge.represents
      representation
      material.SM.traffic_secret
      symbolic_material.symbolic_traffic_secret /\
    symbolic_material.symbolic_traffic_key ==
      Terms.record_key symbolic_material.symbolic_traffic_secret /\
    Bridge.represents
      representation
      material.SM.traffic_key
      symbolic_material.symbolic_traffic_key /\
    symbolic_material.symbolic_traffic_iv ==
      Terms.record_iv symbolic_material.symbolic_traffic_secret /\
    Bridge.represents
      representation
      material.SM.traffic_iv
      symbolic_material.symbolic_traffic_iv
  | _, _ -> False

let key_schedule_refines
  (representation:Bridge.representation)
  (concrete:SM.key_schedule_state)
  (symbolic:symbolic_key_schedule)
  : prop =
  secret_option_represents
    representation
    concrete.SM.ks_early_secret
    symbolic.symbolic_early_secret /\
  secret_option_represents
    representation
    concrete.SM.ks_shared_secret
    symbolic.symbolic_shared_secret /\
  secret_option_represents
    representation
    concrete.SM.ks_handshake_secret
    symbolic.symbolic_handshake_secret /\
  secret_option_represents
    representation
    concrete.SM.ks_master_secret
    symbolic.symbolic_master_secret /\
  traffic_material_represents
    representation
    concrete.SM.ks_client_handshake_traffic
    symbolic.symbolic_client_handshake_traffic /\
  traffic_material_represents
    representation
    concrete.SM.ks_server_handshake_traffic
    symbolic.symbolic_server_handshake_traffic /\
  traffic_material_represents
    representation
    concrete.SM.ks_client_application_traffic
    symbolic.symbolic_client_application_traffic /\
  traffic_material_represents
    representation
    concrete.SM.ks_server_application_traffic
    symbolic.symbolic_server_application_traffic

let direction_state_refines
  (representation:Bridge.representation)
  (concrete:R.direction_state)
  (symbolic:symbolic_direction_state)
  : prop =
  symbolic.symbolic_epoch == concrete.R.epoch /\
  option_represents representation concrete.R.key symbolic.symbolic_key /\
  option_represents
    representation concrete.R.static_iv symbolic.symbolic_static_iv /\
  symbolic.symbolic_sequence_number == concrete.R.seq

let direction_matches_material
  (direction:symbolic_direction_state)
  (material:option symbolic_traffic_material)
  : prop =
  match direction.symbolic_key, direction.symbolic_static_iv, material with
  | None, None, None -> True
  | Some key, Some iv, Some traffic ->
    key == traffic.symbolic_traffic_key /\
    iv == traffic.symbolic_traffic_iv
  | _, _, _ -> False

let expected_direction_material
  (role:Terms.symbolic_role)
  (direction:R.epoch)
  (is_read:bool)
  (schedule:symbolic_key_schedule)
  : option symbolic_traffic_material =
  match direction with
  | R.Initial -> None
  | R.Handshake ->
    (match role, is_read with
     | Terms.SymbolicClient, true ->
       schedule.symbolic_server_handshake_traffic
     | Terms.SymbolicClient, false ->
       schedule.symbolic_client_handshake_traffic
     | Terms.SymbolicServer, true ->
       schedule.symbolic_client_handshake_traffic
     | Terms.SymbolicServer, false ->
       schedule.symbolic_server_handshake_traffic)
  | R.Application ->
    (match role, is_read with
     | Terms.SymbolicClient, true ->
       schedule.symbolic_server_application_traffic
     | Terms.SymbolicClient, false ->
       schedule.symbolic_client_application_traffic
     | Terms.SymbolicServer, true ->
       schedule.symbolic_client_application_traffic
     | Terms.SymbolicServer, false ->
       schedule.symbolic_server_application_traffic)

let event_excludes_key_update (event:SM.conn_event) : prop =
  match event with
  | SM.ConnNetworkEvent directed ->
    (match directed.CL.message_value with
     | M.TlsKeyUpdate _ -> False
     | _ -> True)
  | SM.ConnLocalEvent _ -> True

let is_local_event (event:SM.conn_event) : prop =
  match event with
  | SM.ConnLocalEvent _ -> True
  | SM.ConnNetworkEvent _ -> False

let rec events_exclude_key_update
  (events:list SM.conn_event)
  : Tot prop (decreases events) =
  match events with
  | [] -> True
  | event :: rest ->
    event_excludes_key_update event /\
    events_exclude_key_update rest

let config_matches_role (shadow:endpoint_shadow) : prop =
  match shadow.shadow_session.Terms.session_role with
  | Terms.SymbolicClient ->
    Profile.client_config_in_profile
      shadow.shadow_concrete.SM.cs_model.SM.model_config
  | Terms.SymbolicServer ->
    Profile.server_config_in_profile
      shadow.shadow_concrete.SM.cs_model.SM.model_config

let context_matches_endpoint (shadow:endpoint_shadow) : prop =
  match shadow.shadow_context with
  | None -> True
  | Some context ->
    context.Terms.context_transcript == shadow.shadow_transcript /\
    (match shadow.shadow_session.Terms.session_role with
     | Terms.SymbolicClient ->
       context.Terms.context_client == shadow.shadow_session
     | Terms.SymbolicServer ->
       context.Terms.context_server == shadow.shadow_session)

let validated_leaf_key
  (peer:option X.peer_identity)
  : option B.bytes =
  match peer with
  | None -> None
  | Some identity -> Some identity.X.leaf_public_key

let endpoint_refines
  (representation:Bridge.representation)
  (shadow:endpoint_shadow)
  : prop =
  shadow.shadow_origin ==
    SM.initial shadow.shadow_origin.SM.cs_model.SM.model_config /\
  reverse_concrete_execution
    shadow.shadow_concrete
    shadow.shadow_reverse_history
    shadow.shadow_origin /\
  config_matches_role shadow /\
  Reach.connection_state_consistent shadow.shadow_concrete /\
  context_matches_endpoint shadow /\
  Bridge.transcript_represents
    representation
    shadow.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_transcript
    shadow.shadow_transcript /\
  key_schedule_refines
    representation
    shadow.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_keys
    shadow.shadow_key_schedule /\
  direction_state_refines
    representation
    shadow.shadow_concrete.SM.cs_model.SM.model_record.SM.record_read
    shadow.shadow_record_read /\
  direction_state_refines
    representation
    shadow.shadow_concrete.SM.cs_model.SM.model_record.SM.record_write
    shadow.shadow_record_write /\
  direction_matches_material
    shadow.shadow_record_read
    (expected_direction_material
      shadow.shadow_session.Terms.session_role
      shadow.shadow_record_read.symbolic_epoch
      true
      shadow.shadow_key_schedule) /\
  direction_matches_material
    shadow.shadow_record_write
    (expected_direction_material
      shadow.shadow_session.Terms.session_role
      shadow.shadow_record_write.symbolic_epoch
      false
      shadow.shadow_key_schedule) /\
  option_represents
    representation
    (validated_leaf_key
      shadow.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_validated_peer)
    shadow.shadow_authenticated_server_key /\
  shadow.shadow_certificate_verify_accepted ==
    shadow.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_certificate_verify_verified /\
  shadow.shadow_server_finished_accepted ==
    shadow.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_server_finished_verified /\
  shadow.shadow_client_finished_accepted ==
    ((shadow.shadow_session.Terms.session_role = Terms.SymbolicServer) &&
     (shadow.shadow_concrete.SM.cs_model.SM.model_control =
       SM.ControlApplicationData)) /\
  events_exclude_key_update shadow.shadow_concrete.SM.cs_event_log /\
  shadow.shadow_concrete.SM.cs_model.SM.model_application.SM.app_key_update_response_pending ==
    false

let encode_optional_symbolic (value:option DY.bytes) : DY.bytes =
  match value with
  | None -> Terms.public_bytes (B.singleton 0uy)
  | Some symbolic ->
    DY.Concat (Terms.public_bytes (B.singleton 1uy)) symbolic

let encode_optional_traffic
  (value:option symbolic_traffic_material)
  : DY.bytes =
  match value with
  | None -> Terms.public_bytes (B.singleton 0uy)
  | Some material ->
    DY.Concat
      (Terms.public_bytes (B.singleton 1uy))
      (DY.Concat
        material.symbolic_traffic_secret
        (DY.Concat
          material.symbolic_traffic_key
          material.symbolic_traffic_iv))

let encode_key_schedule (schedule:symbolic_key_schedule) : DY.bytes =
  DY.Concat
    (encode_optional_symbolic schedule.symbolic_early_secret)
    (DY.Concat
      (encode_optional_symbolic schedule.symbolic_shared_secret)
      (DY.Concat
        (encode_optional_symbolic schedule.symbolic_handshake_secret)
        (DY.Concat
          (encode_optional_symbolic schedule.symbolic_master_secret)
          (DY.Concat
            (encode_optional_traffic
              schedule.symbolic_client_handshake_traffic)
            (DY.Concat
              (encode_optional_traffic
                schedule.symbolic_server_handshake_traffic)
              (DY.Concat
                (encode_optional_traffic
                  schedule.symbolic_client_application_traffic)
                (encode_optional_traffic
                  schedule.symbolic_server_application_traffic)))))))

let encode_direction_state
  (direction:symbolic_direction_state)
  : DY.bytes =
  DY.Concat
    (encode_optional_symbolic direction.symbolic_key)
    (encode_optional_symbolic direction.symbolic_static_iv)

let endpoint_state_content (shadow:endpoint_shadow) : DY.bytes =
  DY.Concat
    (Terms.encode_endpoint_session shadow.shadow_session)
    (DY.Concat
      shadow.shadow_transcript
      (DY.Concat
        (encode_key_schedule shadow.shadow_key_schedule)
        (DY.Concat
          (encode_direction_state shadow.shadow_record_read)
          (DY.Concat
            (encode_direction_state shadow.shadow_record_write)
            (encode_optional_symbolic
              shadow.shadow_authenticated_server_key)))))

let endpoint_state_entry (shadow:endpoint_shadow) : DY.trace_entry =
  DY.SetState
    shadow.shadow_session.Terms.session_principal
    shadow.shadow_session.Terms.session_state_id
    (endpoint_state_content shadow)

noeq
type network_packet = {
  packet_raw: B.bytes;
  packet_symbolic: DY.bytes;
}

noeq
type product_state = {
  product_trace: DY.trace;
  product_representation: Bridge.representation;
  product_endpoints: list endpoint_shadow;
  product_network: list network_packet;
  product_registry: list Bridge.trusted_server;
}

let rec endpoint_member
  (shadow:endpoint_shadow)
  (endpoints:list endpoint_shadow)
  : Tot prop (decreases endpoints) =
  match endpoints with
  | [] -> False
  | head :: tail -> head == shadow \/ endpoint_member shadow tail

let rec endpoints_refine
  (representation:Bridge.representation)
  (endpoints:list endpoint_shadow)
  : Tot prop (decreases endpoints) =
  match endpoints with
  | [] -> True
  | head :: tail ->
    endpoint_refines representation head /\
    endpoints_refine representation tail

let same_session
  (left right:Terms.endpoint_session)
  : prop =
  left.Terms.session_principal == right.Terms.session_principal /\
  left.Terms.session_state_id == right.Terms.session_state_id

let rec session_absent
  (session:Terms.endpoint_session)
  (endpoints:list endpoint_shadow)
  : Tot prop (decreases endpoints) =
  match endpoints with
  | [] -> True
  | head :: tail ->
    ~(same_session session head.shadow_session) /\
    session_absent session tail

let rec sessions_unique
  (endpoints:list endpoint_shadow)
  : Tot prop (decreases endpoints) =
  match endpoints with
  | [] -> True
  | head :: tail ->
    session_absent head.shadow_session tail /\
    sessions_unique tail

let trace_entry_unique
  (tr:DY.trace)
  (entry:DY.trace_entry)
  : prop =
  forall left right.
    DY.entry_at tr left entry /\
    DY.entry_at tr right entry
    ==> left == right

let security_events_unique (tr:DY.trace) : prop =
  forall principal content.
    trace_entry_unique
      tr
      (DY.Event principal
        (Events.event_tag Events.ServerCertificateVerifySigned)
        content) /\
    trace_entry_unique
      tr
      (DY.Event principal
        (Events.event_tag Events.ServerFinishedSent)
        content) /\
    trace_entry_unique
      tr
      (DY.Event principal
        (Events.event_tag Events.ClientFinishedSent)
        content)

val entry_at_snoc_cases:
  tr:DY.trace ->
  last:DY.trace_entry ->
  time:DY.timestamp ->
  entry:DY.trace_entry ->
  Lemma
    (requires DY.entry_at (DY.Snoc tr last) time entry)
    (ensures
      (time == DY.trace_length tr /\ entry == last) \/
      (time < DY.trace_length tr /\ DY.entry_at tr time entry))
let entry_at_snoc_cases tr last time entry =
  norm_spec
    [delta_only
      [`%DY.entry_at;
       `%DY.on_trace;
       `%DY.trace_length;
       `%DY.get_entry_at;
       `%DY.last_timestamp;
       `%DY.last;
       `%DY.init];
     iota]
    (DY.entry_at (DY.Snoc tr last) time entry)

val trace_entry_unique_snoc:
  tr:DY.trace ->
  last:DY.trace_entry ->
  entry:DY.trace_entry ->
  Lemma
    (requires
      trace_entry_unique tr entry /\
      (~(last == entry) \/ ~(DY.entry_exists tr entry)))
    (ensures trace_entry_unique (DY.Snoc tr last) entry)

val entry_at_implies_exists:
  tr:DY.trace ->
  time:DY.timestamp ->
  entry:DY.trace_entry ->
  Lemma
    (requires DY.entry_at tr time entry)
    (ensures DY.entry_exists tr entry)
let entry_at_implies_exists tr time entry =
  introduce exists witness. DY.entry_at tr witness entry
  with time and ()

val trace_entry_unique_at:
  tr:DY.trace ->
  entry:DY.trace_entry ->
  left:DY.timestamp ->
  right:DY.timestamp ->
  Lemma
    (requires
      trace_entry_unique tr entry /\
      DY.entry_at tr left entry /\
      DY.entry_at tr right entry)
    (ensures left == right)
let trace_entry_unique_at tr entry left right =
  normalize_term_spec trace_entry_unique

val fresh_entry_not_old:
  tr:DY.trace ->
  entry:DY.trace_entry ->
  time:DY.timestamp ->
  Lemma
    (requires
      ~(DY.entry_exists tr entry) /\
      DY.entry_at tr time entry)
    (ensures False)
let fresh_entry_not_old tr entry time =
  entry_at_implies_exists tr time entry

let trace_entry_unique_snoc tr last entry =
  introduce forall left right.
    DY.entry_at (DY.Snoc tr last) left entry /\
    DY.entry_at (DY.Snoc tr last) right entry
    ==> left == right
  with (
    introduce _ ==> _ with _. (
      entry_at_snoc_cases tr last left entry;
      entry_at_snoc_cases tr last right entry;
      if left = DY.trace_length tr
      then
        if right = DY.trace_length tr
        then ()
        else begin
          assert (entry == last);
          assert (last == entry);
          assert (~(DY.entry_exists tr entry));
          assert (DY.entry_at tr right entry);
          fresh_entry_not_old tr entry right
        end
      else if right = DY.trace_length tr
      then begin
        assert (entry == last);
        assert (last == entry);
        assert (~(DY.entry_exists tr entry));
        assert (DY.entry_at tr left entry);
        fresh_entry_not_old tr entry left
      end
      else begin
        assert (DY.entry_at tr left entry);
        assert (DY.entry_at tr right entry);
        trace_entry_unique_at tr entry left right
      end))

let is_security_event_entry (entry:DY.trace_entry) : prop =
  match entry with
  | DY.Event _ tag _ ->
    tag == Events.event_tag Events.ServerCertificateVerifySigned \/
    tag == Events.event_tag Events.ServerFinishedSent \/
    tag == Events.event_tag Events.ClientFinishedSent
  | _ -> False

val security_target_unique_snoc:
  tr:DY.trace ->
  last:DY.trace_entry ->
  target:DY.trace_entry{is_security_event_entry target} ->
  Lemma
    (requires
      trace_entry_unique tr target /\
      (is_security_event_entry last ==> ~(DY.entry_exists tr last)))
    (ensures trace_entry_unique (DY.Snoc tr last) target)
let security_target_unique_snoc tr last target =
  assert (~(last == target) \/ ~(DY.entry_exists tr target));
  trace_entry_unique_snoc tr last target

val security_events_unique_snoc:
  tr:DY.trace ->
  last:DY.trace_entry ->
  Lemma
    (requires
      security_events_unique tr /\
      (is_security_event_entry last ==> ~(DY.entry_exists tr last)))
    (ensures security_events_unique (DY.Snoc tr last))
let security_events_unique_snoc tr last =
  introduce forall principal content.
    trace_entry_unique
      (DY.Snoc tr last)
      (DY.Event principal
        (Events.event_tag Events.ServerCertificateVerifySigned)
        content) /\
    trace_entry_unique
      (DY.Snoc tr last)
      (DY.Event principal
        (Events.event_tag Events.ServerFinishedSent)
        content) /\
    trace_entry_unique
      (DY.Snoc tr last)
      (DY.Event principal
        (Events.event_tag Events.ClientFinishedSent)
        content)
  with (
    security_target_unique_snoc
      tr last
      (DY.Event principal
        (Events.event_tag Events.ServerCertificateVerifySigned)
        content);
    security_target_unique_snoc
      tr last
      (DY.Event principal
        (Events.event_tag Events.ServerFinishedSent)
        content);
    security_target_unique_snoc
      tr last
      (DY.Event principal
        (Events.event_tag Events.ClientFinishedSent)
        content))

let product_well_formed (state:product_state) : prop =
  state.product_representation.Bridge.representation_trace ==
    state.product_trace /\
  endpoints_refine
    state.product_representation
    state.product_endpoints /\
  sessions_unique state.product_endpoints

let security_origin_free (tr:DY.trace) : prop =
  forall principal content.
    ~(DY.event_triggered
        tr principal
        (Events.event_tag Events.ServerCertificateVerifySigned)
        content) /\
    ~(DY.event_triggered
        tr principal
        (Events.event_tag Events.ServerFinishedSent)
        content) /\
    ~(DY.event_triggered
        tr principal
        (Events.event_tag Events.ClientFinishedSent)
        content) /\
    ~(DY.event_triggered
        tr principal
        (Events.event_tag Events.ProtectedRecordSent)
        content)

let initial_product_state (state:product_state) : prop =
  product_well_formed state /\
  security_origin_free state.product_trace

let rec replace_endpoint
  (before_shadow after_shadow:endpoint_shadow)
  (before_endpoints after_endpoints:list endpoint_shadow)
  : Tot prop (decreases before_endpoints) =
  match before_endpoints with
  | [] -> False
  | head :: tail ->
    (head == before_shadow /\
     after_endpoints == after_shadow :: tail) \/
    (exists after_tail.
      after_endpoints == head :: after_tail /\
      replace_endpoint
        before_shadow after_shadow tail after_tail)

let rec packet_member
  (packet:network_packet)
  (packets:list network_packet)
  : Tot prop (decreases packets) =
  match packets with
  | [] -> False
  | head :: tail -> head == packet \/ packet_member packet tail

let rec remove_packet
  (packet:network_packet)
  (before after:list network_packet)
  : Tot prop (decreases before) =
  match before with
  | [] -> False
  | head :: tail ->
    (head == packet /\ after == tail) \/
    (exists after_tail.
      after == head :: after_tail /\
      remove_packet packet tail after_tail)

noeq
type sent_record_realization = {
  sent_record_context: Terms.session_context;
  sent_record_direction: Events.record_direction;
  sent_record_epoch: Events.record_epoch;
  sent_record_sequence_number: nat;
  sent_record_concrete_key: C.aead_key;
  sent_record_concrete_static_iv: C.aead_nonce;
  sent_record_concrete_aad: B.bytes;
  sent_record_concrete_plaintext: B.bytes;
  sent_record_symbolic_key: DY.bytes;
  sent_record_symbolic_static_iv: DY.bytes;
  sent_record_symbolic_plaintext: DY.bytes;
}

noeq
type accepted_record_realization = {
  accepted_record_context: Terms.session_context;
  accepted_record_direction: Events.record_direction;
  accepted_record_epoch: Events.record_epoch;
  accepted_record_sequence_number: nat;
  accepted_record_concrete_key: C.aead_key;
  accepted_record_concrete_static_iv: C.aead_nonce;
  accepted_record_concrete_aad: B.bytes;
  accepted_record_concrete_ciphertext: B.bytes;
  accepted_record_concrete_plaintext:
    (plaintext:B.bytes{
      B.length plaintext + 16 ==
      B.length accepted_record_concrete_ciphertext
    });
  accepted_record_symbolic_key: DY.bytes;
  accepted_record_symbolic_static_iv: DY.bytes;
  accepted_record_symbolic_plaintext: DY.bytes;
}

let sent_record_symbolic_nonce
  (record:sent_record_realization)
  : DY.bytes =
  Terms.record_nonce
    record.sent_record_symbolic_static_iv
    record.sent_record_sequence_number

let sent_record_protected_term
  (record:sent_record_realization)
  : DY.bytes =
  Terms.protected_record
    record.sent_record_symbolic_key
    (sent_record_symbolic_nonce record)
    record.sent_record_symbolic_plaintext
    (Terms.protected_record_additional_data
      record.sent_record_concrete_aad)

let sent_record_wire_term
  (record:sent_record_realization)
  : DY.bytes =
  DY.Concat
    (Terms.protected_record_additional_data
      record.sent_record_concrete_aad)
    (sent_record_protected_term record)

let accepted_record_symbolic_nonce
  (record:accepted_record_realization)
  : DY.bytes =
  Terms.record_nonce
    record.accepted_record_symbolic_static_iv
    record.accepted_record_sequence_number

val accepted_record_symbolic_nonce_definition:
  record:accepted_record_realization ->
  Lemma
    (ensures
      accepted_record_symbolic_nonce record ==
      Terms.record_nonce_from_sequence_token
        (Terms.encode_record_sequence_number
          record.accepted_record_sequence_number))
let accepted_record_symbolic_nonce_definition record = ()

let accepted_record_protected_term
  (record:accepted_record_realization)
  : DY.bytes =
  Terms.protected_record
    record.accepted_record_symbolic_key
    (accepted_record_symbolic_nonce record)
    record.accepted_record_symbolic_plaintext
    (Terms.protected_record_additional_data
      record.accepted_record_concrete_aad)

val accepted_record_protected_term_definition:
  record:accepted_record_realization ->
  Lemma
    (ensures
      accepted_record_protected_term record ==
      Terms.protected_record
        record.accepted_record_symbolic_key
        (accepted_record_symbolic_nonce record)
        record.accepted_record_symbolic_plaintext
        (Terms.protected_record_additional_data
          record.accepted_record_concrete_aad))
let accepted_record_protected_term_definition record = ()

let accepted_record_wire_term
  (record:accepted_record_realization)
  : DY.bytes =
  DY.Concat
    (Terms.protected_record_additional_data
      record.accepted_record_concrete_aad)
    (accepted_record_protected_term record)

let rec sent_record_batch_wire_term
  (records:list sent_record_realization)
  : Tot DY.bytes (decreases records) =
  match records with
  | [] -> Terms.public_bytes B.empty
  | [record] -> sent_record_wire_term record
  | record :: rest ->
    DY.Concat
      (sent_record_wire_term record)
      (sent_record_batch_wire_term rest)

let record_direction_for_sender
  (role:Terms.symbolic_role)
  : Events.record_direction =
  match role with
  | Terms.SymbolicClient -> Events.ClientToServer
  | Terms.SymbolicServer -> Events.ServerToClient

let record_direction_for_receiver
  (role:Terms.symbolic_role)
  : Events.record_direction =
  match role with
  | Terms.SymbolicClient -> Events.ServerToClient
  | Terms.SymbolicServer -> Events.ClientToServer

let record_epoch_matches
  (symbolic:Events.record_epoch)
  (concrete:R.epoch)
  : prop =
  match symbolic, concrete with
  | Events.HandshakeEpoch, R.Handshake -> True
  | Events.ApplicationEpoch, R.Application -> True
  | _, _ -> False

let sent_symbolic_plaintext_realizes_message
  (representation:Bridge.representation)
  (shadow:endpoint_shadow)
  (message:M.tls_message)
  (record:sent_record_realization)
  : prop =
  match message with
  | M.TlsApplicationData content ->
    exists symbolic_content.
      Bridge.represents representation content symbolic_content /\
      record.sent_record_symbolic_plaintext ==
        Terms.application_plaintext symbolic_content (B.singleton 23uy) /\
      DY.get_label
        #Usages.tls_crypto_usages
        representation.Bridge.representation_trace
        symbolic_content ==
        Labels.honest_application_data_label
          shadow.shadow_session
          shadow.shadow_session.Terms.session_state_id
  | _ -> True

let accepted_symbolic_plaintext_realizes_message
  (representation:Bridge.representation)
  (message:M.tls_message)
  (record:accepted_record_realization)
  : prop =
  match message with
  | M.TlsApplicationData content ->
    exists symbolic_content.
      Bridge.represents representation content symbolic_content /\
      record.accepted_record_symbolic_plaintext ==
        Terms.application_plaintext symbolic_content (B.singleton 23uy)
  | _ -> True

let sent_record_realizes
  (representation:Bridge.representation)
  (shadow:endpoint_shadow)
  (expected_sequence_number:nat)
  (expected_message:M.tls_message)
  (raw:B.bytes)
  (record:sent_record_realization)
  : prop =
  Some? shadow.shadow_context /\
  (match shadow.shadow_context with
   | Some context -> record.sent_record_context == context
   | None -> False) /\
  Terms.session_context_in_profile record.sent_record_context /\
  record.sent_record_direction ==
    record_direction_for_sender shadow.shadow_session.Terms.session_role /\
  record_epoch_matches
    record.sent_record_epoch shadow.shadow_record_write.symbolic_epoch /\
  record.sent_record_sequence_number == expected_sequence_number /\
  Seq.equal
    record.sent_record_concrete_plaintext
    (Canonical.sent_tls_inner_plaintext_fragment expected_message) /\
  sent_symbolic_plaintext_realizes_message
    representation shadow expected_message record /\
  Seq.equal
    record.sent_record_concrete_aad
    (Canonical.record_header_aad raw) /\
  (match
     shadow.shadow_concrete.SM.cs_model.SM.model_record.SM.record_write.R.key,
     shadow.shadow_concrete.SM.cs_model.SM.model_record.SM.record_write.R.static_iv,
     shadow.shadow_record_write.symbolic_key,
     shadow.shadow_record_write.symbolic_static_iv
   with
   | Some concrete_key, Some concrete_iv,
     Some symbolic_key, Some symbolic_iv ->
     Seq.equal concrete_key record.sent_record_concrete_key /\
     Seq.equal concrete_iv record.sent_record_concrete_static_iv /\
     symbolic_key == record.sent_record_symbolic_key /\
     symbolic_iv == record.sent_record_symbolic_static_iv
   | _, _, _, _ -> False) /\
  W.parse_record raw ==
    Some
      (T.Application_data,
       C.chacha20_poly1305_seal
         record.sent_record_concrete_key
         (C.tls13_record_nonce
           record.sent_record_concrete_static_iv
           record.sent_record_sequence_number)
         record.sent_record_concrete_aad
         record.sent_record_concrete_plaintext,
       B.length raw) /\
  Bridge.aead_seal_bridge
    representation
    record.sent_record_concrete_key
    record.sent_record_symbolic_key
    (C.tls13_record_nonce
      record.sent_record_concrete_static_iv
      record.sent_record_sequence_number)
    (sent_record_symbolic_nonce record)
    record.sent_record_concrete_aad
    record.sent_record_concrete_plaintext
    (Terms.protected_record_additional_data
      record.sent_record_concrete_aad)
    record.sent_record_symbolic_plaintext

let rec sent_application_record_contents_realize
  (representation:Bridge.representation)
  (shadow:endpoint_shadow)
  (sequence_number:nat)
  (bytes:B.bytes)
  (raw:B.bytes)
  (records:list sent_record_realization)
  : Tot prop (decreases B.length bytes) =
  if B.length bytes <= RF.max_application_data_fragment_len
  then
    match records with
    | [record] ->
      sent_record_realizes
        representation shadow sequence_number
        (M.TlsApplicationData bytes) raw record
    | _ -> False
  else
    let head =
      Seq.slice bytes 0 RF.max_application_data_fragment_len in
    let tail =
      Seq.slice
        bytes
        RF.max_application_data_fragment_len
        (B.length bytes) in
    match records with
    | record :: rest ->
      exists raw_head raw_tail.
        Seq.equal raw (B.append raw_head raw_tail) /\
        sent_record_realizes
          representation shadow sequence_number
          (M.TlsApplicationData head) raw_head record /\
        sent_application_record_contents_realize
          representation shadow (sequence_number + 1)
          tail raw_tail rest
    | [] -> False

let sent_record_batch_realizes
  (representation:Bridge.representation)
  (shadow:endpoint_shadow)
  (event:SM.conn_event)
  (raw:B.bytes)
  (records:list sent_record_realization)
  : prop =
  match event with
  | SM.ConnNetworkEvent directed ->
    directed.CL.message_direction == CL.Sent /\
    SM.network_message_is_cleartext
      directed.CL.message_direction directed.CL.message_value == false /\
    (match directed.CL.message_value with
     | M.TlsApplicationData bytes ->
       sent_application_record_contents_realize
         representation shadow
         shadow.shadow_record_write.symbolic_sequence_number
         bytes raw records
     | protected_message ->
       (match records with
        | [record] ->
          sent_record_realizes
            representation shadow
            shadow.shadow_record_write.symbolic_sequence_number
            protected_message raw record
        | _ -> False)) /\
    Bridge.represents
      representation raw (sent_record_batch_wire_term records)
  | _ -> False

let accepted_record_realizes
  (representation:Bridge.representation)
  (shadow:endpoint_shadow)
  (event:SM.conn_event)
  (raw:B.bytes)
  (record:accepted_record_realization)
  : prop =
  Some? shadow.shadow_context /\
  (match shadow.shadow_context with
   | Some context -> record.accepted_record_context == context
   | None -> False) /\
  Terms.session_context_in_profile record.accepted_record_context /\
  record.accepted_record_direction ==
    record_direction_for_receiver shadow.shadow_session.Terms.session_role /\
  record_epoch_matches
    record.accepted_record_epoch shadow.shadow_record_read.symbolic_epoch /\
  record.accepted_record_sequence_number ==
    shadow.shadow_record_read.symbolic_sequence_number /\
  Seq.equal
    record.accepted_record_concrete_aad
    (Canonical.record_header_aad raw) /\
  (match
     shadow.shadow_concrete.SM.cs_model.SM.model_record.SM.record_read.R.key,
     shadow.shadow_concrete.SM.cs_model.SM.model_record.SM.record_read.R.static_iv,
     shadow.shadow_record_read.symbolic_key,
     shadow.shadow_record_read.symbolic_static_iv
   with
   | Some concrete_key, Some concrete_iv,
     Some symbolic_key, Some symbolic_iv ->
     Seq.equal concrete_key record.accepted_record_concrete_key /\
     Seq.equal concrete_iv record.accepted_record_concrete_static_iv /\
     symbolic_key == record.accepted_record_symbolic_key /\
     symbolic_iv == record.accepted_record_symbolic_static_iv
   | _, _, _, _ -> False) /\
  W.parse_record_wire raw ==
    Some
      (T.Application_data,
       record.accepted_record_concrete_ciphertext,
       B.length raw) /\
  (match event with
   | SM.ConnNetworkEvent directed ->
     directed.CL.message_direction == CL.Received /\
     SM.network_message_is_cleartext
       directed.CL.message_direction directed.CL.message_value == false /\
     exists plaintext.
       W.parse_plaintext record.accepted_record_concrete_plaintext ==
         Some plaintext /\
       W.parse_tls_message
         plaintext.M.content_type plaintext.M.fragment ==
         Some directed.CL.message_value /\
       accepted_symbolic_plaintext_realizes_message
         representation directed.CL.message_value record
   | _ -> False) /\
  Bridge.aead_open_bridge
    representation
    record.accepted_record_concrete_key
    record.accepted_record_symbolic_key
    (C.tls13_record_nonce
      record.accepted_record_concrete_static_iv
      record.accepted_record_sequence_number)
    (accepted_record_symbolic_nonce record)
    record.accepted_record_concrete_aad
    record.accepted_record_concrete_ciphertext
    record.accepted_record_concrete_plaintext
    (Terms.protected_record_additional_data
      record.accepted_record_concrete_aad)
    record.accepted_record_symbolic_plaintext /\
  Bridge.represents
    representation raw (accepted_record_wire_term record)

noeq
type protocol_event_realization =
  | NoProtocolEvent
  | ServerSignatureGenerated:
      context:Terms.session_context ->
      verification_key:DY.bytes ->
      signing_key:DY.bytes ->
      signing_nonce:DY.bytes ->
      protocol_event_realization
  | ServerFinishedGenerated:
      context:Terms.session_context ->
      finished_key:DY.bytes ->
      records:list sent_record_realization ->
      protocol_event_realization
  | ClientFinishedGenerated:
      context:Terms.session_context ->
      finished_key:DY.bytes ->
      records:list sent_record_realization ->
      protocol_event_realization
  | ProtectedRecordsGenerated:
      records:list sent_record_realization ->
      protocol_event_realization
  | ProtectedRecordAccepted:
      record:accepted_record_realization ->
      protocol_event_realization

let protocol_origin_event (event:SM.conn_event) : bool =
  match event with
  | SM.ConnLocalEvent (SM.LocalSignCertificateVerify _) -> true
  | SM.ConnNetworkEvent directed ->
    (match directed.CL.message_direction, directed.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.Finished _) -> true
     | _, message ->
       not (SM.network_message_is_cleartext
         directed.CL.message_direction message))
  | _ -> false

let record_only_origin_event (event:SM.conn_event) : bool =
  match event with
  | SM.ConnNetworkEvent directed ->
    (match directed.CL.message_direction, directed.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.Finished _) -> false
     | CL.Sent, message ->
       not (SM.network_message_is_cleartext CL.Sent message)
     | _, _ -> false)
  | _ -> false

let protocol_event_entry
  (shadow:endpoint_shadow)
  (realization:protocol_event_realization)
  : option DY.trace_entry =
  match realization with
  | NoProtocolEvent -> None
  | ServerSignatureGenerated context verification_key _ _ ->
    Some
      (Events.handshake_event_entry
        shadow.shadow_session.Terms.session_principal
        Events.ServerCertificateVerifySigned
        context
        (DY.Concat
          verification_key
          (Terms.certificate_verify_input
            context.Terms.context_transcript)))
  | ServerFinishedGenerated context finished_key _ ->
    Some
      (Events.handshake_event_entry
        shadow.shadow_session.Terms.session_principal
        Events.ServerFinishedSent
        context
        (DY.Concat
          finished_key
          (Terms.transcript_hash context.Terms.context_transcript)))
  | ClientFinishedGenerated context finished_key _ ->
    Some
      (Events.handshake_event_entry
        shadow.shadow_session.Terms.session_principal
        Events.ClientFinishedSent
        context
        (DY.Concat
          finished_key
          (Terms.transcript_hash context.Terms.context_transcript)))
  | ProtectedRecordsGenerated _
  | ProtectedRecordAccepted _ ->
    None

let sent_record_event_entry
  (record:sent_record_realization)
  : DY.trace_entry =
  Events.record_event_entry
    (match record.sent_record_direction with
     | Events.ClientToServer ->
       record.sent_record_context.Terms.context_client.Terms.session_principal
     | Events.ServerToClient ->
       record.sent_record_context.Terms.context_server.Terms.session_principal)
    Events.ProtectedRecordSent
    record.sent_record_context
    record.sent_record_direction
    record.sent_record_epoch
    (Terms.encode_record_sequence_number
      record.sent_record_sequence_number)
    record.sent_record_symbolic_plaintext
    (sent_record_protected_term record)

let accepted_record_event_entry
  (shadow:endpoint_shadow)
  (record:accepted_record_realization)
  : DY.trace_entry =
  Events.record_event_entry
    shadow.shadow_session.Terms.session_principal
    Events.ProtectedRecordAccepted
    record.accepted_record_context
    record.accepted_record_direction
    record.accepted_record_epoch
    (Terms.encode_record_sequence_number
      record.accepted_record_sequence_number)
    record.accepted_record_symbolic_plaintext
    (accepted_record_protected_term record)

let rec sent_record_event_trace
  (before:DY.trace)
  (records:list sent_record_realization)
  : Tot DY.trace (decreases records) =
  match records with
  | [] -> before
  | record :: rest ->
    sent_record_event_trace
      (DY.Snoc before (sent_record_event_entry record))
      rest

let record_nonce_used
  (trace:DY.trace)
  (key nonce:DY.bytes)
  : prop =
  exists principal context direction epoch sequence_number plaintext additional_data.
    DY.event_triggered
      trace principal
      (Events.event_tag Events.ProtectedRecordSent)
      (Events.record_event_content
        context direction epoch sequence_number plaintext
        (Terms.protected_record key nonce plaintext additional_data))

let rec sent_record_batch_fresh
  (before:DY.trace)
  (records:list sent_record_realization)
  : Tot prop (decreases records) =
  match records with
  | [] -> True
  | record :: rest ->
    ~(record_nonce_used
        before
        record.sent_record_symbolic_key
        (sent_record_symbolic_nonce record)) /\
    sent_record_batch_fresh
      (DY.Snoc before (sent_record_event_entry record))
      rest

let protocol_event_realizes
  (representation:Bridge.representation)
  (registry:list Bridge.trusted_server)
  (shadow:endpoint_shadow)
  (event:SM.conn_event)
  (raw_sent raw_received:B.bytes)
  (realization:protocol_event_realization)
  : prop =
  match event, realization with
  | SM.ConnLocalEvent (SM.LocalSignCertificateVerify cv),
    ServerSignatureGenerated context verification_key signing_key signing_nonce ->
    shadow.shadow_session.Terms.session_role == Terms.SymbolicServer /\
    shadow.shadow_context == Some context /\
    Terms.session_context_in_profile context /\
    context.Terms.context_server == shadow.shadow_session /\
    (exists server selection.
      Bridge.registered_server registry server /\
      server.Bridge.trusted_server_principal ==
        shadow.shadow_session.Terms.session_principal /\
      server.Bridge.trusted_server_symbolic_key == verification_key /\
      shadow.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_server_selection ==
        Some selection /\
      selection.SM.server_selected_credential ==
        server.Bridge.trusted_server_verification_key /\
      Bridge.represents
        representation
        selection.SM.server_selected_credential
        (Terms.verification_key signing_key)) /\
    Bridge.represents
      representation
      (Sem.certificateVerify_signature_bytes cv)
      (Terms.certificate_verify
        signing_key signing_nonce context.Terms.context_transcript)
  | SM.ConnNetworkEvent directed,
    ServerFinishedGenerated context finished_key records ->
    shadow.shadow_session.Terms.session_role == Terms.SymbolicServer /\
    shadow.shadow_context == Some context /\
    Terms.session_context_in_profile context /\
    context.Terms.context_server == shadow.shadow_session /\
    (match
       directed.CL.message_direction,
       directed.CL.message_value,
       shadow.shadow_key_schedule.symbolic_server_handshake_traffic
     with
     | CL.Sent, M.TlsHandshake (M.Finished fin), Some traffic ->
       finished_key == Terms.finished_key traffic.symbolic_traffic_secret /\
       Bridge.represents
         representation
         (Sem.finished_verify_data fin)
         (Terms.finished_verify_data
           traffic.symbolic_traffic_secret
           context.Terms.context_transcript)
     | _, _, _ -> False) /\
    B.length raw_sent <> 0 /\
    B.length raw_received == 0 /\
    sent_record_batch_realizes
      representation shadow event raw_sent records
  | SM.ConnNetworkEvent directed,
    ClientFinishedGenerated context finished_key records ->
    shadow.shadow_session.Terms.session_role == Terms.SymbolicClient /\
    shadow.shadow_context == Some context /\
    Terms.session_context_in_profile context /\
    context.Terms.context_client == shadow.shadow_session /\
    (match
       directed.CL.message_direction,
       directed.CL.message_value,
       shadow.shadow_key_schedule.symbolic_client_handshake_traffic
     with
     | CL.Sent, M.TlsHandshake (M.Finished fin), Some traffic ->
       finished_key == Terms.finished_key traffic.symbolic_traffic_secret /\
       Bridge.represents
         representation
         (Sem.finished_verify_data fin)
         (Terms.finished_verify_data
           traffic.symbolic_traffic_secret
           context.Terms.context_transcript)
     | _, _, _ -> False) /\
    B.length raw_sent <> 0 /\
    B.length raw_received == 0 /\
    sent_record_batch_realizes
      representation shadow event raw_sent records
  | _,
    ProtectedRecordsGenerated records ->
    record_only_origin_event event /\
    B.length raw_sent <> 0 /\
    B.length raw_received == 0 /\
    sent_record_batch_realizes
      representation shadow event raw_sent records
  | _,
    ProtectedRecordAccepted record ->
    B.length raw_sent == 0 /\
    B.length raw_received <> 0 /\
    accepted_record_realizes
      representation shadow event raw_received record
  | _, NoProtocolEvent -> protocol_origin_event event == false
  | _, _ -> False

let protocol_event_symbolic_message
  (realization:protocol_event_realization)
  (symbolic:DY.bytes)
  : prop =
  match realization with
  | ServerFinishedGenerated _ _ records
  | ClientFinishedGenerated _ _ records
  | ProtectedRecordsGenerated records ->
    symbolic == sent_record_batch_wire_term records
  | _ -> True

let protocol_event_trace
  (before:DY.trace)
  (shadow:endpoint_shadow)
  (realization:protocol_event_realization)
  : DY.trace =
  match realization with
  | ServerFinishedGenerated _ _ records
  | ClientFinishedGenerated _ _ records ->
    (match protocol_event_entry shadow realization with
     | None -> before
     | Some entry ->
       sent_record_event_trace (DY.Snoc before entry) records)
  | ProtectedRecordsGenerated records ->
    sent_record_event_trace before records
  | ProtectedRecordAccepted record ->
    DY.Snoc before (accepted_record_event_entry shadow record)
  | _ ->
    (match protocol_event_entry shadow realization with
     | None -> before
     | Some entry -> DY.Snoc before entry)

let protocol_event_fresh
  (before:DY.trace)
  (shadow:endpoint_shadow)
  (realization:protocol_event_realization)
  : prop =
  match realization with
  | ServerFinishedGenerated _ _ records
  | ClientFinishedGenerated _ _ records ->
    (match protocol_event_entry shadow realization with
     | None -> False
     | Some entry ->
       ~(DY.entry_exists before entry) /\
       sent_record_batch_fresh (DY.Snoc before entry) records)
  | ProtectedRecordsGenerated records ->
    sent_record_batch_fresh before records
  | ProtectedRecordAccepted _ ->
    True
  | _ ->
    (match protocol_event_entry shadow realization with
     | None -> True
     | Some entry -> ~(DY.entry_exists before entry))

let honest_network_trace_delta
  (representation:Bridge.representation)
  (registry:list Bridge.trusted_server)
  (before_network:list network_packet)
  (before_trace:DY.trace)
  (before_shadow:endpoint_shadow)
  (after_shadow:endpoint_shadow)
  (event:SM.conn_event)
  (raw_sent raw_received:B.bytes)
  (after_network:list network_packet)
  (after_trace:DY.trace)
  : prop =
  exists realization.
    protocol_event_realizes
      representation registry before_shadow event
      raw_sent raw_received realization /\
    protocol_event_fresh before_trace before_shadow realization /\
    (let event_trace =
       protocol_event_trace before_trace before_shadow realization in
     (B.length raw_sent == 0 /\
      B.length raw_received == 0 /\
      after_network == before_network /\
      after_trace == DY.Snoc event_trace (endpoint_state_entry after_shadow)) \/
     (B.length raw_sent <> 0 /\
      B.length raw_received == 0 /\
      exists symbolic.
        Bridge.represents representation raw_sent symbolic /\
        protocol_event_symbolic_message realization symbolic /\
        after_network == {
          packet_raw = raw_sent;
          packet_symbolic = symbolic;
        } :: before_network /\
        after_trace ==
          DY.Snoc
            (DY.Snoc event_trace (DY.MsgSent symbolic))
            (endpoint_state_entry after_shadow)) \/
     (B.length raw_sent == 0 /\
      B.length raw_received <> 0 /\
      exists packet.
        packet.packet_raw == raw_received /\
        Bridge.represents
          representation packet.packet_raw packet.packet_symbolic /\
        remove_packet packet before_network after_network /\
        after_trace == DY.Snoc event_trace (endpoint_state_entry after_shadow)))

let representation_extends
  (before after:Bridge.representation)
  : prop =
  DY.grows
    before.Bridge.representation_trace
    after.Bridge.representation_trace /\
  forall concrete symbolic.
    Bridge.explicitly_bound
      before.Bridge.representation_bindings concrete symbolic ==>
    Bridge.explicitly_bound
      after.Bridge.representation_bindings concrete symbolic

noeq
type product_action =
  | CreateEndpoint: endpoint_shadow -> product_action
  | HonestGenerate:
      shadow:endpoint_shadow ->
      usage:DY.usage ->
      label:DY.label ->
      length:nat{length <> 0} ->
      product_action
  | HonestLocal:
      before_shadow:endpoint_shadow ->
      after_shadow:endpoint_shadow ->
      event:SM.conn_event ->
      raw_sent:B.bytes ->
      raw_received:B.bytes ->
      product_action
  | HonestCanonical:
      before_shadow:endpoint_shadow ->
      after_shadow:endpoint_shadow ->
      event:SM.conn_event ->
      raw_sent:B.bytes ->
      raw_received:B.bytes ->
      product_action
  | AttackerInject: network_packet -> product_action
  | AttackerRoute: network_packet -> product_action
  | AttackerDrop: network_packet -> product_action
  | AttackerReplay: network_packet -> product_action
  | CorruptState:
      principal:DY.principal ->
      state_id:DY.state_id ->
      state_timestamp:DY.timestamp ->
      product_action

let symbolic_update_realizes
  (before after:product_state)
  (before_shadow after_shadow:endpoint_shadow)
  (event:SM.conn_event)
  (raw_sent raw_received:B.bytes)
  : prop =
  same_session before_shadow.shadow_session after_shadow.shadow_session /\
  after_shadow.shadow_origin == before_shadow.shadow_origin /\
  after_shadow.shadow_reverse_history == {
    concrete_before = before_shadow.shadow_concrete;
    concrete_after = after_shadow.shadow_concrete;
    concrete_event = event;
    concrete_raw_sent = raw_sent;
    concrete_raw_received = raw_received;
  } :: before_shadow.shadow_reverse_history /\
  representation_extends
    before.product_representation
    after.product_representation /\
  after.product_representation.Bridge.representation_trace ==
    after.product_trace /\
  replace_endpoint
    before_shadow after_shadow
    before.product_endpoints after.product_endpoints /\
  honest_network_trace_delta
    after.product_representation
    before.product_registry
    before.product_network
    before.product_trace
    before_shadow
    after_shadow
    event
    raw_sent raw_received
    after.product_network
    after.product_trace /\
  after.product_registry == before.product_registry /\
  endpoint_refines after.product_representation after_shadow

let honest_state_update
  (before after:product_state)
  (before_shadow after_shadow:endpoint_shadow)
  (event:SM.conn_event)
  (raw_sent raw_received:B.bytes)
  : prop =
  symbolic_update_realizes
    before after before_shadow after_shadow event raw_sent raw_received

let session_started_kind
  (role:Terms.symbolic_role)
  : Events.event_kind =
  match role with
  | Terms.SymbolicClient -> Events.ClientSessionStarted
  | Terms.SymbolicServer -> Events.ServerSessionStarted

let session_started_entry (shadow:endpoint_shadow) : DY.trace_entry =
  Events.event_entry
    shadow.shadow_session.Terms.session_principal
    (session_started_kind shadow.shadow_session.Terms.session_role)
    (Terms.encode_endpoint_session shadow.shadow_session)

let created_endpoint_trace
  (before:DY.trace)
  (shadow:endpoint_shadow)
  : DY.trace =
  DY.Snoc
    (DY.Snoc before (session_started_entry shadow))
    (endpoint_state_entry shadow)

let product_step
  (before:product_state)
  (action:product_action)
  (after:product_state)
  : prop =
  product_well_formed before /\
  product_well_formed after /\
  (match action with
  | CreateEndpoint shadow ->
    shadow.shadow_concrete ==
      SM.initial shadow.shadow_concrete.SM.cs_model.SM.model_config /\
    shadow.shadow_origin == shadow.shadow_concrete /\
    shadow.shadow_reverse_history == [] /\
    shadow.shadow_session.Terms.session_state_id ==
      DY.compute_new_session_id
        shadow.shadow_session.Terms.session_principal
        before.product_trace /\
    session_absent shadow.shadow_session before.product_endpoints /\
    after.product_trace == created_endpoint_trace before.product_trace shadow /\
    after.product_representation.Bridge.representation_trace ==
      after.product_trace /\
    after.product_representation.Bridge.representation_bindings ==
      before.product_representation.Bridge.representation_bindings /\
    after.product_endpoints == shadow :: before.product_endpoints /\
    after.product_network == before.product_network /\
    after.product_registry == before.product_registry /\
    endpoint_refines after.product_representation shadow
  | HonestGenerate shadow usage label length ->
    endpoint_member shadow before.product_endpoints /\
    after.product_trace ==
      DY.Snoc before.product_trace (DY.RandGen usage label length) /\
    after.product_representation.Bridge.representation_trace ==
      after.product_trace /\
    after.product_representation.Bridge.representation_bindings ==
      before.product_representation.Bridge.representation_bindings /\
    after.product_endpoints == before.product_endpoints /\
    after.product_network == before.product_network /\
    after.product_registry == before.product_registry
  | HonestLocal
      before_shadow after_shadow event raw_sent raw_received ->
    endpoint_member before_shadow before.product_endpoints /\
    is_local_event event /\
    B.length raw_sent == 0 /\
    B.length raw_received == 0 /\
    SM.legal_connection_delta
      before_shadow.shadow_concrete
      {
        SM.delta_event = event;
        SM.delta_raw_sent = raw_sent;
        SM.delta_raw_received = raw_received;
      }
      after_shadow.shadow_concrete /\
    symbolic_update_realizes
      before after before_shadow after_shadow event raw_sent raw_received
  | HonestCanonical
      before_shadow after_shadow event raw_sent raw_received ->
    endpoint_member before_shadow before.product_endpoints /\
    event_excludes_key_update event /\
    (B.length raw_sent <> 0 \/ B.length raw_received <> 0) /\
    Canonical.canonical_wire_step
      before_shadow.shadow_concrete
      after_shadow.shadow_concrete
      event raw_sent raw_received /\
    symbolic_update_realizes
      before after before_shadow after_shadow event raw_sent raw_received
  | AttackerInject packet ->
    DY.attacker_knows before.product_trace packet.packet_symbolic /\
    Bridge.represents
      before.product_representation
      packet.packet_raw
      packet.packet_symbolic /\
    after.product_trace == before.product_trace /\
    after.product_representation == before.product_representation /\
    after.product_endpoints == before.product_endpoints /\
    after.product_network == packet :: before.product_network /\
    after.product_registry == before.product_registry
  | AttackerRoute packet ->
    packet_member packet before.product_network /\
    after == before
  | AttackerDrop packet ->
    after.product_trace == before.product_trace /\
    after.product_representation == before.product_representation /\
    after.product_endpoints == before.product_endpoints /\
    after.product_registry == before.product_registry /\
    remove_packet
      packet before.product_network after.product_network
  | AttackerReplay packet ->
    packet_member packet before.product_network /\
    after.product_trace == before.product_trace /\
    after.product_representation == before.product_representation /\
    after.product_endpoints == before.product_endpoints /\
    after.product_network == packet :: before.product_network /\
    after.product_registry == before.product_registry
  | CorruptState principal state_id state_timestamp ->
    (exists content.
      DY.entry_at
        before.product_trace
        state_timestamp
        (DY.SetState principal state_id content)) /\
    after.product_trace ==
      DY.Snoc before.product_trace (DY.Corrupt state_timestamp) /\
    after.product_representation.Bridge.representation_trace ==
      after.product_trace /\
    after.product_representation.Bridge.representation_bindings ==
      before.product_representation.Bridge.representation_bindings /\
    after.product_endpoints == before.product_endpoints /\
    after.product_network == before.product_network /\
    after.product_registry == before.product_registry)

noeq
type product_transition = {
  transition_before: product_state;
  transition_action: product_action;
  transition_after: product_state;
}

let rec product_execution
  (initial:product_state)
  (transitions:list product_transition)
  (final:product_state)
  : Tot prop (decreases transitions) =
  match transitions with
  | [] -> final == initial /\ product_well_formed initial
  | transition :: rest ->
    transition.transition_before == initial /\
    product_step
      transition.transition_before
      transition.transition_action
      transition.transition_after /\
    product_execution transition.transition_after rest final

val initial_product_state_has_unique_security_events:
  state:product_state ->
  Lemma
    (requires initial_product_state state)
    (ensures security_events_unique state.product_trace)
let initial_product_state_has_unique_security_events state =
  norm_spec
    [delta_only
      [`%initial_product_state;
       `%security_origin_free;
       `%security_events_unique;
       `%trace_entry_unique;
       `%DY.event_triggered;
       `%DY.event_triggered_at;
       `%DY.entry_exists]]
    (initial_product_state state)

val protocol_event_entry_is_security:
  shadow:endpoint_shadow ->
  realization:protocol_event_realization ->
  entry:DY.trace_entry ->
  Lemma
    (requires protocol_event_entry shadow realization == Some entry)
    (ensures is_security_event_entry entry)
let protocol_event_entry_is_security shadow realization entry =
  match realization with
  | NoProtocolEvent -> ()
  | ServerSignatureGenerated _ _ _ _ -> ()
  | ServerFinishedGenerated _ _ _ -> ()
  | ClientFinishedGenerated _ _ _ -> ()
  | ProtectedRecordsGenerated _ -> ()
  | ProtectedRecordAccepted _ -> ()

val sent_record_event_trace_preserves_unique_security_events:
  before:DY.trace ->
  records:list sent_record_realization ->
  Lemma
    (requires security_events_unique before)
    (ensures
      security_events_unique (sent_record_event_trace before records))
    (decreases (List.Tot.length records))
let rec sent_record_event_trace_preserves_unique_security_events
  before records =
  match records with
  | [] -> ()
  | record :: rest ->
    assert (~(is_security_event_entry (sent_record_event_entry record)));
    security_events_unique_snoc before (sent_record_event_entry record);
    sent_record_event_trace_preserves_unique_security_events
      (DY.Snoc before (sent_record_event_entry record))
      rest

val protocol_event_trace_preserves_unique_security_events:
  before:DY.trace ->
  shadow:endpoint_shadow ->
  realization:protocol_event_realization ->
  Lemma
    (requires
      security_events_unique before /\
      protocol_event_fresh before shadow realization)
    (ensures
      security_events_unique
        (protocol_event_trace before shadow realization))
let protocol_event_trace_preserves_unique_security_events
  before shadow realization =
  match realization with
  | ServerFinishedGenerated _ _ records
  | ClientFinishedGenerated _ _ records ->
    (match protocol_event_entry shadow realization with
     | None -> ()
     | Some entry ->
       protocol_event_entry_is_security shadow realization entry;
       security_events_unique_snoc before entry;
       sent_record_event_trace_preserves_unique_security_events
         (DY.Snoc before entry) records)
  | ProtectedRecordsGenerated records ->
    sent_record_event_trace_preserves_unique_security_events before records
  | ProtectedRecordAccepted record ->
    assert (~(is_security_event_entry
      (accepted_record_event_entry shadow record)));
    security_events_unique_snoc
      before (accepted_record_event_entry shadow record)
  | _ ->
    (match protocol_event_entry shadow realization with
     | None -> ()
     | Some entry ->
       protocol_event_entry_is_security shadow realization entry;
       security_events_unique_snoc before entry)

val honest_network_trace_delta_preserves_unique_security_events:
  representation:Bridge.representation ->
  registry:list Bridge.trusted_server ->
  before_network:list network_packet ->
  before_trace:DY.trace ->
  before_shadow:endpoint_shadow ->
  after_shadow:endpoint_shadow ->
  event:SM.conn_event ->
  raw_sent:B.bytes ->
  raw_received:B.bytes ->
  after_network:list network_packet ->
  after_trace:DY.trace ->
  Lemma
    (requires
      security_events_unique before_trace /\
      honest_network_trace_delta
        representation registry before_network before_trace
        before_shadow after_shadow event raw_sent raw_received
        after_network after_trace)
    (ensures security_events_unique after_trace)
let honest_network_trace_delta_preserves_unique_security_events
  representation registry before_network before_trace
  before_shadow after_shadow event raw_sent raw_received
  after_network after_trace =
  eliminate exists realization.
    protocol_event_realizes
      representation registry before_shadow event
      raw_sent raw_received realization /\
    protocol_event_fresh before_trace before_shadow realization /\
    (let event_trace =
       protocol_event_trace before_trace before_shadow realization in
     (B.length raw_sent == 0 /\
      B.length raw_received == 0 /\
      after_network == before_network /\
      after_trace == DY.Snoc event_trace (endpoint_state_entry after_shadow)) \/
     (B.length raw_sent <> 0 /\
      B.length raw_received == 0 /\
      exists symbolic.
        Bridge.represents representation raw_sent symbolic /\
        protocol_event_symbolic_message realization symbolic /\
        after_network == {
          packet_raw = raw_sent;
          packet_symbolic = symbolic;
        } :: before_network /\
        after_trace ==
          DY.Snoc
            (DY.Snoc event_trace (DY.MsgSent symbolic))
            (endpoint_state_entry after_shadow)) \/
     (B.length raw_sent == 0 /\
      B.length raw_received <> 0 /\
      exists packet.
        packet.packet_raw == raw_received /\
        Bridge.represents
          representation packet.packet_raw packet.packet_symbolic /\
        remove_packet packet before_network after_network /\
        after_trace == DY.Snoc event_trace (endpoint_state_entry after_shadow)))
  returns security_events_unique after_trace
  with _. (
    let event_trace =
      protocol_event_trace before_trace before_shadow realization in
    protocol_event_trace_preserves_unique_security_events
      before_trace before_shadow realization;
    if B.length raw_sent = 0
    then begin
      assert (after_trace ==
        DY.Snoc event_trace (endpoint_state_entry after_shadow));
      assert (~(is_security_event_entry (endpoint_state_entry after_shadow)));
      security_events_unique_snoc
        event_trace (endpoint_state_entry after_shadow)
    end
    else begin
      eliminate exists symbolic.
        Bridge.represents representation raw_sent symbolic /\
        protocol_event_symbolic_message realization symbolic /\
        after_network == {
          packet_raw = raw_sent;
          packet_symbolic = symbolic;
        } :: before_network /\
        after_trace ==
          DY.Snoc
            (DY.Snoc event_trace (DY.MsgSent symbolic))
            (endpoint_state_entry after_shadow)
      returns security_events_unique after_trace
      with _. (
        assert (~(is_security_event_entry (DY.MsgSent symbolic)));
        security_events_unique_snoc event_trace (DY.MsgSent symbolic);
        assert (~(is_security_event_entry
          (endpoint_state_entry after_shadow)));
        security_events_unique_snoc
          (DY.Snoc event_trace (DY.MsgSent symbolic))
          (endpoint_state_entry after_shadow))
    end)

val product_step_preserves_unique_security_events:
  before:product_state ->
  action:product_action ->
  after:product_state ->
  Lemma
    (requires
      security_events_unique before.product_trace /\
      product_step before action after)
    (ensures security_events_unique after.product_trace)
let product_step_preserves_unique_security_events before action after =
  match action with
  | CreateEndpoint shadow ->
    assert (~(is_security_event_entry (session_started_entry shadow)));
    security_events_unique_snoc
      before.product_trace (session_started_entry shadow);
    assert (~(is_security_event_entry (endpoint_state_entry shadow)));
    security_events_unique_snoc
      (DY.Snoc before.product_trace (session_started_entry shadow))
      (endpoint_state_entry shadow)
  | HonestGenerate shadow usage label length ->
    assert (~(is_security_event_entry (DY.RandGen usage label length)));
    security_events_unique_snoc
      before.product_trace (DY.RandGen usage label length)
  | HonestLocal
      before_shadow after_shadow event raw_sent raw_received
  | HonestCanonical
      before_shadow after_shadow event raw_sent raw_received ->
    honest_network_trace_delta_preserves_unique_security_events
      after.product_representation
      before.product_registry
      before.product_network
      before.product_trace
      before_shadow after_shadow event raw_sent raw_received
      after.product_network
      after.product_trace
  | AttackerInject _
  | AttackerRoute _
  | AttackerDrop _
  | AttackerReplay _ -> ()
  | CorruptState _ _ timestamp ->
    assert (~(is_security_event_entry (DY.Corrupt timestamp)));
    security_events_unique_snoc
      before.product_trace (DY.Corrupt timestamp)

val product_execution_preserves_unique_security_events:
  initial:product_state ->
  transitions:list product_transition ->
  final:product_state ->
  Lemma
    (requires
      security_events_unique initial.product_trace /\
      product_execution initial transitions final)
    (ensures security_events_unique final.product_trace)
    (decreases (List.Tot.length transitions))
let rec product_execution_preserves_unique_security_events
  initial transitions final =
  match transitions with
  | [] -> ()
  | transition :: rest ->
    product_step_preserves_unique_security_events
      transition.transition_before
      transition.transition_action
      transition.transition_after;
    product_execution_preserves_unique_security_events
      transition.transition_after rest final

val reachable_product_state_has_unique_security_events:
  initial:product_state ->
  transitions:list product_transition ->
  final:product_state ->
  Lemma
    (requires
      initial_product_state initial /\
      product_execution initial transitions final)
    (ensures security_events_unique final.product_trace)
let reachable_product_state_has_unique_security_events
  initial transitions final =
  initial_product_state_has_unique_security_events initial;
  product_execution_preserves_unique_security_events
    initial transitions final

let transition_projects_exactly
 (concrete:concrete_transition)
 (product:product_transition)
 : prop =
 match product.transition_action with
 | HonestLocal
     before_shadow after_shadow event raw_sent raw_received ->
   before_shadow.shadow_concrete == concrete.concrete_before /\
   after_shadow.shadow_concrete == concrete.concrete_after /\
   event == concrete.concrete_event /\
   raw_sent == concrete.concrete_raw_sent /\
   raw_received == concrete.concrete_raw_received
 | HonestCanonical
     before_shadow after_shadow event raw_sent raw_received ->
    before_shadow.shadow_concrete == concrete.concrete_before /\
    after_shadow.shadow_concrete == concrete.concrete_after /\
    event == concrete.concrete_event /\
    raw_sent == concrete.concrete_raw_sent /\
    raw_received == concrete.concrete_raw_received
  | _ -> False

let concrete_transition_in_profile
  (transition:concrete_transition)
  : prop =
  event_excludes_key_update transition.concrete_event /\
  ((B.length transition.concrete_raw_sent == 0 /\
    B.length transition.concrete_raw_received == 0 /\
    is_local_event transition.concrete_event /\
    concrete_transition_is_legal transition) \/
   ((B.length transition.concrete_raw_sent <> 0 /\
     B.length transition.concrete_raw_received == 0) \/
    (B.length transition.concrete_raw_sent == 0 /\
     B.length transition.concrete_raw_received <> 0)) /\
   concrete_transition_is_canonical transition)

noeq
type transition_realization = {
  realization_before_shadow: endpoint_shadow;
  realization_after_shadow: endpoint_shadow;
  realization_after_state: product_state;
}

let transition_realization_obligations
  (before:product_state)
  (concrete:concrete_transition)
  (realization:transition_realization)
  : prop =
  let before_shadow = realization.realization_before_shadow in
  let after_shadow = realization.realization_after_shadow in
  let after = realization.realization_after_state in
  concrete_transition_in_profile concrete /\
  product_well_formed before /\
  product_well_formed after /\
  endpoint_member before_shadow before.product_endpoints /\
  before_shadow.shadow_concrete == concrete.concrete_before /\
  after_shadow.shadow_concrete == concrete.concrete_after /\
  symbolic_update_realizes
    before after before_shadow after_shadow
    concrete.concrete_event
    concrete.concrete_raw_sent
    concrete.concrete_raw_received

let symbolically_realizable_transition
  (before:product_state)
  (concrete:concrete_transition)
  (realization:transition_realization)
  : prop =
  transition_realization_obligations before concrete realization

let realized_product_transition
  (before:product_state)
  (concrete:concrete_transition)
  (realization:transition_realization)
  : product_transition =
  let action =
    if B.length concrete.concrete_raw_sent = 0 &&
       B.length concrete.concrete_raw_received = 0
    then HonestLocal
      realization.realization_before_shadow
      realization.realization_after_shadow
      concrete.concrete_event
      concrete.concrete_raw_sent
      concrete.concrete_raw_received
    else HonestCanonical
      realization.realization_before_shadow
      realization.realization_after_shadow
      concrete.concrete_event
      concrete.concrete_raw_sent
      concrete.concrete_raw_received in
  {
    transition_before = before;
    transition_action = action;
    transition_after = realization.realization_after_state;
  }

val transition_realization_facts:
  before:product_state ->
  concrete:concrete_transition ->
  realization:transition_realization ->
  Lemma
    (requires
      transition_realization_obligations before concrete realization)
    (ensures (
      product_well_formed before /\
      product_well_formed realization.realization_after_state /\
      endpoint_member
        realization.realization_before_shadow before.product_endpoints /\
      realization.realization_before_shadow.shadow_concrete ==
        concrete.concrete_before /\
      realization.realization_after_shadow.shadow_concrete ==
        concrete.concrete_after /\
      event_excludes_key_update concrete.concrete_event /\
      symbolic_update_realizes
        before
        realization.realization_after_state
        realization.realization_before_shadow
        realization.realization_after_shadow
        concrete.concrete_event
        concrete.concrete_raw_sent
        concrete.concrete_raw_received /\
      (if B.length concrete.concrete_raw_sent = 0 &&
          B.length concrete.concrete_raw_received = 0
       then
         is_local_event concrete.concrete_event /\
         concrete_transition_is_legal concrete
       else
         ((B.length concrete.concrete_raw_sent <> 0 /\
           B.length concrete.concrete_raw_received == 0) \/
          (B.length concrete.concrete_raw_sent == 0 /\
           B.length concrete.concrete_raw_received <> 0)) /\
         concrete_transition_is_canonical concrete)))
let transition_realization_facts before concrete realization =
  norm_spec
    [zeta; delta_only [`%transition_realization_obligations]]
    (transition_realization_obligations before concrete realization);
  norm_spec
    [zeta; delta_only [`%concrete_transition_in_profile]]
    (concrete_transition_in_profile concrete);
  if B.length concrete.concrete_raw_sent = 0 &&
     B.length concrete.concrete_raw_received = 0
  then ()
  else ()

val realizable_transition_lifts:
  before:product_state ->
  concrete:concrete_transition ->
  realization:transition_realization ->
  Lemma
    (requires
      transition_realization_obligations before concrete realization)
    (ensures (
      let product =
        realized_product_transition before concrete realization in
      product_step
        product.transition_before
        product.transition_action
        product.transition_after /\
      transition_projects_exactly concrete product))
let realizable_transition_lifts before concrete realization =
  transition_realization_facts before concrete realization;
  let product =
    realized_product_transition before concrete realization in
  if B.length concrete.concrete_raw_sent = 0 &&
     B.length concrete.concrete_raw_received = 0
  then (
    norm_spec
      [zeta; iota; delta_only [`%realized_product_transition; `%product_step]]
      (product_step
        product.transition_before
        product.transition_action
        product.transition_after);
    norm_spec
      [zeta; iota;
       delta_only [`%realized_product_transition; `%transition_projects_exactly]]
      (transition_projects_exactly concrete product)
  )
  else (
    norm_spec
      [zeta; iota; delta_only [`%realized_product_transition; `%product_step]]
      (product_step
        product.transition_before
        product.transition_action
        product.transition_after);
    norm_spec
      [zeta; iota;
       delta_only [`%realized_product_transition; `%transition_projects_exactly]]
      (transition_projects_exactly concrete product)
  )

let rec symbolically_realizable_execution
  (product_initial:product_state)
  (concrete_initial:SM.connection_state)
  (concrete:list concrete_transition)
  (concrete_final:SM.connection_state)
  (realizations:list transition_realization)
  (product_final:product_state)
  : Tot prop (decreases concrete) =
  match concrete, realizations with
  | [], [] ->
    concrete_final == concrete_initial /\
    product_final == product_initial /\
    product_well_formed product_initial
  | concrete_head :: concrete_tail,
    realization_head :: realization_tail ->
    concrete_head.concrete_before == concrete_initial /\
    transition_realization_obligations
      product_initial concrete_head realization_head /\
    symbolically_realizable_execution
      realization_head.realization_after_state
      concrete_head.concrete_after
      concrete_tail
      concrete_final
      realization_tail
      product_final
  | _, _ -> False

let rec lifted_product_transitions
  (product_initial:product_state)
  (concrete:list concrete_transition)
  (realizations:list transition_realization)
  : Tot (list product_transition) (decreases concrete) =
  match concrete, realizations with
  | concrete_head :: concrete_tail,
    realization_head :: realization_tail ->
    realized_product_transition
      product_initial concrete_head realization_head ::
    lifted_product_transitions
      realization_head.realization_after_state
      concrete_tail
      realization_tail
  | _, _ -> []

let rec execution_projects_exactly
  (concrete:list concrete_transition)
  (product:list product_transition)
  : Tot prop (decreases concrete) =
  match concrete, product with
  | [], [] -> True
  | concrete_head :: concrete_tail, product_head :: product_tail ->
    transition_projects_exactly concrete_head product_head /\
    execution_projects_exactly concrete_tail product_tail
  | _, _ -> False

val complete_execution_lifts:
  product_initial:product_state ->
  concrete_initial:SM.connection_state ->
  concrete:list concrete_transition ->
  concrete_final:SM.connection_state ->
  realizations:list transition_realization ->
  product_final:product_state ->
  Lemma
    (requires
      symbolically_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final)
    (ensures (
      let product =
        lifted_product_transitions
          product_initial concrete realizations in
      concrete_execution concrete_initial concrete concrete_final /\
      product_execution product_initial product product_final /\
      execution_projects_exactly concrete product))
    (decreases (List.Tot.length concrete))
let rec complete_execution_lifts
  product_initial concrete_initial concrete concrete_final
  realizations product_final =
  match concrete, realizations with
  | [], [] -> ()
  | concrete_head :: concrete_tail,
    realization_head :: realization_tail ->
    norm_spec
      [zeta; iota; delta_only [`%symbolically_realizable_execution]]
      (symbolically_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final);
    realizable_transition_lifts
      product_initial concrete_head realization_head;
    complete_execution_lifts
      realization_head.realization_after_state
      concrete_head.concrete_after
      concrete_tail
      concrete_final
      realization_tail
      product_final
  | _, _ -> ()

val concrete_execution_has_product_lift:
  product_initial:product_state ->
  concrete_initial:SM.connection_state ->
  concrete:list concrete_transition ->
  concrete_final:SM.connection_state ->
  realizations:list transition_realization ->
  product_final:product_state ->
  Lemma
    (requires
      symbolically_realizable_execution
        product_initial concrete_initial concrete concrete_final
        realizations product_final)
    (ensures
      exists product.
        product ==
          lifted_product_transitions
            product_initial concrete realizations /\
        product_execution product_initial product product_final /\
        execution_projects_exactly concrete product)
let concrete_execution_has_product_lift
  product_initial concrete_initial concrete concrete_final
  realizations product_final =
  complete_execution_lifts
    product_initial concrete_initial concrete concrete_final
    realizations product_final

val product_step_preserves_well_formed:
  before:product_state ->
  action:product_action ->
  after:product_state ->
  Lemma
    (requires product_step before action after)
    (ensures
      product_well_formed before /\
      product_well_formed after)
let product_step_preserves_well_formed before action after = ()

val product_execution_final_well_formed:
  initial:product_state ->
  transitions:list product_transition ->
  final:product_state ->
  Lemma
    (requires product_execution initial transitions final)
    (ensures product_well_formed final)
    (decreases (List.Tot.length transitions))
let rec product_execution_final_well_formed initial transitions final =
  norm_spec
    [zeta; iota; delta_only [`%product_execution]]
    (product_execution initial transitions final);
  match transitions with
  | [] -> ()
  | transition :: rest ->
    product_execution_final_well_formed
      transition.transition_after rest final

val honest_local_step_is_legal:
  before:product_state ->
  after:product_state ->
  before_shadow:endpoint_shadow ->
  after_shadow:endpoint_shadow ->
  event:SM.conn_event ->
  raw_sent:B.bytes ->
  raw_received:B.bytes ->
  Lemma
    (requires
      product_step
        before
        (HonestLocal
          before_shadow after_shadow event raw_sent raw_received)
        after)
    (ensures
      SM.legal_connection_delta
        before_shadow.shadow_concrete
        {
          SM.delta_event = event;
          SM.delta_raw_sent = raw_sent;
          SM.delta_raw_received = raw_received;
        }
        after_shadow.shadow_concrete)
let honest_local_step_is_legal
  before after before_shadow after_shadow event raw_sent raw_received = ()

val honest_canonical_step_is_legal:
  before:product_state ->
  after:product_state ->
  before_shadow:endpoint_shadow ->
  after_shadow:endpoint_shadow ->
  event:SM.conn_event ->
  raw_sent:B.bytes ->
  raw_received:B.bytes ->
  Lemma
    (requires
      product_step
        before
        (HonestCanonical
          before_shadow after_shadow event raw_sent raw_received)
        after)
    (ensures
      SM.legal_connection_delta
        before_shadow.shadow_concrete
        {
          SM.delta_event = event;
          SM.delta_raw_sent = raw_sent;
          SM.delta_raw_received = raw_received;
        }
        after_shadow.shadow_concrete /\
      Canonical.canonical_wire_step
        before_shadow.shadow_concrete
        after_shadow.shadow_concrete
        event raw_sent raw_received)
let honest_canonical_step_is_legal
  before after before_shadow after_shadow event raw_sent raw_received = ()

val endpoint_member_refines:
  representation:Bridge.representation ->
  endpoints:list endpoint_shadow ->
  shadow:endpoint_shadow ->
  Lemma
    (requires
      endpoints_refine representation endpoints /\
      endpoint_member shadow endpoints)
    (ensures endpoint_refines representation shadow)
    (decreases (List.Tot.length endpoints))
let rec endpoint_member_refines representation endpoints shadow =
  match endpoints with
  | [] -> ()
  | head :: tail ->
    if head == shadow then ()
    else endpoint_member_refines representation tail shadow

val endpoint_projection_is_reachable:
  state:product_state ->
  shadow:endpoint_shadow ->
  Lemma
    (requires
      product_well_formed state /\
      endpoint_member shadow state.product_endpoints)
    (ensures Reach.connection_state_consistent shadow.shadow_concrete)
let endpoint_projection_is_reachable state shadow =
  endpoint_member_refines
    state.product_representation state.product_endpoints shadow

val reachable_endpoint_projects_exactly:
  initial:product_state ->
  transitions:list product_transition ->
  final:product_state ->
  shadow:endpoint_shadow ->
  Lemma
    (requires
      product_execution initial transitions final /\
      endpoint_member shadow final.product_endpoints)
    (ensures
      shadow.shadow_origin ==
        SM.initial shadow.shadow_origin.SM.cs_model.SM.model_config /\
      reverse_concrete_execution
        shadow.shadow_concrete
        shadow.shadow_reverse_history
        shadow.shadow_origin /\
      Reach.connection_state_consistent shadow.shadow_concrete)
let reachable_endpoint_projects_exactly
  initial transitions final shadow =
  product_execution_final_well_formed initial transitions final;
  endpoint_projection_is_reachable final shadow;
  endpoint_member_refines
    final.product_representation final.product_endpoints shadow
