module TLS13.Symbolic.Product

module B = TLS13.Bytes
module Bridge = TLS13.Symbolic.Bridge
module Canonical = TLS13.Spec.StateMachine.Canonical
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module DY = DY.Core
module Events = TLS13.Symbolic.Events
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module Profile = TLS13.Symbolic.Profile
module R = TLS13.Record.Spec
module Reach = TLS13.Spec.StateMachine.Reachability
module SM = TLS13.Spec.StateMachine
module Terms = TLS13.Symbolic.Terms
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

let product_well_formed (state:product_state) : prop =
  state.product_representation.Bridge.representation_trace ==
    state.product_trace /\
  endpoints_refine
    state.product_representation
    state.product_endpoints /\
  sessions_unique state.product_endpoints

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

let honest_network_trace_delta
  (representation:Bridge.representation)
  (before_network:list network_packet)
  (before_trace:DY.trace)
  (after_shadow:endpoint_shadow)
  (raw_sent raw_received:B.bytes)
  (after_network:list network_packet)
  (after_trace:DY.trace)
  : prop =
  (B.length raw_sent == 0 /\
   B.length raw_received == 0 /\
   after_network == before_network /\
   after_trace == DY.Snoc before_trace (endpoint_state_entry after_shadow)) \/
  (B.length raw_sent <> 0 /\
   B.length raw_received == 0 /\
   exists symbolic.
     Bridge.represents representation raw_sent symbolic /\
     after_network == {
       packet_raw = raw_sent;
       packet_symbolic = symbolic;
     } :: before_network /\
     after_trace ==
       DY.Snoc
         (DY.Snoc before_trace (DY.MsgSent symbolic))
         (endpoint_state_entry after_shadow)) \/
  (B.length raw_sent == 0 /\
   B.length raw_received <> 0 /\
   exists packet.
     packet.packet_raw == raw_received /\
     Bridge.represents
       representation packet.packet_raw packet.packet_symbolic /\
     remove_packet packet before_network after_network /\
     after_trace == DY.Snoc before_trace (endpoint_state_entry after_shadow))

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
    before.product_network
    before.product_trace
    after_shadow
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
