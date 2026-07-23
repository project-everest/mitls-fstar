module TLS13.Symbolic.Secrecy

module B = TLS13.Bytes
module DY = DY.Core
module Invariant = TLS13.Symbolic.Invariant
module K = TLS13.Keys
module Lemmas = TLS13.Symbolic.Lemmas
module Product = TLS13.Symbolic.Product
module Seq = FStar.Seq
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

noeq
type key_schedule_inputs = {
  client_session: Terms.endpoint_session;
  server_session: Terms.endpoint_session;
  client_ephemeral_secret: DY.bytes;
  server_ephemeral_secret: DY.bytes;
  handshake_transcript: DY.bytes;
  application_transcript: DY.bytes;
}

let shared_secret (inputs:key_schedule_inputs) : DY.bytes =
  Terms.x25519_shared
    inputs.client_ephemeral_secret
    (Terms.x25519_public inputs.server_ephemeral_secret)

let handshake_secret (inputs:key_schedule_inputs) : DY.bytes =
  Terms.handshake_secret (shared_secret inputs)

let master_secret (inputs:key_schedule_inputs) : DY.bytes =
  Terms.master_secret (handshake_secret inputs)

let client_handshake_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.client_handshake_traffic_secret
    (handshake_secret inputs)
    inputs.handshake_transcript

let server_handshake_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.server_handshake_traffic_secret
    (handshake_secret inputs)
    inputs.handshake_transcript

let client_application_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.client_application_traffic_secret
    (master_secret inputs)
    inputs.application_transcript

let server_application_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.server_application_traffic_secret
    (master_secret inputs)
    inputs.application_transcript

let traffic_material_matches
  (material:option Product.symbolic_traffic_material)
  (traffic_secret:DY.bytes)
  : prop =
  match material with
  | None -> False
  | Some installed ->
    installed.Product.symbolic_traffic_secret == traffic_secret /\
    installed.Product.symbolic_traffic_key ==
      Terms.record_key traffic_secret /\
    installed.Product.symbolic_traffic_iv ==
      Terms.record_iv traffic_secret

let complete_key_schedule_lineage
  (schedule:Product.symbolic_key_schedule)
  (inputs:key_schedule_inputs)
  : prop =
  schedule.Product.symbolic_early_secret == Some Terms.early_secret /\
  schedule.Product.symbolic_shared_secret == Some (shared_secret inputs) /\
  schedule.Product.symbolic_handshake_secret ==
    Some (handshake_secret inputs) /\
  schedule.Product.symbolic_master_secret == Some (master_secret inputs) /\
  traffic_material_matches
    schedule.Product.symbolic_client_handshake_traffic
    (client_handshake_traffic_secret inputs) /\
  traffic_material_matches
    schedule.Product.symbolic_server_handshake_traffic
    (server_handshake_traffic_secret inputs) /\
  traffic_material_matches
    schedule.Product.symbolic_client_application_traffic
    (client_application_traffic_secret inputs) /\
  traffic_material_matches
    schedule.Product.symbolic_server_application_traffic
    (server_application_traffic_secret inputs)

let ephemeral_pair_has_labels
  (tr:DY.trace)
  (inputs:key_schedule_inputs)
  (client_label server_label:DY.label)
  : prop =
  DY.get_label tr inputs.client_ephemeral_secret == client_label /\
  DY.get_label tr inputs.server_ephemeral_secret == server_label /\
  inputs.client_ephemeral_secret `DY.has_usage tr`
    Usages.ephemeral_dh_usage inputs.client_session /\
  inputs.server_ephemeral_secret `DY.has_usage tr`
    Usages.ephemeral_dh_usage inputs.server_session

let schedule_secret_label
  (tr:DY.trace)
  (inputs:key_schedule_inputs)
  : DY.label =
  DY.join
    (DY.get_label tr inputs.client_ephemeral_secret)
    (DY.get_label tr inputs.server_ephemeral_secret)

type schedule_secret_kind =
  | SharedSecret
  | HandshakeSecret
  | ClientHandshakeTrafficSecret
  | ServerHandshakeTrafficSecret
  | ClientFinishedKey
  | ServerFinishedKey
  | MasterSecret
  | ClientApplicationTrafficSecret
  | ServerApplicationTrafficSecret
  | ClientHandshakeRecordKey
  | ServerHandshakeRecordKey
  | ClientApplicationRecordKey
  | ServerApplicationRecordKey

let schedule_secret_term
  (kind:schedule_secret_kind)
  (inputs:key_schedule_inputs)
  : DY.bytes =
  match kind with
  | SharedSecret -> shared_secret inputs
  | HandshakeSecret -> handshake_secret inputs
  | ClientHandshakeTrafficSecret ->
    client_handshake_traffic_secret inputs
  | ServerHandshakeTrafficSecret ->
    server_handshake_traffic_secret inputs
  | ClientFinishedKey ->
    Terms.finished_key (client_handshake_traffic_secret inputs)
  | ServerFinishedKey ->
    Terms.finished_key (server_handshake_traffic_secret inputs)
  | MasterSecret -> master_secret inputs
  | ClientApplicationTrafficSecret ->
    client_application_traffic_secret inputs
  | ServerApplicationTrafficSecret ->
    server_application_traffic_secret inputs
  | ClientHandshakeRecordKey ->
    Terms.record_key (client_handshake_traffic_secret inputs)
  | ServerHandshakeRecordKey ->
    Terms.record_key (server_handshake_traffic_secret inputs)
  | ClientApplicationRecordKey ->
    Terms.record_key (client_application_traffic_secret inputs)
  | ServerApplicationRecordKey ->
    Terms.record_key (server_application_traffic_secret inputs)

let schedule_target_matches
  (schedule:Product.symbolic_key_schedule)
  (kind:schedule_secret_kind)
  (target:DY.bytes)
  : prop =
  match kind with
  | SharedSecret ->
    schedule.Product.symbolic_shared_secret == Some target
  | HandshakeSecret ->
    schedule.Product.symbolic_handshake_secret == Some target
  | MasterSecret ->
    schedule.Product.symbolic_master_secret == Some target
  | ClientHandshakeTrafficSecret ->
    (match schedule.Product.symbolic_client_handshake_traffic with
     | Some material ->
       material.Product.symbolic_traffic_secret == target
     | None -> False)
  | ServerHandshakeTrafficSecret ->
    (match schedule.Product.symbolic_server_handshake_traffic with
     | Some material ->
       material.Product.symbolic_traffic_secret == target
     | None -> False)
  | ClientApplicationTrafficSecret ->
    (match schedule.Product.symbolic_client_application_traffic with
     | Some material ->
       material.Product.symbolic_traffic_secret == target
     | None -> False)
  | ServerApplicationTrafficSecret ->
    (match schedule.Product.symbolic_server_application_traffic with
     | Some material ->
       material.Product.symbolic_traffic_secret == target
     | None -> False)
  | ClientFinishedKey ->
    (match schedule.Product.symbolic_client_handshake_traffic with
     | Some material ->
       Terms.finished_key material.Product.symbolic_traffic_secret == target
     | None -> False)
  | ServerFinishedKey ->
    (match schedule.Product.symbolic_server_handshake_traffic with
     | Some material ->
       Terms.finished_key material.Product.symbolic_traffic_secret == target
     | None -> False)
  | ClientHandshakeRecordKey ->
    (match schedule.Product.symbolic_client_handshake_traffic with
     | Some material ->
       material.Product.symbolic_traffic_key == target
     | None -> False)
  | ServerHandshakeRecordKey ->
    (match schedule.Product.symbolic_server_handshake_traffic with
     | Some material ->
       material.Product.symbolic_traffic_key == target
     | None -> False)
  | ClientApplicationRecordKey ->
    (match schedule.Product.symbolic_client_application_traffic with
     | Some material ->
       material.Product.symbolic_traffic_key == target
     | None -> False)
  | ServerApplicationRecordKey ->
    (match schedule.Product.symbolic_server_application_traffic with
     | Some material ->
       material.Product.symbolic_traffic_key == target
     | None -> False)

val early_secret_is_public:
  tr:DY.trace ->
  Lemma (DY.get_label tr Terms.early_secret == DY.public)
let early_secret_is_public tr =
  norm_spec
    [delta_only
      [`%Terms.early_secret;
       `%Terms.public_zero_secret;
       `%Terms.public_bytes]]
    (DY.get_label tr Terms.early_secret);
  normalize_term_spec DY.get_label;
  DY.meet_public_label DY.public

val shared_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (shared_secret inputs) ==
     schedule_secret_label tr inputs)
let shared_secret_has_session_label tr inputs =
  Lemmas.x25519_shared_label
    tr inputs.client_ephemeral_secret inputs.server_ephemeral_secret

val shared_secret_has_tls_usage:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (requires
      inputs.client_ephemeral_secret `DY.has_usage tr`
        Usages.ephemeral_dh_usage inputs.client_session /\
      inputs.server_ephemeral_secret `DY.has_usage tr`
        Usages.ephemeral_dh_usage inputs.server_session)
    (ensures
      shared_secret inputs `DY.has_usage tr` Usages.shared_dh_usage)
let shared_secret_has_tls_usage tr inputs =
  DY.has_dh_usage_dh_pk
    tr
    inputs.server_ephemeral_secret
    (Usages.ephemeral_dh_usage inputs.server_session);
  DY.has_usage_dh_known_peer
    tr
    inputs.client_ephemeral_secret
    (Usages.ephemeral_dh_usage inputs.client_session)
    (Terms.x25519_public inputs.server_ephemeral_secret)
    (Usages.ephemeral_dh_usage inputs.server_session);
  Lemmas.tls_dh_usage_known_peer
    inputs.client_session inputs.server_session

val handshake_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (handshake_secret inputs) ==
     schedule_secret_label tr inputs)
let handshake_secret_has_session_label tr inputs =
  early_secret_is_public tr;
  Lemmas.kdf_expand_label
    tr
    Terms.early_secret
    (Terms.hkdf_info
      0uy 32uy 13uy TLS13.Keys.label_derived 32uy
      (Terms.transcript_hash Terms.empty_transcript))
    32;
  shared_secret_has_session_label tr inputs;
  norm_spec
    [delta_only
      [`%handshake_secret;
       `%Terms.handshake_secret;
       `%Terms.derived_secret;
       `%Terms.derive_secret]]
    (DY.get_label tr (handshake_secret inputs));
  normalize_term_spec DY.get_label;
  DY.meet_public_label (schedule_secret_label tr inputs)

val master_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (master_secret inputs) ==
     schedule_secret_label tr inputs)
let master_secret_has_session_label tr inputs =
  handshake_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (handshake_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 13uy TLS13.Keys.label_derived 32uy
      (Terms.transcript_hash Terms.empty_transcript))
    32;
  norm_spec
    [delta_only
      [`%master_secret;
       `%Terms.master_secret;
       `%Terms.derived_secret;
       `%Terms.derive_secret;
       `%Terms.public_zero_secret;
       `%Terms.public_bytes]]
    (DY.get_label tr (master_secret inputs));
  normalize_term_spec DY.get_label;
  DY.meet_label_public (schedule_secret_label tr inputs)

val client_handshake_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (client_handshake_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
let client_handshake_traffic_secret_has_session_label tr inputs =
  handshake_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (handshake_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_c_hs_traffic 32uy
      (Terms.transcript_hash inputs.handshake_transcript))
    32

val server_handshake_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (server_handshake_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
let server_handshake_traffic_secret_has_session_label tr inputs =
  handshake_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (handshake_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_s_hs_traffic 32uy
      (Terms.transcript_hash inputs.handshake_transcript))
    32

val client_application_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (client_application_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
let client_application_traffic_secret_has_session_label tr inputs =
  master_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (master_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_c_ap_traffic 32uy
      (Terms.transcript_hash inputs.application_transcript))
    32

val server_application_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (server_application_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
let server_application_traffic_secret_has_session_label tr inputs =
  master_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (master_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_s_ap_traffic 32uy
      (Terms.transcript_hash inputs.application_transcript))
    32

val finished_key_has_label:
  tr:DY.trace ->
  traffic_secret:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.finished_key traffic_secret) ==
     DY.get_label tr traffic_secret)
let finished_key_has_label tr traffic_secret =
  Lemmas.kdf_expand_label
    tr traffic_secret
    (Terms.hkdf_info
      0uy 32uy 14uy TLS13.Keys.label_finished 0uy
      (Terms.public_bytes TLS13.Bytes.empty))
    32

val record_key_has_label:
  tr:DY.trace ->
  traffic_secret:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.record_key traffic_secret) ==
     DY.get_label tr traffic_secret)
let record_key_has_label tr traffic_secret =
  Lemmas.kdf_expand_label
    tr traffic_secret
    (Terms.hkdf_info
      0uy 32uy 9uy TLS13.Keys.label_key 0uy
      (Terms.public_bytes TLS13.Bytes.empty))
    32

val schedule_secret_term_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  Lemma
    (DY.get_label tr (schedule_secret_term kind inputs) ==
     schedule_secret_label tr inputs)
let schedule_secret_term_has_session_label tr inputs kind =
  match kind with
  | SharedSecret ->
    shared_secret_has_session_label tr inputs
  | HandshakeSecret ->
    handshake_secret_has_session_label tr inputs
  | ClientHandshakeTrafficSecret ->
    client_handshake_traffic_secret_has_session_label tr inputs
  | ServerHandshakeTrafficSecret ->
    server_handshake_traffic_secret_has_session_label tr inputs
  | ClientFinishedKey ->
    client_handshake_traffic_secret_has_session_label tr inputs;
    finished_key_has_label tr (client_handshake_traffic_secret inputs)
  | ServerFinishedKey ->
    server_handshake_traffic_secret_has_session_label tr inputs;
    finished_key_has_label tr (server_handshake_traffic_secret inputs)
  | MasterSecret ->
    master_secret_has_session_label tr inputs
  | ClientApplicationTrafficSecret ->
    client_application_traffic_secret_has_session_label tr inputs
  | ServerApplicationTrafficSecret ->
    server_application_traffic_secret_has_session_label tr inputs
  | ClientHandshakeRecordKey ->
    client_handshake_traffic_secret_has_session_label tr inputs;
    record_key_has_label tr (client_handshake_traffic_secret inputs)
  | ServerHandshakeRecordKey ->
    server_handshake_traffic_secret_has_session_label tr inputs;
    record_key_has_label tr (server_handshake_traffic_secret inputs)
  | ClientApplicationRecordKey ->
    client_application_traffic_secret_has_session_label tr inputs;
    record_key_has_label tr (client_application_traffic_secret inputs)
  | ServerApplicationRecordKey ->
    server_application_traffic_secret_has_session_label tr inputs;
    record_key_has_label tr (server_application_traffic_secret inputs)

val complete_lineage_identifies_schedule_target:
  schedule:Product.symbolic_key_schedule ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  target:DY.bytes ->
  Lemma
    (requires
      complete_key_schedule_lineage schedule inputs /\
      schedule_target_matches schedule kind target)
    (ensures target == schedule_secret_term kind inputs)
let complete_lineage_identifies_schedule_target
  schedule inputs kind target =
  match kind with
  | SharedSecret -> ()
  | HandshakeSecret -> ()
  | ClientHandshakeTrafficSecret -> ()
  | ServerHandshakeTrafficSecret -> ()
  | ClientFinishedKey -> ()
  | ServerFinishedKey -> ()
  | MasterSecret -> ()
  | ClientApplicationTrafficSecret -> ()
  | ServerApplicationTrafficSecret -> ()
  | ClientHandshakeRecordKey -> ()
  | ServerHandshakeRecordKey -> ()
  | ClientApplicationRecordKey -> ()
  | ServerApplicationRecordKey -> ()

val attacker_knowledge_implies_label_corruption:
  state:Product.product_state ->
  message:DY.bytes ->
  label:DY.label ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows state.Product.product_trace message /\
      DY.get_label state.Product.product_trace message == label)
    (ensures DY.is_corrupt state.Product.product_trace label)
let attacker_knowledge_implies_label_corruption state message label =
  Invariant.attacker_only_knows_publishable state message;
  DY.flow_to_public_eq state.Product.product_trace label

val attacker_knowledge_implies_ephemeral_compromise:
  state:Product.product_state ->
  inputs:key_schedule_inputs ->
  message:DY.bytes ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows state.Product.product_trace message /\
      DY.get_label state.Product.product_trace message ==
        schedule_secret_label state.Product.product_trace inputs)
    (ensures
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.client_ephemeral_secret) \/
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.server_ephemeral_secret))
let attacker_knowledge_implies_ephemeral_compromise state inputs message =
  attacker_knowledge_implies_label_corruption
    state message
    (schedule_secret_label state.Product.product_trace inputs);
  DY.is_corrupt_join
    state.Product.product_trace
    (DY.get_label
      state.Product.product_trace inputs.client_ephemeral_secret)
    (DY.get_label
      state.Product.product_trace inputs.server_ephemeral_secret)

val schedule_secret_secrecy:
  state:Product.product_state ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows
        state.Product.product_trace
        (schedule_secret_term kind inputs))
    (ensures
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.client_ephemeral_secret) \/
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.server_ephemeral_secret))
let schedule_secret_secrecy state inputs kind =
  schedule_secret_term_has_session_label
    state.Product.product_trace inputs kind;
  attacker_knowledge_implies_ephemeral_compromise
    state inputs (schedule_secret_term kind inputs)

val honest_peer_schedule_secret_secrecy:
  state:Product.product_state ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  client_label:DY.label ->
  server_label:DY.label ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      ephemeral_pair_has_labels
        state.Product.product_trace inputs client_label server_label /\
      DY.attacker_knows
        state.Product.product_trace
        (schedule_secret_term kind inputs))
    (ensures
      DY.is_corrupt state.Product.product_trace client_label \/
      DY.is_corrupt state.Product.product_trace server_label)
let honest_peer_schedule_secret_secrecy
  state inputs kind client_label server_label =
  schedule_secret_secrecy state inputs kind

val authenticated_client_schedule_secret_secrecy:
  state:Product.product_state ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  credential_label:DY.label ->
  client_label:DY.label ->
  server_label:DY.label ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      (DY.is_corrupt
         state.Product.product_trace credential_label \/
       ephemeral_pair_has_labels
         state.Product.product_trace inputs client_label server_label) /\
      DY.attacker_knows
        state.Product.product_trace
        (schedule_secret_term kind inputs))
    (ensures
      DY.is_corrupt state.Product.product_trace credential_label \/
      DY.is_corrupt state.Product.product_trace client_label \/
      DY.is_corrupt state.Product.product_trace server_label)
let authenticated_client_schedule_secret_secrecy
  state inputs kind credential_label client_label server_label =
  eliminate
    DY.is_corrupt state.Product.product_trace credential_label \/
    ephemeral_pair_has_labels
      state.Product.product_trace inputs client_label server_label
  returns
    DY.is_corrupt state.Product.product_trace credential_label \/
    DY.is_corrupt state.Product.product_trace client_label \/
    DY.is_corrupt state.Product.product_trace server_label
  with _. ()
  and _.
    honest_peer_schedule_secret_secrecy
      state inputs kind client_label server_label

val established_schedule_secret_secrecy:
  state:Product.product_state ->
  shadow:Product.endpoint_shadow ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  installed_secret:DY.bytes ->
  client_label:DY.label ->
  server_label:DY.label ->
  Lemma
    (requires
      Product.product_well_formed state /\
      Product.endpoint_member shadow state.Product.product_endpoints /\
      complete_key_schedule_lineage
        shadow.Product.shadow_key_schedule inputs /\
      schedule_target_matches
        shadow.Product.shadow_key_schedule kind installed_secret /\
      ephemeral_pair_has_labels
        state.Product.product_trace inputs client_label server_label /\
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows
        state.Product.product_trace installed_secret)
    (ensures
      Product.endpoint_refines state.Product.product_representation shadow /\
      (DY.is_corrupt state.Product.product_trace client_label \/
       DY.is_corrupt state.Product.product_trace server_label))
let established_schedule_secret_secrecy
  state shadow inputs kind installed_secret client_label server_label =
  Product.endpoint_member_refines
    state.Product.product_representation
    state.Product.product_endpoints
    shadow;
  complete_lineage_identifies_schedule_target
    shadow.Product.shadow_key_schedule inputs kind installed_secret;
  honest_peer_schedule_secret_secrecy
    state inputs kind client_label server_label

val shared_secret_secrecy:
  state:Product.product_state ->
  inputs:key_schedule_inputs ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows
        state.Product.product_trace (shared_secret inputs))
    (ensures
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.client_ephemeral_secret) \/
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.server_ephemeral_secret))
let shared_secret_secrecy state inputs =
  shared_secret_has_session_label state.Product.product_trace inputs;
  attacker_knowledge_implies_ephemeral_compromise
    state inputs (shared_secret inputs)

val handshake_secret_secrecy:
  state:Product.product_state ->
  inputs:key_schedule_inputs ->
  Lemma
    (requires
      DY.trace_invariant state.Product.product_trace /\
      DY.attacker_knows
        state.Product.product_trace (handshake_secret inputs))
    (ensures
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.client_ephemeral_secret) \/
      DY.is_corrupt
        state.Product.product_trace
        (DY.get_label
          state.Product.product_trace inputs.server_ephemeral_secret))
let handshake_secret_secrecy state inputs =
  handshake_secret_has_session_label state.Product.product_trace inputs;
  attacker_knowledge_implies_ephemeral_compromise
    state inputs (handshake_secret inputs)

let symbolic_key_separation (inputs:key_schedule_inputs) : prop =
  client_handshake_traffic_secret inputs =!=
    server_handshake_traffic_secret inputs /\
  client_handshake_traffic_secret inputs =!=
    client_application_traffic_secret inputs /\
  server_handshake_traffic_secret inputs =!=
    server_application_traffic_secret inputs /\
  client_application_traffic_secret inputs =!=
    server_application_traffic_secret inputs /\
  Terms.finished_key (client_handshake_traffic_secret inputs) =!=
    Terms.record_key (client_handshake_traffic_secret inputs) /\
  Terms.finished_key (server_handshake_traffic_secret inputs) =!=
    Terms.record_key (server_handshake_traffic_secret inputs) /\
  Terms.record_key (client_handshake_traffic_secret inputs) =!=
    Terms.record_iv (client_handshake_traffic_secret inputs) /\
  Terms.record_key (server_handshake_traffic_secret inputs) =!=
    Terms.record_iv (server_handshake_traffic_secret inputs) /\
  Terms.record_key (client_application_traffic_secret inputs) =!=
    Terms.record_iv (client_application_traffic_secret inputs) /\
  Terms.record_key (server_application_traffic_secret inputs) =!=
    Terms.record_iv (server_application_traffic_secret inputs)

val client_server_handshake_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_c_hs_traffic =!=
     Terms.tls13_label K.label_s_hs_traffic)
let client_server_handshake_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_hs_traffic) 6 == 0x63uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_hs_traffic) 6 == 0x73uy)

val client_handshake_application_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_c_hs_traffic =!=
     Terms.tls13_label K.label_c_ap_traffic)
let client_handshake_application_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_hs_traffic) 8 == 0x68uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_ap_traffic) 8 == 0x61uy)

val server_handshake_application_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_s_hs_traffic =!=
     Terms.tls13_label K.label_s_ap_traffic)
let server_handshake_application_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_hs_traffic) 8 == 0x68uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_ap_traffic) 8 == 0x61uy)

val client_server_application_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_c_ap_traffic =!=
     Terms.tls13_label K.label_s_ap_traffic)
let client_server_application_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_ap_traffic) 6 == 0x63uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_ap_traffic) 6 == 0x73uy)

val client_server_handshake_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (client_handshake_traffic_secret inputs =!=
     server_handshake_traffic_secret inputs)
let client_server_handshake_traffic_separated inputs =
  client_server_handshake_labels_distinct ();
  normalize_term_spec client_handshake_traffic_secret;
  normalize_term_spec server_handshake_traffic_secret;
  normalize_term_spec Terms.client_handshake_traffic_secret;
  normalize_term_spec Terms.server_handshake_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

val client_handshake_application_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (client_handshake_traffic_secret inputs =!=
     client_application_traffic_secret inputs)
let client_handshake_application_traffic_separated inputs =
  client_handshake_application_labels_distinct ();
  normalize_term_spec client_handshake_traffic_secret;
  normalize_term_spec client_application_traffic_secret;
  normalize_term_spec Terms.client_handshake_traffic_secret;
  normalize_term_spec Terms.client_application_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

val server_handshake_application_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (server_handshake_traffic_secret inputs =!=
     server_application_traffic_secret inputs)
let server_handshake_application_traffic_separated inputs =
  server_handshake_application_labels_distinct ();
  normalize_term_spec server_handshake_traffic_secret;
  normalize_term_spec server_application_traffic_secret;
  normalize_term_spec Terms.server_handshake_traffic_secret;
  normalize_term_spec Terms.server_application_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

val client_server_application_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (client_application_traffic_secret inputs =!=
     server_application_traffic_secret inputs)
let client_server_application_traffic_separated inputs =
  client_server_application_labels_distinct ();
  normalize_term_spec client_application_traffic_secret;
  normalize_term_spec server_application_traffic_secret;
  normalize_term_spec Terms.client_application_traffic_secret;
  normalize_term_spec Terms.server_application_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

val finished_record_key_separated:
  traffic_secret:DY.bytes ->
  Lemma
    (Terms.finished_key traffic_secret =!=
     Terms.record_key traffic_secret)
let finished_record_key_separated traffic_secret =
  assert_norm
    (Seq.index (B.of_list [0uy; 32uy; 14uy]) 2 == 14uy);
  assert_norm
    (Seq.index (B.of_list [0uy; 32uy; 9uy]) 2 == 9uy);
  normalize_term_spec Terms.finished_key;
  normalize_term_spec Terms.record_key;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

val record_key_iv_separated:
  traffic_secret:DY.bytes ->
  Lemma
    (Terms.record_key traffic_secret =!=
     Terms.record_iv traffic_secret)
let record_key_iv_separated traffic_secret =
  normalize_term_spec Terms.record_key;
  normalize_term_spec Terms.record_iv

val tls_symbolic_keys_are_separated:
  inputs:key_schedule_inputs ->
  Lemma (symbolic_key_separation inputs)
let tls_symbolic_keys_are_separated inputs =
  client_server_handshake_traffic_separated inputs;
  client_handshake_application_traffic_separated inputs;
  server_handshake_application_traffic_separated inputs;
  client_server_application_traffic_separated inputs;
  finished_record_key_separated
    (client_handshake_traffic_secret inputs);
  finished_record_key_separated
    (server_handshake_traffic_secret inputs);
  record_key_iv_separated
    (client_handshake_traffic_secret inputs);
  record_key_iv_separated
    (server_handshake_traffic_secret inputs);
  record_key_iv_separated
    (client_application_traffic_secret inputs);
  record_key_iv_separated
    (server_application_traffic_secret inputs)
