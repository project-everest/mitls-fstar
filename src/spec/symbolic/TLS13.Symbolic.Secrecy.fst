module TLS13.Symbolic.Secrecy

(*
 * Symbolic TLS 1.3 key-schedule secrecy and constructor separation.
 *
 * The key schedule is rebuilt from symbolic ephemeral secrets and transcript
 * terms.  DY labels propagate through X25519 and HKDF constructors, so attacker
 * knowledge of a derived secret implies corruption of one ephemeral-secret
 * label.  Endpoint-installed secrets are covered only when callers supply
 * complete_key_schedule_lineage.  Likewise, endpoint-specific conclusions rely
 * on caller-supplied labels being tied to the intended non-public endpoints.
 * Separation is syntactic constructor disequality, not a computational
 * non-collision theorem about concrete cryptographic outputs.
 *)

module B = TLS13.Bytes
module DY = DY.Core
module Invariant = TLS13.Symbolic.Invariant
module K = TLS13.Keys
module Lemmas = TLS13.Symbolic.Lemmas
module Product = TLS13.Symbolic.Product
module Seq = FStar.Seq
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

(*
 * Symbolic sessions, ephemeral secrets, and transcript checkpoints from which
 * the modeled generation-zero key schedule is derived.
 *)
noeq
type key_schedule_inputs = {
  client_session: Terms.endpoint_session;
  server_session: Terms.endpoint_session;
  client_ephemeral_secret: DY.bytes;
  server_ephemeral_secret: DY.bytes;
  handshake_transcript: DY.bytes;
  application_transcript: DY.bytes;
}

(* Derive the symbolic X25519 shared secret from both ephemeral contributions. *)
let shared_secret (inputs:key_schedule_inputs) : DY.bytes =
  Terms.x25519_shared
    inputs.client_ephemeral_secret
    (Terms.x25519_public inputs.server_ephemeral_secret)

(* Derive the TLS handshake secret from the symbolic shared secret. *)
let handshake_secret (inputs:key_schedule_inputs) : DY.bytes =
  Terms.handshake_secret (shared_secret inputs)

(* Derive the TLS master secret from the symbolic handshake secret. *)
let master_secret (inputs:key_schedule_inputs) : DY.bytes =
  Terms.master_secret (handshake_secret inputs)

(* Derive the client handshake traffic secret at the handshake transcript. *)
let client_handshake_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.client_handshake_traffic_secret
    (handshake_secret inputs)
    inputs.handshake_transcript

(* Derive the server handshake traffic secret at the handshake transcript. *)
let server_handshake_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.server_handshake_traffic_secret
    (handshake_secret inputs)
    inputs.handshake_transcript

(* Derive the client application traffic secret at the application transcript. *)
let client_application_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.client_application_traffic_secret
    (master_secret inputs)
    inputs.application_transcript

(* Derive the server application traffic secret at the application transcript. *)
let server_application_traffic_secret
  (inputs:key_schedule_inputs)
  : DY.bytes =
  Terms.server_application_traffic_secret
    (master_secret inputs)
    inputs.application_transcript

(* Match installed traffic secret/key/IV fields to one derived symbolic secret. *)
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

(*
 * Tie every installed symbolic key-schedule field to the reconstructed lineage.
 *
 * This predicate is an explicit theorem premise; Product.endpoint_refines alone
 * relates representations but does not establish this derivation structure.
 *)
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

(*
 * Tie both ephemeral secrets to caller-supplied labels and endpoint-specific
 * ephemeral-DH usages.
 *)
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

(* Join the actual DY labels of the client and server ephemeral secrets. *)
let schedule_secret_label
  (tr:DY.trace)
  (inputs:key_schedule_inputs)
  : DY.label =
  DY.join
    (DY.get_label tr inputs.client_ephemeral_secret)
    (DY.get_label tr inputs.server_ephemeral_secret)

(* Enumerate all key-schedule secrets and derived Finished/record keys proved secret. *)
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

(* Select the canonical symbolic term for one schedule-secret kind. *)
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

(* State that an installed schedule field equals a selected target term. *)
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

(*
 * Establish the label of the fixed zero early secret.
 *
 * Requirement: none.
 * Guarantee: Terms.early_secret has the public label on any trace.
 *)
val early_secret_is_public:
  tr:DY.trace ->
  Lemma (DY.get_label tr Terms.early_secret == DY.public)
(* Normalize the public literal construction and simplify the label meet. *)
let early_secret_is_public tr =
  norm_spec
    [delta_only
      [`%Terms.early_secret;
       `%Terms.public_zero_secret;
       `%Terms.public_bytes]]
    (DY.get_label tr Terms.early_secret);
  normalize_term_spec DY.get_label;
  DY.meet_public_label DY.public

(*
 * Compute the X25519 shared-secret label.
 *
 * Requirement: none beyond the symbolic input terms.
 * Guarantee: its label is the join of both ephemeral-secret labels.
 *)
val shared_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (shared_secret inputs) ==
     schedule_secret_label tr inputs)
(* Apply the shared-X25519 label lemma to the two ephemeral secrets. *)
let shared_secret_has_session_label tr inputs =
  Lemmas.x25519_shared_label
    tr inputs.client_ephemeral_secret inputs.server_ephemeral_secret

(*
 * Establish the TLS shared-DH usage on the symbolic shared secret.
 *
 * Requirement: each ephemeral secret has its endpoint-specific DH usage.
 * Guarantee: shared_secret has Usages.shared_dh_usage.
 *)
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
(* Compose public-key and known-peer usage rules, then normalize TLS DH usage. *)
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

(*
 * Propagate the joined ephemeral label to the handshake secret.
 *
 * Requirement: none beyond symbolic constructor semantics.
 * Guarantee: handshake_secret has schedule_secret_label.
 *)
val handshake_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (handshake_secret inputs) ==
     schedule_secret_label tr inputs)
(* Combine public early-secret derivation with shared-secret label propagation. *)
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

(*
 * Propagate the joined ephemeral label to the master secret.
 *
 * Requirement: none.
 * Guarantee: master_secret has schedule_secret_label.
 *)
val master_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (master_secret inputs) ==
     schedule_secret_label tr inputs)
(* Derive from the handshake-secret label and public zero-secret extraction. *)
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

(*
 * Propagate the schedule label to the client handshake traffic secret.
 *
 * Requirement: none.
 * Guarantee: the selected traffic secret has schedule_secret_label.
 *)
val client_handshake_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (client_handshake_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
(* Apply HKDF label propagation from handshake_secret. *)
let client_handshake_traffic_secret_has_session_label tr inputs =
  handshake_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (handshake_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_c_hs_traffic 32uy
      (Terms.transcript_hash inputs.handshake_transcript))
    32

(*
 * Propagate the schedule label to the server handshake traffic secret.
 *
 * Requirement: none.
 * Guarantee: the selected traffic secret has schedule_secret_label.
 *)
val server_handshake_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (server_handshake_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
(* Apply HKDF label propagation from handshake_secret. *)
let server_handshake_traffic_secret_has_session_label tr inputs =
  handshake_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (handshake_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_s_hs_traffic 32uy
      (Terms.transcript_hash inputs.handshake_transcript))
    32

(*
 * Propagate the schedule label to the client application traffic secret.
 *
 * Requirement: none.
 * Guarantee: the selected traffic secret has schedule_secret_label.
 *)
val client_application_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (client_application_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
(* Apply HKDF label propagation from master_secret. *)
let client_application_traffic_secret_has_session_label tr inputs =
  master_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (master_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_c_ap_traffic 32uy
      (Terms.transcript_hash inputs.application_transcript))
    32

(*
 * Propagate the schedule label to the server application traffic secret.
 *
 * Requirement: none.
 * Guarantee: the selected traffic secret has schedule_secret_label.
 *)
val server_application_traffic_secret_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  Lemma
    (DY.get_label tr (server_application_traffic_secret inputs) ==
     schedule_secret_label tr inputs)
(* Apply HKDF label propagation from master_secret. *)
let server_application_traffic_secret_has_session_label tr inputs =
  master_secret_has_session_label tr inputs;
  Lemmas.kdf_expand_label
    tr
    (master_secret inputs)
    (Terms.hkdf_info
      0uy 32uy 18uy TLS13.Keys.label_s_ap_traffic 32uy
      (Terms.transcript_hash inputs.application_transcript))
    32

(*
 * Show that Finished-key derivation preserves its traffic-secret label.
 *
 * Requirement: none.
 * Guarantee: finished_key and traffic_secret have equal labels.
 *)
val finished_key_has_label:
  tr:DY.trace ->
  traffic_secret:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.finished_key traffic_secret) ==
     DY.get_label tr traffic_secret)
(* Apply the generic KDF-expand label theorem to the Finished HKDF info. *)
let finished_key_has_label tr traffic_secret =
  Lemmas.kdf_expand_label
    tr traffic_secret
    (Terms.hkdf_info
      0uy 32uy 14uy TLS13.Keys.label_finished 0uy
      (Terms.public_bytes TLS13.Bytes.empty))
    32

(*
 * Show that record-key derivation preserves its traffic-secret label.
 *
 * Requirement: none.
 * Guarantee: record_key and traffic_secret have equal labels.
 *)
val record_key_has_label:
  tr:DY.trace ->
  traffic_secret:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.record_key traffic_secret) ==
     DY.get_label tr traffic_secret)
(* Apply the generic KDF-expand label theorem to the record-key HKDF info. *)
let record_key_has_label tr traffic_secret =
  Lemmas.kdf_expand_label
    tr traffic_secret
    (Terms.hkdf_info
      0uy 32uy 9uy TLS13.Keys.label_key 0uy
      (Terms.public_bytes TLS13.Bytes.empty))
    32

(*
 * Uniform label theorem for every schedule_secret_kind.
 *
 * Requirement: none.
 * Guarantee: schedule_secret_term kind inputs has schedule_secret_label.
 *)
val schedule_secret_term_has_session_label:
  tr:DY.trace ->
  inputs:key_schedule_inputs ->
  kind:schedule_secret_kind ->
  Lemma
    (DY.get_label tr (schedule_secret_term kind inputs) ==
     schedule_secret_label tr inputs)
(* Case-analyze kind and compose the corresponding traffic/derived-key lemma. *)
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

(*
 * Identify an installed target with its canonical reconstructed schedule term.
 *
 * Requirement: complete_key_schedule_lineage and schedule_target_matches.
 * Guarantee: target equals schedule_secret_term kind inputs.
 *)
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
(* Case-analyze the selected field and reduce lineage/material equalities. *)
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

(*
 * Convert attacker knowledge of an exactly labeled term into label corruption.
 *
 * Requirement: invariant trace, attacker knowledge, and exact message label.
 * Guarantee: the supplied label is corrupt.
 *)
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
(* Convert knowledge to publishability, then use flow-to-public equality. *)
let attacker_knowledge_implies_label_corruption state message label =
  Invariant.attacker_only_knows_publishable state message;
  DY.flow_to_public_eq state.Product.product_trace label

(*
 * Split corruption of the joined schedule label into ephemeral compromises.
 *
 * Requirement: invariant trace, attacker knowledge, and message label equal to
 * schedule_secret_label.
 * Guarantee: corruption of the client or server ephemeral secret's actual label.
 *)
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
(* Corrupt the join, then apply DY.is_corrupt_join. *)
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

(*
 * Generic secrecy theorem for every reconstructed schedule secret.
 *
 * Requirement: invariant trace and attacker knowledge of the selected term.
 * Guarantee: one actual ephemeral-secret label is corrupt.
 *)
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
(* Establish the term's joined label and apply ephemeral-compromise splitting. *)
let schedule_secret_secrecy state inputs kind =
  schedule_secret_term_has_session_label
    state.Product.product_trace inputs kind;
  attacker_knowledge_implies_ephemeral_compromise
    state inputs (schedule_secret_term kind inputs)

(*
 * Restate schedule secrecy using caller-supplied endpoint labels.
 *
 * Requirement: invariant trace, ephemeral_pair_has_labels tying the supplied
 * labels to the terms, and attacker knowledge.
 * Guarantee: client_label or server_label is corrupt.
 *)
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
(* Instantiate schedule_secret_secrecy and rewrite by the supplied label ties. *)
let honest_peer_schedule_secret_secrecy
  state inputs kind client_label server_label =
  schedule_secret_secrecy state inputs kind

(*
 * Add an authentication disjunction to client-side schedule secrecy.
 *
 * Requirement: invariant trace; either credential-label corruption or valid
 * ephemeral label ties; and attacker knowledge.
 * Guarantee: credential, client ephemeral, or server ephemeral label corruption.
 *)
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
(* Split the authentication premise; the honest branch uses peer schedule secrecy. *)
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

(*
 * Secrecy theorem for a secret installed in a refined endpoint schedule.
 *
 * Requirement: endpoint membership/refinement, explicit complete lineage,
 * selected installed target, supplied ephemeral-label ties, invariant trace,
 * and attacker knowledge of installed_secret.
 * Guarantee: endpoint refinement plus corruption of one supplied endpoint label.
 *)
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
(* Select endpoint refinement, identify the installed term, then apply secrecy. *)
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

(*
 * Specialized secrecy theorem for the reconstructed X25519 shared secret.
 *
 * Requirement: invariant trace and attacker knowledge of shared_secret.
 * Guarantee: one actual ephemeral-secret label is corrupt.
 *)
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
(* Compute the shared-secret label and apply ephemeral-compromise splitting. *)
let shared_secret_secrecy state inputs =
  shared_secret_has_session_label state.Product.product_trace inputs;
  attacker_knowledge_implies_ephemeral_compromise
    state inputs (shared_secret inputs)

(*
 * Specialized secrecy theorem for the reconstructed handshake secret.
 *
 * Requirement: invariant trace and attacker knowledge of handshake_secret.
 * Guarantee: one actual ephemeral-secret label is corrupt.
 *)
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
(* Compute the handshake-secret label and apply ephemeral-compromise splitting. *)
let handshake_secret_secrecy state inputs =
  handshake_secret_has_session_label state.Product.product_trace inputs;
  attacker_knowledge_implies_ephemeral_compromise
    state inputs (handshake_secret inputs)

(*
 * Syntactic disequalities between role-, epoch-, and purpose-separated terms.
 *)
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

(*
 * Distinguish client and server handshake HKDF labels.
 *
 * Requirement: none. Guarantee: the encoded labels are syntactically unequal.
 *)
val client_server_handshake_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_c_hs_traffic =!=
     Terms.tls13_label K.label_s_hs_traffic)
(* Compare their differing client/server byte. *)
let client_server_handshake_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_hs_traffic) 6 == 0x63uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_hs_traffic) 6 == 0x73uy)

(*
 * Distinguish client handshake and application HKDF labels.
 *
 * Requirement: none. Guarantee: the encoded labels are syntactically unequal.
 *)
val client_handshake_application_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_c_hs_traffic =!=
     Terms.tls13_label K.label_c_ap_traffic)
(* Compare their differing handshake/application byte. *)
let client_handshake_application_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_hs_traffic) 8 == 0x68uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_ap_traffic) 8 == 0x61uy)

(*
 * Distinguish server handshake and application HKDF labels.
 *
 * Requirement: none. Guarantee: the encoded labels are syntactically unequal.
 *)
val server_handshake_application_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_s_hs_traffic =!=
     Terms.tls13_label K.label_s_ap_traffic)
(* Compare their differing handshake/application byte. *)
let server_handshake_application_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_hs_traffic) 8 == 0x68uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_ap_traffic) 8 == 0x61uy)

(*
 * Distinguish client and server application HKDF labels.
 *
 * Requirement: none. Guarantee: the encoded labels are syntactically unequal.
 *)
val client_server_application_labels_distinct:
  unit ->
  Lemma
    (Terms.tls13_label K.label_c_ap_traffic =!=
     Terms.tls13_label K.label_s_ap_traffic)
(* Compare their differing client/server byte. *)
let client_server_application_labels_distinct () =
  assert_norm
    (Seq.index (Terms.tls13_label K.label_c_ap_traffic) 6 == 0x63uy);
  assert_norm
    (Seq.index (Terms.tls13_label K.label_s_ap_traffic) 6 == 0x73uy)

(*
 * Separate client and server handshake traffic-secret constructors.
 *
 * Requirement: none. Guarantee: the two symbolic terms are unequal.
 *)
val client_server_handshake_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (client_handshake_traffic_secret inputs =!=
     server_handshake_traffic_secret inputs)
(* Reduce both derivations and use distinct encoded HKDF labels. *)
let client_server_handshake_traffic_separated inputs =
  client_server_handshake_labels_distinct ();
  normalize_term_spec client_handshake_traffic_secret;
  normalize_term_spec server_handshake_traffic_secret;
  normalize_term_spec Terms.client_handshake_traffic_secret;
  normalize_term_spec Terms.server_handshake_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

(*
 * Separate client handshake and application traffic-secret constructors.
 *
 * Requirement: none. Guarantee: the two symbolic terms are unequal.
 *)
val client_handshake_application_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (client_handshake_traffic_secret inputs =!=
     client_application_traffic_secret inputs)
(* Reduce both derivations and use distinct encoded HKDF labels. *)
let client_handshake_application_traffic_separated inputs =
  client_handshake_application_labels_distinct ();
  normalize_term_spec client_handshake_traffic_secret;
  normalize_term_spec client_application_traffic_secret;
  normalize_term_spec Terms.client_handshake_traffic_secret;
  normalize_term_spec Terms.client_application_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

(*
 * Separate server handshake and application traffic-secret constructors.
 *
 * Requirement: none. Guarantee: the two symbolic terms are unequal.
 *)
val server_handshake_application_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (server_handshake_traffic_secret inputs =!=
     server_application_traffic_secret inputs)
(* Reduce both derivations and use distinct encoded HKDF labels. *)
let server_handshake_application_traffic_separated inputs =
  server_handshake_application_labels_distinct ();
  normalize_term_spec server_handshake_traffic_secret;
  normalize_term_spec server_application_traffic_secret;
  normalize_term_spec Terms.server_handshake_traffic_secret;
  normalize_term_spec Terms.server_application_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

(*
 * Separate client and server application traffic-secret constructors.
 *
 * Requirement: none. Guarantee: the two symbolic terms are unequal.
 *)
val client_server_application_traffic_separated:
  inputs:key_schedule_inputs ->
  Lemma
    (client_application_traffic_secret inputs =!=
     server_application_traffic_secret inputs)
(* Reduce both derivations and use distinct encoded HKDF labels. *)
let client_server_application_traffic_separated inputs =
  client_server_application_labels_distinct ();
  normalize_term_spec client_application_traffic_secret;
  normalize_term_spec server_application_traffic_secret;
  normalize_term_spec Terms.client_application_traffic_secret;
  normalize_term_spec Terms.server_application_traffic_secret;
  normalize_term_spec Terms.derive_secret;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

(*
 * Separate Finished and record keys derived from one traffic secret.
 *
 * Requirement: none. Guarantee: the symbolic KDF terms are unequal.
 *)
val finished_record_key_separated:
  traffic_secret:DY.bytes ->
  Lemma
    (Terms.finished_key traffic_secret =!=
     Terms.record_key traffic_secret)
(* Compare differing HKDF-info label lengths and normalize the constructors. *)
let finished_record_key_separated traffic_secret =
  assert_norm
    (Seq.index (B.of_list [0uy; 32uy; 14uy]) 2 == 14uy);
  assert_norm
    (Seq.index (B.of_list [0uy; 32uy; 9uy]) 2 == 9uy);
  normalize_term_spec Terms.finished_key;
  normalize_term_spec Terms.record_key;
  normalize_term_spec Terms.hkdf_info;
  normalize_term_spec Terms.tls13_label

(*
 * Separate record key and record IV derivations from one traffic secret.
 *
 * Requirement: none. Guarantee: the symbolic KDF terms are unequal.
 *)
val record_key_iv_separated:
  traffic_secret:DY.bytes ->
  Lemma
    (Terms.record_key traffic_secret =!=
     Terms.record_iv traffic_secret)
(* Normalize the two distinct record-key and record-IV constructors. *)
let record_key_iv_separated traffic_secret =
  normalize_term_spec Terms.record_key;
  normalize_term_spec Terms.record_iv

(*
 * Prove the complete symbolic_key_separation conjunction.
 *
 * Requirement: none.
 * Guarantee: all role, epoch, and purpose disequalities in the predicate.
 *)
val tls_symbolic_keys_are_separated:
  inputs:key_schedule_inputs ->
  Lemma (symbolic_key_separation inputs)
(* Compose all traffic-label, Finished/record, and key/IV separation lemmas. *)
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
