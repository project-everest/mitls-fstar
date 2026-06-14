# TLS 1.3 server design, proof, and implementation plan

## Authoritative status

This is the single authoritative plan for adding a verified TLS 1.3 server to
this repository. It covers the supported server profile, the pure
role-parametric state-machine design, the client/server derived-key agreement
theorem family, the server Pulse implementation strategy, the runtime/TCB
surface, and the validation checklist.

The plan is intentionally spec-first. Server Pulse handlers, drivers, and C
runtime work should not begin until the pure state machine has enough role
precision to state and prove the main client/server derived-key agreement
theorems. Once those theorems are settled, the Pulse implementation should be a
mostly mechanical refinement of the already-audited pure transitions, following
the existing client implementation structure.

## Implementation status

Current phase: **Phase 6 server buffer/event API and theorem surface**.

- [x] Single authoritative plan committed.
- [x] Superseded server/transcript planning docs removed.
- [x] First-milestone scope clarified:
  - KeyUpdate is deferred.
  - The first derived-key theorem uses a trusted `TLS13.Crypto.Spec` X25519
    agreement lemma.
  - `TLS13.Spec.ConnectionState` is refactored in place before considering a
    separate endpoint-state module.
  - Server credentials are supplied as in-memory PEM/DER buffers.
  - The top-level server `accept` mirrors the client driver's `connect` style
    and uses typed `TLS13.IO.listen_tcp`/`accept_tcp`.
- [x] Phase 0 baseline verification: `make verify` passes after the
  role-vocabulary changes and the proof-guidance assertion in
  `TLS13.Impl.Client.Types`.
- [ ] Phase 1 role-parametric pure state and role-correct key projections.
- [x] X25519 agreement lemma added at the crypto TCB boundary
  (`TLS13.Crypto.Spec.lemma_x25519_shared_agreement`).
- [x] Initial Phase 1 role/key vocabulary added:
  - `ServerEndpoint`;
  - `traffic_label`, `base_secret_id`, `derived_key_id`, and
    `key_derivation_checkpoint`;
  - role/direction-to-traffic-label mapping;
  - role-parametric expected traffic-secret helper with the existing client
    helper preserved as a `ClientEndpoint` wrapper.
- [x] Role-parametric record read/write key projection helpers added, with the
  existing client projections preserved as `ClientEndpoint` wrappers.
- [x] Client-compatibility and server traffic-label mapping lemmas added in
  `TLS13.ConnectionState.Lemmas`.
- [x] Additive pure `server_config` added to `connection_config`; existing
  client constructors explicitly set `config_server = None`.
- [x] Initial server handshake-stage constructors added, with low-level tag
  mappings; existing client stages and transitions are unchanged.
- [x] Optional server handshake selection artifacts added to `handshake_state`,
  including selected ClientHello, suite/group/signature scheme, random,
  key share, and credential identity.
- [x] Initial server local-event vocabulary added for parameter selection,
  CertificateVerify signing, and client Finished verification.
- [x] First server legal local transitions added:
  - `LocalStartServer` enters `HsAwaitingClientHello` from server config.
  - `LocalSelectServerParameters` records accepted ClientHello parameters and
    selected server artifacts.
- [x] `LocalDeriveSharedSecret` is role-aware for the initial server path,
  deriving from the selected server private key and accepted ClientHello key
  share.
- [x] Role-explicit traffic-key install event vocabulary and helpers added.
  Server install legality remains intentionally deferred until the surrounding
  server transition set and preservation lemmas are completed.
- [x] Role-parametric `model_record_keys_consistent_for_role` added, with a
  focused preservation lemma for role-explicit traffic-key installs. The legacy
  client invariant remains a `ClientEndpoint` wrapper.
- [x] Role-indexed connection-state record-key, layered-log, and full-log
  invariant packages added. The existing client-named packages remain
  `ClientEndpoint` wrappers, while new `_for_role` surfaces can state the same
  invariant for `ServerEndpoint`.
- [x] Existing client-only legal transitions are now explicitly gated by
  `ClientEndpoint`, and the server shared-secret path is explicitly gated by
  `ServerEndpoint`, preventing accidental server-config execution of client
  handshake/application transitions.
- [x] Added a role-parametric record-key preservation lemma for legal model
  steps under the endpoint role stored in the connection config.
- [x] Legacy client-named record-key, layered-log, full-log, replay, and
  trace-wrapper lemmas are now explicitly `ClientEndpoint`-guarded, so they
  cannot be applied accidentally to server-configured states.
- [x] `LocalInstallTrafficKeysForRole` is now genuinely role-parametric for
  config-role installs, allowing the server path to install its handshake
  traffic keys while preserving the legacy `LocalInstallTrafficKeys` client
  wrapper.
- [x] Role-indexed legal-delta preservation lemmas now cover record-key,
  layered-log, and full-log consistency through the endpoint role stored in the
  connection config.
- [x] Added the first network-visible server handshake transitions:
  received `ClientHello` appends exact transcript bytes and enters
  `HsClientHelloReceived`; sent `ServerHello` is checked against the selected
  server parameters, appends exact transcript bytes, is classified as cleartext
  raw TLS, and enters `HsServerHelloSent`.
- [x] Server handshake traffic-key installation is now staged after the
  transcript includes `ServerHello` (`HsServerHelloSent`), rather than at the
  pre-`ServerHello` ClientHello stage.
- [x] Added server encrypted-flight prefix transitions:
  sent empty-ALPN `EncryptedExtensions`, configured single-certificate
  `Certificate`, local `CertificateVerify` signing, and sent
  `CertificateVerify` now update the pure transcript and protected write-record
  projection under installed server handshake traffic keys.
- [x] Record-layer event projection is now endpoint-role indexed, with the
  legacy predicate name following the connection's configured role. This
  separates client `Finished` application-write switching from server
  `Finished` handshake-record advancement and enables server application-key
  installs after server `Finished`.
- [x] Added server `Finished` send and client `Finished` receive/verify pure
  transitions. Server `Finished` is verified against the server handshake
  traffic secret, appends exact transcript bytes, advances the protected
  handshake write record, and enters `HsServerFinishedSent`; received client
  `Finished` advances the protected handshake read record, and
  `LocalVerifyClientFinished` verifies against the client handshake traffic
  secret before appending the final handshake transcript bytes.
- [x] Added role-aware server application-key staging after server `Finished`:
  server application write keys install at `HsServerFinishedSent`, client
  application read keys install after receiving client `Finished`, and
  `LocalVerifyClientFinished` now requires both application record directions
  to match the key schedule before entering `ControlApplicationData`.
- [x] Added protected server application-data receive dispatch:
  `TLS13.Impl.Server.Network.process_network_bytes` now accepts decoded
  `LTlsApplicationData` records when the server is in application-data control,
  server-role client application read keys are installed, and the caller
  `app_out` buffer can hold the plaintext. The handler copies the delivered
  plaintext prefix, applies the role-parametric received-application-data
  mutation, preserves `server_end_to_end_invariant`, and extends the public
  consumed-prefix/read-key decode projection to the exact
  `received_application_data_state`.
- [x] Added protected server close_notify receive dispatch:
  close_notify model/mutation/query helpers are role-parametric with legacy
  client wrappers preserved, and `process_network_bytes` now accepts protected
  `LTlsAlert CloseNotify` records in application/closing control. The successful
  branch advances the server read record, enters `received_close_notify_state`,
  preserves the server invariant, and exposes the exact consumed prefix plus
  `ServerEndpoint` read-key provenance.
- [x] Added protected server non-close alert receive dispatch:
  `server_network_event_end_to_end_correct` now permits handled received TLS
  events to return `ConnectionFailed` as well as `StepOk`, while still excluding
  `NeedMoreInput`/`DecodeError`. Non-close `LTlsAlert` records now consume the
  protected record, enter `received_alert_failure_state`, preserve the server
  invariant, and return `ConnectionFailed`.
- [x] Added compatibility ChangeCipherSpec receive dispatch:
  cleartext `LTlsChangeCipherSpec` records are accepted while the server is in a
  handshaking control state, preserve the server invariant via
  `received_change_cipher_spec_state`, and expose the exact consumed prefix. CCS
  outside handshaking remains a zero-consume `IllegalTransition` refusal.
- [x] Added server decode-error state mutation:
  top-level parser failures now return zero-consume `DecodeError` after entering
  `LocalFail DecodeError`, while record-level parsed-buffer failures consume the
  decoded raw-record prefix and enter the same failed state. Both paths preserve
  the server invariant and expose the server `decode_error_response` theorem
  shape.
- [x] Application-data and close_notify legal message predicates are now
  endpoint-role aware. Server application sends use server application traffic,
  server application receives use client application traffic, and close_notify
  is legal for either endpoint role while KeyUpdate remains client-only/deferred
  for the first server milestone.
- [x] Added named transcript checkpoints (`TH_CH`, `TH_SH`, `TH_before_CV`,
  `TH_before_SF`, `TH_SF`, `TH_CF`), checkpoint-byte extraction from stored
  handshake messages, `same_transcript_checkpoint`, and
  `same_key_derivation_checkpoint`.
- [x] Added first-milestone derived-key material vocabulary:
  `key_checkpoint_for_derived_key`, expected traffic-secret/key/IV/Finished-key
  material from endpoint state, `derivation_inputs_agree`, and
  `peer_derived_key_material_agrees`.
- [x] Added the first pure derived-key agreement theorem
  `TLS13.ConnectionState.Lemmas.lemma_paired_endpoints_derived_key_agrees` for
  base secrets, handshake/application traffic secrets, AEAD keys/IVs, and
  Finished keys under the explicit first-milestone input-agreement predicate.
- [x] Added endpoint-pairing predicates for wire logs and X25519 key shares.
  `paired_x25519_key_shares` records the client/server public-share pairing,
  private/public correspondence, and both local X25519 shared-secret
  computations; `lemma_paired_x25519_key_shares_shared_secret_agree` derives
  shared-secret equality using the trusted crypto TCB agreement lemma.
- [x] Added supported-profile key-schedule lineage and the stronger theorem
  `lemma_paired_x25519_key_shares_derived_key_agrees`, which derives
  base-secret agreement from paired X25519 shares plus deterministic empty-PSK
  lineage before applying the first-milestone derived-key agreement theorem.
- [x] Repaired the existing Pulse client proof surface after the role gates:
  implementation readiness queries and mutation/model lemmas now expose
  `ClientEndpoint` exactly where legacy client-only transitions rely on it, and
  bounded full `make verify` passes.
- [x] Added pure record-material agreement vocabulary and theorem:
  `record_direction_material_matches_key_schedule_for_role`,
  `key_schedule_traffic_record_material_agrees`,
  `peer_record_material_inputs_agree`, `peer_record_material_agrees`, and
  `lemma_peer_record_material_agrees`. These prove the first-milestone
  cross-endpoint record key/IV shape: client write equals server read for
  `ClientTraffic`, and server write equals client read for `ServerTraffic`, once
  both endpoints project the installed traffic material for the same label.
- [x] Added `paired_handshake_events` and projection lemmas from paired
  checkpoint state to `same_transcript_checkpoint` and
  `same_key_derivation_checkpoint` for first-milestone key derivation points.
- [x] Started Phase 3 with `TLS13.Impl.Endpoint.Types`, a role-neutral
  extraction-facing status/response/buffer-response module. `TLS13.Impl.Client.Types`
  now includes that module and aliases the existing public client names to the
  shared shapes, preserving the client constructor/field namespace while giving
  the server API a shared base.
- [x] Started Phase 4 TCB specification:
  - `server_selection_acceptable` now pins the selected credential identity to
    the configured server credential identity.
  - `LocalSignCertificateVerify` legality now requires the CertificateVerify
    signature to verify over the exact `certificate_verify_input` for the
    current transcript hash and selected credential identity.
  - `TLS13.IO.fsti` now exposes typed `listener`, `listen_tcp`, `accept_tcp`,
    and `close_listener` resources for the planned server `accept`.
  - `TLS13.OpenSSL.fsti` now exposes typed in-memory server credential
    allocation/free and `sign_certificate_verify`, with a postcondition that a
    successful signature verifies as `RsaPssRsaeSha256` against the credential
    identity.
- [x] Added C shim support for the new Phase 4 TCB surface:
  `tls13_io_listen_tcp`/`tls13_io_accept_tcp` and the KaRaMeL listener ABI,
  plus OpenSSL-backed in-memory server credential allocation, RSA-PSS/SHA-256
  CertificateVerify signing, and credential free functions.
- [x] Started Phase 5 serializer support:
  - `TLS13.Wire.Spec` now has stable fixed-server serializer anchors for
    ServerHello, empty EncryptedExtensions, Certificate, CertificateVerify, and
    server Finished, all definitionally tied to `serialize_handshake`.
  - `TLS13.Impl.Serializer.fsti` exposes L-level fixed server handshake builders
    with exact emitted bytes and parse-back postconditions.
  - `c_stubs/tls13_connection_backend.h` implements matching C TCB helpers over
    concrete L-level server message storage.
  - The serializer TCB now also exposes
    `serialize_protected_handshake_record`, a generic protected handshake-record
    builder whose postcondition gives the outer `ApplicationData` parse,
    recursive raw-record segmentation, header-AAD bytes, and `Record.Spec.seal`
    equation for the supplied handshake fragment under the current write state.
- [x] Started Phase 6 with `TLS13.Impl.Server.Types`:
  server status/response aliases over shared endpoint response types,
  server-specific local action/payload vocabulary, `server_state_correct`,
  `server_end_to_end_invariant`, initial invariant lemmas, and first theorem
  predicates for server network/local buffer steps.
- [x] Added the first public server constructor path:
  `TLS13.Impl.ConnectionState.Repr.new_server` builds a `ServerEndpoint`
  initial connection state with ghost/spec server credential metadata, and
  `TLS13.Impl.Server.new_server` establishes `server_state_correct` and
  `server_end_to_end_invariant`.
- [x] Added the first read-only server action scheduler:
  `TLS13.Impl.Server.next_local_action` advertises `LocalStartServer` exactly
  when the concrete server is still `ControlNew` and the public
  `server_state_correct` invariant supplies the required server config.
- [x] Added the first server local mutation primitive:
  `TLS13.Impl.ConnectionState.LocalHandshake.try_start_server` performs the
  control-only `LocalStartServer` transition to `HsAwaitingClientHello` and
  proves the corresponding legal connection delta.
- [x] Added the first public server `process_local_event` slice for
  `LocalStartServer`. The wrapper requires the action selected by
  `next_local_action`, performs the verified `start_server` mutation, returns
  `StepOk` with zero network/app output, and proves
  `server_local_event_end_to_end_correct`.
- [x] Corrected the first server invariant package so it does not reuse the
  existing client-specific `connection_state_raw_to_message_replay_consistent`
  key-schedule replay subpackage. The server surface now exposes a
  server-local raw-message replay package over raw-event replay, protected raw
  segmentation, sent-seal replay, and received-decode replay; role-indexed
  key-schedule replay remains a later proof-hardening step.
- [x] Added the first verified server network receive slice for SNI-present
  `ClientHello`:
  - `TLS13.Impl.ConnectionState.Model.received_client_hello_state` mirrors the
    pure server receive transition, appending exact ClientHello handshake bytes
    to the transcript and raw receive log.
  - `TLS13.Impl.ConnectionState.Network.mark_received_client_hello` copies the
    parsed L-level ClientHello into server connection storage, records the exact
    handshake fragment, advances to `HsClientHelloReceived`, and proves the legal
    connection delta.
  - `TLS13.Impl.Server.process_client_hello` is a focused Pulse handler that
    copy-and-frees the parsed ClientHello, returns `StepOk` with zero output, and
    proves `server_network_event_end_to_end_correct` plus invariant
    preservation.
- [x] Added the first public buffer-oriented server `process_network_bytes`
  dispatcher. It calls the shared record decoder, accepts canonical
  SNI-present `ClientHello` records when the concrete server state is ready and
  the decoded fragment fits the stored ClientHello buffer, returns explicit
  zero-consume `NeedMoreInput`/`DecodeError`/`IllegalTransition` statuses for
  unsupported or overlarge inputs, preserves `server_end_to_end_invariant`, and
  exposes `server_network_bytes_end_to_end_correct`.
- [x] Strengthened the successful ClientHello byte-dispatch theorem surface:
  every `StepOk` result from `process_network_bytes` now exposes the exact
  `received_client_hello_state` post-state and proves that the stored raw
  ClientHello receive bytes equal the consumed input prefix
  `Seq.slice input 0 consumed_len`.
- [x] Added protected client `Finished` byte dispatch to the public server
  `process_network_bytes` path. The dispatcher now derives the parser/open
  projection for protected `Finished`, checks concrete server readiness with a
  new `can_receive_client_finished` query, calls the focused verified handler,
  and exposes the exact `received_client_finished_state` post-state plus the
  consumed-prefix raw-byte equality on successful `StepOk`.
- [x] Began factoring the oversized server Pulse implementation: receive-event
  handlers and public byte dispatch now live in
  `TLS13.Impl.Server.Network.fsti`/`.fst` behind a focused interface, while
  `TLS13.Impl.Server` keeps thin public wrappers. This preserves the verified
  theorem surface and cuts the top-level server implementation by roughly one
  thousand lines, following the client `Handle.*`/facade structure.
- [x] Started a focused `TLS13.Impl.Server.Keys.fsti`/`.fst` module for
  key-schedule-related server handlers. Shared-secret derivation and all current
  handshake/application traffic-key install handlers, both supplied-material and
  internally derived, now live behind that interface. `TLS13.Impl.Server`
  retains only public wrappers and explicit `connection_exactly` predicate
  rewrites for these key handlers.
- [x] Started a focused `TLS13.Impl.Server.Send.fsti`/`.fst` module for
  server send-flight handlers. The raw, serialized, and from-array
  `ServerHello` send transitions and the protected `EncryptedExtensions` send
  transition now live behind that interface. Certificate construction from
  credentials, certificate send transitions, and CertificateVerify send
  transitions are also factored there. Server Finished serialization/send is now
  factored there too, completing the main encrypted handshake-flight send
  cluster. The top-level server module keeps public forwarding wrappers and uses
  the Send helper from the credential-aware local dispatcher.
- [x] Added a focused `TLS13.Impl.Server.Auth.fsti`/`.fst` module for
  server authentication-side local handlers. CertificateVerify signing,
  stored client Finished verification, and the local unexpected-message helper
  now live behind that interface, with `TLS13.Impl.Server` keeping forwarding
  wrappers for the public handlers and local dispatcher.
- [x] Added a focused `TLS13.Impl.Server.Setup.fsti`/`.fst` module for
  server start and parameter-selection handlers. The top-level server module
  now delegates start-server and server-parameter selection through this
  interface.
- [ ] Continue Phase 6/7 by strengthening `process_network_bytes` from the first
  ClientHello path to the final dispatcher theorem: add consumed-prefix
  classification/projections and richer ClientHello/Finished reject deltas
  instead of the current state-preserving refusal cases.
- [x] Removed the immediate C parser backend blocker for that dispatcher:
  `c_stubs/tls13_connection_backend.h` now decodes canonical supported-profile
  `ClientHello` handshake records into `LClientHello`, matching the serializer
  order and profile for legacy version, one ChaCha20/Poly1305 suite, optional
  non-empty SNI, supported_groups X25519, signature_algorithms RSA-PSS-RSAE
  SHA-256, X25519 key_share, and TLS 1.3 supported_versions. The remaining
  dispatcher work is to expose the corresponding server-oriented
  parser/consumed-prefix theorem surface beyond the current invariant-preserving
  byte-step predicate.
- [x] Added `TLS13.Impl.ConnectionState.Queries.can_receive_client_hello`, the
  concrete readiness check needed by the upcoming buffer dispatcher. It reads
  only role/control, stored-ClientHello presence, and transcript length, and
  proves server role, `HsAwaitingClientHello`, no prior ClientHello, transcript
  room for the decoded fragment, and received-ClientHello `legal_event`.
- [x] Added the first server parameter-selection model/mutation slice:
  `TLS13.Impl.ConnectionState.Model.selected_server_parameters_state` records
  `hs_server_selection` after an accepted `ClientHello`, and
  `TLS13.Impl.ConnectionState.LocalHandshake.select_server_parameters` proves the
  corresponding `LocalSelectServerParameters` legal delta while preserving the
  existing no-private-material concrete storage. `connection_exactly` now also
  has a real server private-key-share storage predicate keyed by
  `hs_server_selection.server_key_share_private`, so a generated selector can
  later populate `Some server_sk` from concrete bytes. Executable
  random/key-share generation and scheduler readiness remain pending.
- [x] Added the focused public `TLS13.Impl.Server.process_select_server_parameters`
  wrapper. It exposes the verified `LocalSelectServerParameters` transition at
  the server API theorem surface, returns `StepOk` with zero network/app output,
  and proves `server_local_event_end_to_end_correct` under an explicit ghost
  `selection` precondition. This keeps the final executable selector and
  `next_local_action` scheduling gap visible rather than pretending that
  parameter generation is implemented.
- [x] Added focused public
  `TLS13.Impl.Server.process_select_default_server_parameters_from_arrays`
  wrapper. It constructs the supported-profile selection witness from the stored
  parsed `ClientHello`, the server config credential identity, and concrete
  32-byte server-random/public-key-share arrays, then reuses the verified
  selection transition. This removes the caller-built ghost-selection record for
  the default profile; the wrapper is now explicitly the no-private-material
  supplied-public-key path. Concrete random/X25519 generation that records
  `Some server_sk` and scheduler integration remain pending.
- [x] Added supplied-private-key server selection:
  `TLS13.Impl.ConnectionState.LocalHandshake.select_server_parameters_with_private_from_array`
  stores a concrete 32-byte private key into
  `handshake.server_key_share_private`, while
  `TLS13.Impl.Server.process_select_default_server_parameters_with_private_from_arrays`
  constructs the supported-profile selection with
  `server_key_share_private = Some server_sk`. Its precondition still requires
  `CM.can_select_server_parameters`, so public/private X25519 consistency is
  supplied by the pure selection admissibility predicate. Entropy generation and
  computing the public key from the private key inside the wrapper remain
  pending.
- [x] Added low-level executable server X25519 shared-secret derivation:
  `TLS13.Impl.ConnectionState.LocalHandshake.try_derive_server_shared_secret_from_private_array`
  reads the stored parsed `ClientHello` key share, computes X25519 with a
  concrete 32-byte server private-key array through the crypto runtime TCB, and
  reuses the verified shared-secret/key-schedule lineage mutation on success.
  Its theorem exposes the computed `TLS13.Crypto.Spec.x25519_shared` equation
  and the corresponding `LocalDeriveSharedSecret` legal delta. The public
  `TLS13.Impl.Server.process_derive_shared_secret_from_private_array` wrapper
  exposes this as `server_local_event_end_to_end_correct`; runtime X25519
  failure is mapped to the existing unexpected-message local failure response.
  Scheduler integration remains pending.
- [x] Added the first sent-ServerHello state-mutation slice:
  `TLS13.Impl.ConnectionState.Model.sent_server_hello_state` mirrors the pure
  `Sent ServerHello` transition, and
  `TLS13.Impl.ConnectionState.LocalHandshake.mark_sent_server_hello` records a
  caller-provided exact L-level ServerHello and handshake fragment, updates
  `hs_server_hello`, stores the exact ServerHello transcript bytes, advances to
  `HsServerHelloSent`, appends the raw sent bytes, and proves the legal
  connection delta. The final serializer-driven public output wrapper is still
  pending.
- [x] Added focused public `TLS13.Impl.Server.process_send_server_hello`. It
  exposes the sent-ServerHello mutation at the server API theorem surface under
  explicit exact raw/network-output and handshake-fragment preconditions, returns
  `StepOk` with the raw ServerHello output prefix, and proves
  `server_local_event_end_to_end_correct` for `LocalSendServerHello`.
- [x] Added the serializer-driven public
  `TLS13.Impl.Server.process_send_server_hello_serialized` wrapper. It takes the
  selected concrete L-level ServerHello, serializes the exact 95-byte cleartext
  TLS ServerHello record into `network_out`, serializes the exact 90-byte
  handshake fragment into an internal temporary buffer for transcript storage,
  reuses `mark_sent_server_hello`, and proves
  `server_local_event_end_to_end_correct` for `LocalSendServerHello` without
  caller-provided raw/fragment buffers. The L-level ServerHello is still supplied
  by the caller because executable server parameter selection and concrete
  selection storage remain pending.
- [x] Added
  `TLS13.Impl.Server.process_send_server_hello_from_arrays`, which builds the
  exact L-level ServerHello from concrete 32-byte server-random and public
  key-share arrays, fixes the supported cipher suite to
  `TLS_CHACHA20_POLY1305_SHA256`, reuses the serialized ServerHello send wrapper,
  and preserves `server_local_event_end_to_end_correct`. Concrete generation and
  persistent selection storage still remain pending, but callers no longer need
  to construct the L-level ServerHello record themselves.
- [x] Added extraction-facing pure model helpers for the rest of the first
  server encrypted flight:
  `sent_encrypted_extensions_state`, `sent_certificate_state`,
  `sent_certificate_verify_state`, `sent_server_finished_state`, their
  `can_send_*` predicates, and one-step evolution/legal-delta lemmas. These
  mirror the existing pure spec transitions, advance the write record sequence
  where appropriate, update the transcript/stored handshake artifacts, and give
  the future Pulse send mutations the same focused model surface as
  `sent_server_hello_state`.
- [x] Added the first encrypted-flight Pulse state mutation:
  `TLS13.Impl.ConnectionState.LocalHandshake.mark_sent_encrypted_extensions`
  stores an exact L-level EncryptedExtensions message, appends the exact
  handshake fragment to the transcript using the new reusable
  `copy_array_prefix_to_transcript` helper, advances the concrete write record
  sequence, moves to `HsServerEncryptedFlightSent`, appends the supplied raw
  sent bytes, and proves the `sent_encrypted_extensions_state` legal delta. A
  public server wrapper still requires the protected-record seal/serializer path
  so the end-to-end sent-seal replay invariant is not weakened.
- [x] Added the server Certificate Pulse state mutation:
  `TLS13.Impl.ConnectionState.LocalHandshake.mark_sent_certificate` stores an
  exact L-level Certificate message, extracts and caches the leaf DER from the
  concrete certificate chain buffer, appends the exact Certificate handshake
  fragment to the transcript, advances the concrete write record sequence,
  preserves the encrypted-flight control stage, appends the supplied raw sent
  bytes, and proves the `sent_certificate_state` legal delta. Like
  EncryptedExtensions, a public server wrapper is intentionally pending until the
  protected-record seal/serializer path can expose the sent-seal replay facts.
- [x] Added server CertificateVerify signing and send state mutations:
  `TLS13.Impl.ConnectionState.Model.signed_certificate_verify_state` mirrors
  `LocalSignCertificateVerify` by storing the signed CV, setting the verified
  flag, and caching the exact server CertificateVerify input for the current
  transcript hash. The Pulse mutation
  `TLS13.Impl.ConnectionState.LocalHandshake.mark_signed_certificate_verify`
  implements that local state update, and
  `mark_sent_certificate_verify` then appends the exact CV handshake fragment,
  advances the concrete write record sequence, appends the supplied raw sent
  bytes, and proves the `sent_certificate_verify_state` legal delta. Public
  wrappers remain pending on executable signing and protected-record
  seal/serializer support.
- [x] Added the server Finished Pulse state mutation:
  `TLS13.Impl.ConnectionState.LocalHandshake.mark_sent_server_finished` stores
  an exact L-level Finished message, appends the exact Finished handshake
  fragment to the transcript, advances the concrete write record sequence,
  moves to `HsServerFinishedSent`, appends the supplied raw sent bytes, and
  proves the `sent_server_finished_state` legal delta. A public wrapper remains
  pending until the protected-record seal/serializer path and executable
  Finished construction are connected.
- [x] Added server-side client Finished receive/verify state mutations:
  `TLS13.Impl.ConnectionState.Model.received_client_finished_state` and
  `verified_client_finished_state` expose the pure server path for receiving the
  client's protected Finished, then verifying it after application traffic keys
  are installed. `TLS13.Impl.ConnectionState.Network.mark_received_client_finished`
  stores the exact L-level Finished and advances the concrete read record
  sequence to `HsClientFinishedReceived`; `LocalAuth.mark_verified_client_finished`
  and `mark_verified_stored_client_finished` append the exact stored Finished
  bytes to the transcript and enter `ControlApplicationData`.
- [x] Added supplied-shared-secret derivation support:
  `TLS13.Impl.ConnectionState.LocalHandshake.derive_shared_secret_from_bytes`
  stores the shared, early, handshake, and master secrets in concrete key
  schedule storage and proves the generic `LocalDeriveSharedSecret` delta; the
  focused public `TLS13.Impl.Server.process_derive_shared_secret` wrapper exposes
  that transition at the server theorem surface. It currently assumes a supplied
  shared-secret buffer plus the pure `legal_event` premise; executable X25519
  derivation from stored server/client shares remains pending. Concrete
  allocation for a server private key-share slot now exists in
  `TLS13.Impl.ConnectionState.Repr.handshake_storage`, and
  `connection_exactly` now relates it to `hs_server_selection` when a private
  key is present. The supplied-private selector now populates that slot from a
  concrete private-key array, and the low-level server X25519 helper now derives
  the shared secret from that private-key array and the stored parsed
  `ClientHello` public share. The public response wrapper for that helper is
  now verified; entropy/public-key generation and scheduler integration remain
  pending.
- [x] Added role-indexed traffic-key install model support:
  `TLS13.Impl.ConnectionState.Model.installed_traffic_keys_for_role_state` and
  its evolution lemma mirror the pure `LocalInstallTrafficKeysForRole`
  transition. This is the model foundation needed for server read/write traffic
  key install mutations, since the older implementation helper is client-role
  specific.
- [x] Added supplied-material server handshake write-key installation:
  `TLS13.Impl.ConnectionState.LocalHandshake.install_server_handshake_write_traffic_keys_from_material`
  stores the server handshake traffic material, installs the concrete write
  record keys, and proves the role-indexed legal delta. The focused public
  `TLS13.Impl.Server.process_install_server_handshake_write_keys` wrapper proves
  `server_local_event_end_to_end_correct` for
  `LocalInstallServerHandshakeTrafficKeys`. The supplied-material wrapper is now
  complemented by an internally derived wrapper below, which derives the same
  material from the stored handshake secret and transcript.
- [x] Added supplied-material client handshake read-key installation for the
  server role:
  `TLS13.Impl.ConnectionState.LocalHandshake.install_client_handshake_read_traffic_keys_from_material`
  stores the client handshake traffic material, installs the concrete read
  record keys, and proves the role-indexed legal delta. The focused public
  `TLS13.Impl.Server.process_install_client_handshake_read_keys` wrapper proves
  `server_local_event_end_to_end_correct` for
  `LocalInstallClientHandshakeTrafficKeys`. The supplied-material wrapper is now
  complemented by an internally derived wrapper below, which derives the same
  material from the stored handshake secret and transcript.
- [x] Added internal derivation wrappers for server handshake traffic keys:
  `derive_and_install_server_handshake_write_traffic_keys` and
  `derive_and_install_client_handshake_read_traffic_keys` compute the traffic
  secret from the stored handshake secret and exact transcript hash, derive the
  record key/IV, install the appropriate concrete record direction, and prove
  the role-indexed legal delta. Public wrappers
  `process_derive_and_install_server_handshake_write_keys` and
  `process_derive_and_install_client_handshake_read_keys` expose those steps at
  the server theorem surface. These wrappers remove the supplied-material gap
  for handshake traffic keys; readiness scheduling and application traffic-key
  derivation remain pending.
- [x] Integrated derived handshake key installation into
  `TLS13.Impl.Server.next_local_action`: after `HsServerHelloSent`, the scheduler
  now advertises `LocalInstallServerHandshakeTrafficKeys` while the server
  handshake write material is absent, then
  `LocalInstallClientHandshakeTrafficKeys` while the client handshake read
  material is absent. `next_local_action_sound` exposes the exact control-stage,
  role, handshake-secret-present, and destination-slot-empty facts needed by the
  derived public wrappers.
- [x] Broadened the generic `TLS13.Impl.Server.process_local_event` dispatcher:
  `server_local_event_input_ready` now covers `LocalStartServer`,
  `LocalInstallServerHandshakeTrafficKeys`, and
  `LocalInstallClientHandshakeTrafficKeys`; it also covers
  `LocalInstallServerApplicationTrafficKeys` at `HsServerFinishedSent` and
  `LocalInstallClientApplicationTrafficKeys` at `HsClientFinishedReceived`. The
  dispatcher routes these key-install actions through the internally derived
  public wrappers while preserving `server_local_event_end_to_end_correct`.
  Other server local actions remain intentionally outside this generic
  dispatcher until their handlers are implemented.
- [x] The generic `process_local_event` dispatcher now also accepts
  `LocalDeriveSharedSecret` with a 32-byte payload for the existing
  supplied-shared-secret path. It routes through
  `process_derive_shared_secret` and proves
  `server_local_event_end_to_end_correct` with the payload identified as the
  derived shared secret. This is still the supplied-material path; executable
  server X25519 from stored private/client shares remains a later milestone.
- [x] Added supplied-material server application write-key installation:
  `TLS13.Impl.ConnectionState.LocalHandshake.install_server_application_write_traffic_keys_from_material`
  stores server application traffic material, installs the concrete application
  write record keys, and proves the role-indexed legal delta. The focused public
  `TLS13.Impl.Server.process_install_server_application_write_keys` wrapper
  proves `server_local_event_end_to_end_correct` for
  `LocalInstallServerApplicationTrafficKeys`.
- [x] Added supplied-material client application read-key installation:
  `TLS13.Impl.ConnectionState.LocalHandshake.install_client_application_read_traffic_keys_from_material`
  stores client application traffic material, installs the concrete application
  read record keys, and proves the role-indexed legal delta. The focused public
  `TLS13.Impl.Server.process_install_client_application_read_keys` wrapper proves
  `server_local_event_end_to_end_correct` for
  `LocalInstallClientApplicationTrafficKeys`.
- [x] Added internally derived server application write and client application
  read key installation. The mutations derive traffic secrets from the stored
  master secret and transcript hash, derive AEAD key/IV material, install the
  role-correct concrete record direction, and prove role-indexed legal deltas.
  The public wrappers
  `process_derive_and_install_server_application_write_keys` and
  `process_derive_and_install_client_application_read_keys` expose
  `server_local_event_end_to_end_correct`; `next_local_action` and generic
  `process_local_event` now schedule/dispatch the ready application key installs.
- [x] Wired server-side client Finished verification into the public theorem
  surface and generic local dispatcher. `process_verify_client_finished` now
  verifies the stored client Finished witness, calls the `LocalAuth`
  state mutation, and proves `server_local_event_end_to_end_correct` for
  `LocalVerifyClientFinished`; `server_local_event_input_ready` exposes the
  exact stored-Finished and `can_verify_client_finished` facts required by that
  wrapper.
- [x] Added the first protected encrypted-flight public wrapper:
  `TLS13.Impl.Server.process_send_encrypted_extensions_serialized` constructs
  the fixed empty-ALPN EncryptedExtensions fragment, seals it as one protected
  `ApplicationData` record with the current server handshake write state, stores
  the L-level message through `mark_sent_encrypted_extensions`, and proves
  `server_local_event_end_to_end_correct` including protected segmentation,
  seal projection, and server write-key-schedule projection.
- [x] Added the protected server Finished public wrapper:
  `process_send_server_finished_serialized` derives the Finished verify_data from
  the stored server handshake traffic secret and exact current transcript hash,
  builds the L-level Finished, serializes the exact 36-byte handshake fragment,
  seals it as one protected `ApplicationData` record, stores it through
  `mark_sent_server_finished`, and proves `server_local_event_end_to_end_correct`
  including server-role write-key-schedule projection.
- [x] Added the protected server Certificate public wrapper:
  `process_send_certificate_serialized` serializes the supplied exact L-level
  certificate message into a caller-sized scratch fragment, seals it as one
  protected `ApplicationData` record, stores it through `mark_sent_certificate`,
  and proves `server_local_event_end_to_end_correct` including leaf-DER caching,
  protected segmentation, seal projection, and server-role write-key-schedule
  projection.
- [x] Added the protected server CertificateVerify public wrapper:
  `process_send_certificate_verify_serialized` serializes the supplied exact
  signed L-level CertificateVerify message into a caller-sized scratch fragment,
  seals it as one protected `ApplicationData` record, stores it through
  `mark_sent_certificate_verify`, frees the transient L-level object, and proves
  `server_local_event_end_to_end_correct` including protected segmentation, seal
  projection, and server-role write-key-schedule projection.
- [x] Started protected-flight generic local dispatch:
  `server_local_event_input_ready` and the generic
  `TLS13.Impl.Server.process_local_event` now cover
  `LocalSendEncryptedExtensions` and `LocalSendServerFinished` through the
  self-contained protected serializers. Exact-size output buffers take the
  proved send path; incorrectly sized buffers produce a verified
  `IllegalTransition`/unexpected-message local-fail response. Certificate and
  CertificateVerify remain focused-wrapper-only until executable credential
  selection/signing supplies their concrete L-level inputs.
- [x] Added the focused executable server CertificateVerify signing wrapper:
  `process_sign_certificate_verify` takes an explicit
  `TLS13.OpenSSL.server_credentials` resource, hashes the current transcript,
  builds the exact TLS 1.3 server CertificateVerify input, asks the OpenSSL TCB
  to produce an RSA-PSS/SHA-256 signature, builds the corresponding L-level
  CertificateVerify object, stores it through `mark_signed_certificate_verify`,
  and proves `server_local_event_end_to_end_correct` for
  `LocalSignCertificateVerify`. The credential resource is preserved; signer
  failure is surfaced as a verified local unexpected-message failure.
- [x] Added the stored CertificateVerify protected-send wrapper:
  `TLS13.Impl.ConnectionState.LocalHandshake.serialize_stored_certificate_verify_fragment`
  borrows the L-level CertificateVerify already owned by the server handshake
  state and serializes the exact handshake fragment without consuming the slot;
  `TLS13.Impl.Server.process_send_stored_certificate_verify_serialized` then seals
  that stored fragment as one protected `ApplicationData` record, stores the send
  through `mark_sent_certificate_verify`, and proves
  `server_local_event_end_to_end_correct` without requiring a duplicate
  caller-owned L-level CertificateVerify.
- [x] Wired stored CertificateVerify sends into generic local dispatch:
  `TLS13.Wire.Spec.lemma_serialize_certificate_verify_from_signature_len` and
  `TLS13.Impl.ConnectionState.Queries.get_certificate_verify_signature_snapshot`
  expose the stored signature length without consuming the handshake slot; the
  generic `process_local_event` branch for `LocalSendCertificateVerify` now
  computes the exact protected-record output length at runtime, calls the stored
  sender when the caller buffer is exactly sized, and otherwise returns the
  verified local unexpected-message failure path.
- [x] Added scheduler readiness for the first protected server flight message:
  `TLS13.Impl.ConnectionState.Queries.can_send_encrypted_extensions_runtime`
  exposes the concrete read-only server send facts for empty-ALPN
  EncryptedExtensions, and `TLS13.Impl.Server.next_local_action` now advertises
  `LocalSendEncryptedExtensions` after both handshake-key install hints and before
  later application-key hints. `next_local_action_sound` exposes the matching
  legal-event, transcript-room, write-sequence, role, stage, and server
  handshake-traffic-key facts required by generic local dispatch.
- [x] Added scheduler readiness for stored CertificateVerify sends:
  `TLS13.Impl.ConnectionState.Queries.can_send_certificate_verify_runtime`
  inspects the stored certificate, signed CertificateVerify object, verified
  flag, server handshake write keys, write sequence, and transcript room using
  the dynamic CertificateVerify serializer length. `next_local_action` now
  advertises `LocalSendCertificateVerify` when those facts hold, and
  `next_local_action_sound` exposes the exact readiness facts consumed by the
  generic stored-CertificateVerify dispatch branch.
- [x] Added the credential certificate-chain copyout TCB needed for executable
  Certificate sending: `TLS13.OpenSSL.copy_server_certificate_chain` preserves
  `is_server_credentials` and copies the exact credential certificate-chain bytes
  into a caller buffer when capacity permits. The C OpenSSL stub layer now
  retains and exposes those bytes through the KaRaMeL-facing wrapper, making the
  next step a verified L-level one-certificate `Certificate` builder rather than
  a ghost-only config lookup.
- [x] Added the verified L-level server Certificate builder:
  `TLS13.Impl.Server.build_certificate_from_credentials` copies the credential
  certificate-chain bytes into owned `IM.certificate_msg` storage, initializes a
  one-entry offset/length table, and proves
  `IM.is_valid_certificate_msg` for the pure certificate
  `{ chain = [credential_certificate_chain] }`, plus concrete length/count facts
  for the one-entry message. The OpenSSL copyout TCB now states that copyout
  failure means the output capacity was too small, so the focused send wrapper
  can rule out builder failure under the supported certificate-size bound.
- [x] Added the focused executable server Certificate send wrapper:
  `TLS13.Impl.Server.process_send_certificate_from_credentials` takes
  `TLS13.OpenSSL.server_credentials`, materializes the one-certificate
  `IM.certificate_msg`, uses the new pure wire lemma
  `TLS13.Wire.Spec.lemma_serialize_certificate_from_single_chain_len` to compute
  the exact `13 + certificate_len` handshake fragment length, and delegates to
  the existing protected `Certificate` send path. Its public postcondition is
  `server_local_event_end_to_end_correct` for `LocalSendCertificate`, preserving
  the credential resource and tying the sent certificate to the configured server
  certificate chain.
- [x] Made the first supported server certificate-size bound explicit:
  `Bounds.max_server_certificate_chain_len` is `16610`, the largest certificate
  chain that fits the current one-record protected Certificate path
  (`13 + certificate_len` handshake bytes plus the 17-byte AEAD expansion within
  a 16640-byte TLSInnerPlaintext limit). `new_server` now requires this bound,
  and `server_state_core_correct` preserves it through the immutable server
  config so schedulers and driver code can rely on it.
- [x] Added scheduler readiness for credential-backed Certificate sends:
  `TLS13.Impl.ConnectionState.Queries.can_send_certificate_runtime` checks the
  concrete phase, stored EncryptedExtensions, empty Certificate/leaf-DER slots,
  server handshake write keys, write-sequence advance, and a conservative
  transcript-room bound for the maximum supported certificate size. It proves the
  exact configured one-certificate legal send event, and
  `TLS13.Impl.Server.next_local_action` now advertises `LocalSendCertificate`
  between EncryptedExtensions and CertificateVerify. The generic no-credential
  `process_local_event` path remains intentionally unwired for Certificate; the
  credential-aware dispatcher handles this action through
  `process_send_certificate_from_credentials`.
- [x] Added scheduler readiness for ServerFinished:
  `TLS13.Impl.ConnectionState.Queries.can_send_server_finished_runtime` checks the
  encrypted-flight phase, verified CertificateVerify flag, server handshake write
  keys, write-sequence advance, and transcript room for the fixed 36-byte
  Finished handshake message. `next_local_action` now advertises
  `LocalSendServerFinished` after CertificateVerify and before application-key
  installation; generic `process_local_event` already dispatches this
  self-contained send path with exact 58-byte protected-record output.
- [x] Added scheduler readiness for CertificateVerify signing:
  `TLS13.Impl.ConnectionState.Queries.can_sign_certificate_verify_runtime` checks
  the concrete encrypted-flight phase, sent Certificate slot, empty
  CertificateVerify slot, and empty CertificateVerify-input cache.
  `next_local_action` now advertises `LocalSignCertificateVerify` between
  Certificate and CertificateVerify. The concrete scheduler fact deliberately
  omits the ghost-only credential/selection relation; the focused
  `process_sign_certificate_verify` wrapper still requires and proves the exact
  credential identity, selected RSA-PSS/SHA-256 scheme, generated input, and
  signature-validity facts.
- [x] Added the credential-aware local dispatcher:
  `server_local_event_input_ready_with_credentials` extends the ordinary local
  input predicate only for credential-backed Certificate and CertificateVerify
  signing actions. `process_local_event_with_credentials` preserves the
  credential resource, dispatches `LocalSendCertificate` through the
  credential-chain sender, dispatches `LocalSignCertificateVerify` through the
  signing wrapper, and delegates all other actions to the existing generic
  `process_local_event`, preserving `server_local_event_end_to_end_correct`.
- [x] Strengthened focused server wrapper postconditions for later chaining:
  `process_select_server_parameters`,
  `process_select_default_server_parameters_from_arrays`, and
  `process_derive_shared_secret` now expose the exact pure post-state
  constructor (`selected_server_parameters_state` or
  `derived_shared_secret_state`) in addition to
  `server_local_event_end_to_end_correct`.
- [x] Strengthened ServerHello send wrapper postconditions for later chaining:
  the raw-fragment, serializer-backed, and concrete-array ServerHello send
  entry points now expose `sent_server_hello_state`; the serializer-backed
  wrappers also expose exact cleartext ServerHello record bytes.
- [x] Strengthened encrypted-flight send wrapper postconditions for later
  chaining: EncryptedExtensions, Certificate, CertificateVerify, stored
  CertificateVerify, and server Finished send entry points now expose the exact
  pure send-state constructor they install. CertificateVerify signing remains at
  the existing end-to-end contract because the signature-bearing message is
  produced by the OpenSSL signing TCB rather than determined solely by pre-state.
- [x] Strengthened focused receive wrapper postconditions for later chaining:
  ClientHello and client Finished receive entry points now expose the exact pure
  received-state constructor in addition to
  `server_network_event_end_to_end_correct`.
- [x] Strengthened traffic-key installation and client-Finished verification
  wrapper postconditions for later chaining: supplied-material key installs
  expose exact `installed_traffic_keys_for_role_state` equality, internally
  derived key installs expose the exact installed state directly in the returned
  `connection_exactly` resource with the derived material witness, and
  `process_verify_client_finished` exposes `verified_client_finished_state` with
  the stored Finished witness.
- [x] Promoted focused server application-data and close_notify send wrappers to
  the public Pulse theorem surface. Their contracts preserve the existing
  end-to-end local-event theorem and, on successful sends, expose the exact
  `sent_application_data_state` or `sent_close_notify_state` plus the emitted
  raw network prefix.

## End goal

Build a verified TLS 1.3 server for the same narrow profile as the verified
client:

- TLS 1.3 only.
- X25519 key exchange.
- `TLS_CHACHA20_POLY1305_SHA256`.
- Certificate-based server authentication.
- First server credential scheme: `RsaPssRsaeSha256` (`0x0804`).
- No PSK, no 0-RTT, no HelloRetryRequest, no client authentication, no early
  data, and no resumption in the first implementation.
- Application data and close_notify are in scope for the first implementation.
- KeyUpdate is explicitly deferred until after the first handshake/application
  data server milestone.

The main proof target is two-layered:

1. **Local endpoint correctness**: each server API step preserves a
   calc-sample-style layered invariant from concrete raw buffers through parsed
   TLS records/messages, transcript and key schedule evolution, state-machine
   events, record keys, wire logs, and application-log projection.
2. **Client/server derived-key agreement**: for each supported protocol-derived
   key identified by a `derived_key_id`, paired client and server states derive
   equal peer read/write material when their derivation inputs agree.

## Non-goals for the first server milestone

The first server version should deliberately omit:

- PSK, 0-RTT, early data, and resumption.
- HelloRetryRequest.
- Client authentication.
- KeyUpdate.
- ALPN or non-empty EncryptedExtensions unless interop forces it.
- Multiple simultaneous accepted connections in one verified server object.
- A verified generic serializer for arbitrary TLS messages.
- A broad runtime C server that owns TLS scratch buffers or handshake polling.

## Current client and shared baseline

The current verified client path is the regression baseline. Every server
milestone must keep it green.

Shared or intended-to-be-shared layers:

| Layer | Reuse target | Server-specific work |
| --- | --- | --- |
| Pure messages | `TLS13.Messages`, most of `TLS13.Wire.Spec` | Strengthen server-side parse/serialize facts and ClientHello acceptability predicates. |
| Low-level messages | `TLS13.Impl.Messages` L-level message representations | Add construction/copy helpers only where needed for server messages. |
| Record layer | `TLS13.Record`, `TLS13.Record.Spec` | Prove role-correct server read/write projections. |
| Key schedule | `TLS13.Keys`, `TLS13.KeySchedule` | Add role-indexed traffic-label and derived-key theorem vocabulary. |
| Logs | `TLS13.ConnectionLog` raw sent/received streams and app projections | Add server trace projections and paired endpoint relations. |
| Parser | Existing TLS parser decodes ClientHello and other messages | Move role-neutral parse contracts out of client theorem modules where needed. |
| Serializer | Existing serializer hooks and C backend | Add fixed server builders with parse-back, transcript, and seal facts. |
| Pure connection model | `TLS13.Spec.ConnectionState` is currently client-shaped | Generalize roles, stages, key projections, transcript checkpoints, and endpoint pairing. |
| Pulse state | `TLS13.Impl.ConnectionState.Repr` is client-oriented but contains reusable storage patterns | Reuse storage where genuinely endpoint-neutral; add server credential/selection fields. |
| Driver pattern | Client driver retained-buffer, compaction, IO-history, and total-write patterns | Reuse for a single-connection server driver with listen/accept and signing. |
| TCBs | Crypto, AEAD, TCP read/write/close | Add typed listen/accept IO and server credential/signing TCBs. |

The client theorem surface that the server should mirror:

- extracted buffer/event API over a connection object;
- `process_network_bytes`-style network input step;
- `process_local_event`-style local action step;
- response predicates with exact network/app output slices;
- state correctness and end-to-end invariants;
- raw received decode and raw sent seal replay facts;
- record read/write key schedule projections;
- driver-level IO history relation for transport bytes versus protocol wire logs.

Current code anchors to preserve or factor:

- `src/spec/TLS13.Transcript.fst` defines `TLS13.Transcript.transcript` as raw
  bytes, with append and SHA-256 hash operations.
- `src/spec/TLS13.Spec.ConnectionState.fst` contains the client-shaped pure
  state machine, including `append_handshake_to_transcript`,
  `conn_event_transcript_delta`, `transcript_bytes_of_conn_events`,
  `connection_state_transcript_consistent`, `LocalDeriveSharedSecret`,
  `LocalInstallTrafficKeys`, `expected_traffic_secret`,
  `traffic_install_matches_key_schedule`, and
  `traffic_key_material_for_secret`.
- `src/spec/TLS13.Keys.fst` contains the deterministic schedule functions:
  `early_secret B.empty`, `handshake_secret early shared`, `master_secret
  handshake`, `client_handshake_traffic_secret`,
  `server_handshake_traffic_secret`, `client_application_traffic_secret`,
  `server_application_traffic_secret`, `derive_aead_key`, and
  `derive_aead_iv`.
- `TLS13.Crypto.Spec.fsti` exposes `x25519_public_from_private` and
  `x25519_shared`; the first server milestone should add a trusted X25519
  agreement lemma at this crypto TCB boundary.
- Existing implementation-facing surfaces to keep client-compatible include
  `TLS13.Impl.Client.fsti`, `TLS13.Impl.Client.Driver.fsti`,
  `TLS13.Impl.Client.Types`, `TLS13.Impl.Parser.fsti`, and
  `TLS13.Impl.Serializer.fsti`.

## Hard design principles

1. **Spec before implementation**: role-parametric pure state, transcript
   checkpoints, key-schedule projections, and paired endpoint theorems come
   before server Pulse handlers.
2. **One authoritative pure model**: do not build an unrelated duplicated server
   state machine. Endpoint-specific implementation modules are fine; endpoint-
   specific pure theorem vocabulary should be role-indexed where possible.
3. **Exact transcript bytes**: every handshake transition appends exactly
   `TLS13.Wire.Spec.serialize_handshake msg`, and named transcript checkpoints
   are proved from event logs.
4. **Role-correct traffic mapping**: endpoint role and record direction decide
   whether a read/write state uses client or server traffic labels.
5. **No vague key theorem**: key agreement is indexed by a derived-key
   identifier and follows the TLS 1.3 key-schedule dependency DAG.
6. **Small TCBs with typed postconditions**: crypto, OpenSSL credential/signing,
   parser/serializer C hooks, and TCP listen/accept stay behind narrow
   interfaces.
7. **Mechanical Pulse refinement**: once the pure spec is settled, each Pulse
   transition should prove that concrete state follows the pure transition and
   preserves the invariant.

## Supported server profile

First server version:

- Endpoint role: `ServerEndpoint`.
- Cipher suite: `TLS_CHACHA20_POLY1305_SHA256`.
- Group: X25519.
- Authentication: server certificate only.
- Credential scheme: `RsaPssRsaeSha256`.
- ClientHello acceptance requires:
  - TLS 1.3 supported versions extension;
  - offered `TLS_CHACHA20_POLY1305_SHA256`;
  - offered X25519 key share;
  - offered `RsaPssRsaeSha256`;
  - acceptable SNI according to server config, if an SNI policy is configured.
- Server flight:
  - cleartext `ServerHello` (focused raw/fragment wrapper and serialized
    95-byte record wrapper complete; concrete-array wrapper now builds the
    L-level ServerHello from server-random and public key-share bytes);
  - encrypted empty `EncryptedExtensions`;
  - encrypted `Certificate`;
  - encrypted `CertificateVerify`;
  - encrypted server `Finished`.
- Compatibility ChangeCipherSpec:
  - server does not send it in the first version;
  - receiving it may be tolerated during handshaking if it remains a small reuse
    of existing non-transcript CCS handling.
- Unsupported or malformed profile inputs must transition to explicit failure,
  not silently proceed.

## Role-parametric pure state-machine design

### Endpoint roles

The pure model should expose:

```fstar
type endpoint_role =
  | ClientEndpoint
  | ServerEndpoint
```

Role should flow into:

- connection configuration;
- handshake start/selection state;
- legal event predicates;
- record read/write key projections;
- transcript checkpoint predicates;
- raw/message replay consistency;
- endpoint theorem surfaces.

### Configuration

Client configuration retains:

- server name;
- trust store;
- validation time;
- offered cipher suites;
- offered signature schemes;
- client random/key-share generation inputs.

Server configuration adds:

- certificate chain bytes supplied to `new_server` as in-memory PEM or DER
  buffers;
- credential identity;
- allowed signature schemes;
- supported cipher suites;
- supported groups;
- optional SNI policy;
- signing TCB identity for RSA-PSS/SHA-256.

Private key bytes are an input to the server credential/signing TCB, not a pure
protocol artifact. The pure state should remember only the credential identity,
certificate chain bytes, selected signature scheme, and typed signing capability
facts needed to justify CertificateVerify.

### Handshake/session state

The pure handshake state should record enough information to audit transcript,
key-schedule, and pairing facts:

- ClientHello message and exact serialized bytes.
- ServerHello message and exact serialized bytes.
- Selected cipher suite.
- Selected group.
- Selected signature scheme.
- Client random and server random.
- Client X25519 public share.
- Server X25519 public share.
- Endpoint private key witness where needed for local shared-secret derivation
  predicates.
- Certificate chain and credential identity.
- CertificateVerify input and signature.
- Client and server Finished messages.
- Transcript bytes.
- Key schedule state.
- Handshake buffer/progress data needed by parsers and serializers.

### Server handshake stages

The exact constructors can change, but the model must distinguish at least:

| Stage | Required information |
| --- | --- |
| Awaiting ClientHello | Server config and no accepted client parameters. |
| ClientHello accepted | Parsed ClientHello, offered profile checked, selected suite/group/signature scheme recorded. |
| ServerHello sent | Server random/key share selected, ServerHello appended, `TH_SH` available. |
| Handshake keys installed | Server write and client read handshake traffic material installed role-correctly. |
| EncryptedExtensions sent | Empty EncryptedExtensions appended under server handshake write key. |
| Certificate sent | Certificate chain appended. |
| CertificateVerify signed/sent | CertificateVerify input is `certificate_verify_input(hash(TH_before_CV))`; signature appended. |
| Server Finished sent | Server Finished verify_data is computed over `TH_before_SF`; `TH_SF` available. |
| Application traffic secrets derived | Application traffic secrets are based on `TH_SF`; application use still blocked. |
| Client Finished received | Client Finished parsed under client handshake read key. |
| Client Finished verified | Client Finished MAC checked over `TH_SF`; connection may enter application data. |
| Application data | App data and close_notify according to supported profile; KeyUpdate is deferred. |
| Closing/Closed/Failed | Same close/failure discipline as client, role-correct for alerts and logs. |

### Server legal events

Add legal events for:

- receive `ClientHello`;
- select parameters and generate server random/key share;
- derive server-side X25519 shared secret;
- send `ServerHello`;
- install server handshake write key and client handshake read key;
- send `EncryptedExtensions`;
- send `Certificate`;
- sign/send `CertificateVerify`;
- send server `Finished`;
- derive/install server application write and client application read keys;
- receive client `Finished`;
- verify client `Finished`;
- send/receive application data;
- send/receive close_notify;
- fail with explicit TLS error.

Each legal event must specify:

- source stage/control state;
- required stored artifacts;
- pure functional state update;
- transcript delta, if any;
- raw sent/received delta, if any;
- record read/write sequence and epoch update;
- key schedule update;
- application log or pending application update;
- failure behavior for unsupported profile inputs.

## Transcript checkpoints

Transcript state is byte-oriented. Checkpoints must be named and proved from
event-log projections rather than inferred from control-state names.

| Checkpoint | Transcript contents | Key/proof use |
| --- | --- | --- |
| `TH_CH` | `ClientHello` | Server has accepted client parameters; not enough for handshake traffic. |
| `TH_SH` | `ClientHello || ServerHello` | Handshake traffic secrets. |
| `TH_before_CV` | through `Certificate` | CertificateVerify input. |
| `TH_before_SF` | through `CertificateVerify` | Server Finished verify_data. |
| `TH_SF` | through server `Finished` | Application traffic secrets and client Finished verification context. |
| `TH_CF` | through client `Finished` | Full handshake complete; not the base application traffic-secret context. |
| `TH_KU(label,n)` | traffic update generation point, later milestone | KeyUpdate agreement by label and generation. |

Client and server transcript update discipline:

- Client sends ClientHello; server receives the same ClientHello.
- Server sends ServerHello; client receives the same ServerHello.
- Server sends EncryptedExtensions, Certificate, CertificateVerify, and
  Finished; client receives the same messages in the same transcript order.
- Client sends Finished; server receives the same client Finished.
- Compatibility ChangeCipherSpec is non-transcript.
- Alerts, application data, tickets, and later KeyUpdate messages do not alter
  the handshake transcript.

Required lemmas:

- endpoint event-log consistency implies endpoint transcript consistency;
- paired handshake event logs imply equal transcript bytes at each checkpoint;
- equal transcript bytes imply equal transcript hashes;
- each Finished or CertificateVerify input uses the pre-message transcript hash
  required by TLS 1.3.

## Role-correct key schedule vocabulary

### Traffic labels

```fstar
type traffic_label =
  | ClientTraffic
  | ServerTraffic

let traffic_label_for_endpoint role dir =
  match role, dir with
  | ClientEndpoint, TrafficWrite -> ClientTraffic
  | ClientEndpoint, TrafficRead  -> ServerTraffic
  | ServerEndpoint, TrafficWrite -> ServerTraffic
  | ServerEndpoint, TrafficRead  -> ClientTraffic
```

The existing client projection must reduce to:

- client write handshake = client handshake traffic;
- client read handshake = server handshake traffic;
- client write application = client application traffic;
- client read application = server application traffic.

The server projection must prove:

- server write handshake = server handshake traffic;
- server read handshake = client handshake traffic;
- server write application = server application traffic;
- server read application = client application traffic.

### Derived key identifiers

```fstar
type base_secret_id =
  | EarlySecret
  | HandshakeSecret
  | MasterSecret

type derived_key_id =
  | BaseSecret of base_secret_id
  | TrafficSecret of traffic_epoch * traffic_label
  | TrafficKey of traffic_epoch * traffic_label
  | TrafficIV of traffic_epoch * traffic_label
  | FinishedKey of traffic_label
  | TrafficUpdateSecret of traffic_label * nat
  | ExporterMasterSecret
  | ResumptionMasterSecret
```

First theorem scope:

- `TrafficSecret (TrafficHandshake, ClientTraffic)`;
- `TrafficSecret (TrafficHandshake, ServerTraffic)`;
- `TrafficSecret (TrafficApplication, ClientTraffic)`;
- `TrafficSecret (TrafficApplication, ServerTraffic)`;
- `TrafficKey` and `TrafficIV` for those traffic secrets;
- `FinishedKey ClientTraffic`;
- `FinishedKey ServerTraffic`;

`TrafficUpdateSecret label n`, exporter secrets, and resumption master secrets
remain out of the first proof. Randomness, private keys, certificates,
PSK/0-RTT secrets, and unsupported key material are not part of the first
theorem family.

### Dependency DAG

The key agreement proof follows this dependency graph:

```text
paired X25519 key shares + X25519 agreement law
  -> same shared secret

same shared secret + empty PSK
  -> same early secret
  -> same handshake secret
  -> same master secret

same handshake secret + same TH_SH
  -> same client/server handshake traffic secrets
  -> same handshake AEAD key/IV
  -> same Finished keys

same master secret + same TH_SF
  -> same client/server application traffic secrets
  -> same application AEAD key/IV

same traffic secret generation n
  -> same traffic secret generation n+1
  -> same updated AEAD key/IV
```

The proof rule is:

```text
agreement on every input to a derivation
  implies agreement on that derived key material
```

This is not a simple linear induction over all keys. Application traffic-secret
agreement depends on master-secret agreement and transcript-hash agreement at
`TH_SF`; it does not directly depend on handshake AEAD key agreement except
through the separate proof that both endpoints reached the same authenticated
transcript.

## Endpoint pairing predicates

The two-party theorem needs pure predicates relating a client state and a server
state.

### Wire-log pairing

```fstar
paired_wire_logs client server =
  client.cs_wire_log.raw_sent == server.cs_wire_log.raw_received /\
  server.cs_wire_log.raw_sent == client.cs_wire_log.raw_received
```

This is the pure counterpart of the driver-level IO-history relation.

### Handshake-event pairing

```fstar
paired_handshake_events checkpoint client server
```

This should state that sent/received ClientHello, ServerHello,
EncryptedExtensions, Certificate, CertificateVerify, and Finished events are
paired up to the requested transcript checkpoint.

### X25519 key-share pairing

```fstar
paired_x25519_key_shares client server
```

Meaning:

- the client's sent public key share equals the server's parsed ClientHello key
  share;
- the server's sent public key share equals the client's parsed ServerHello key
  share;
- each public share corresponds to the endpoint's private key;
- both X25519 shared-secret computations are exposed:
  - `x25519_shared client_sk server_pub`;
  - `x25519_shared server_sk client_pub`.

The predicate should stop before silently asserting shared-secret equality. For
the first server milestone, equality must come from an explicit trusted
`TLS13.Crypto.Spec` X25519 agreement lemma, not from a bare theorem premise.

Suggested TCB lemma shape:

```fstar
val lemma_x25519_shared_agreement
  (client_sk:x25519_private)
  (server_sk:x25519_private)
  (client_pub:x25519_public)
  (server_pub:x25519_public)
  : Lemma
      (requires
        x25519_public_from_private client_sk == client_pub /\
        x25519_public_from_private server_sk == server_pub)
      (ensures
        x25519_shared client_sk server_pub ==
        x25519_shared server_sk client_pub)
```

The lemma lives at the existing crypto TCB boundary: F* proofs may rely on it,
but the audit must record that the X25519 Diffie-Hellman law is trusted.

### Key derivation checkpoint pairing

```fstar
same_key_derivation_checkpoint checkpoint client server
```

This says both endpoints are being compared at the same TLS key-schedule point.
It is not transcript equality.

Suggested checkpoint vocabulary:

```fstar
type key_derivation_checkpoint =
  | DeriveHandshakeTraffic
  | DeriveApplicationTraffic
  | DeriveTrafficUpdate of traffic_label * nat
```

`DeriveHandshakeTraffic` requires both endpoints to be at `TH_SH`.
`DeriveApplicationTraffic` requires both endpoints to be at `TH_SF`.
`DeriveTrafficUpdate label n` is reserved for the later KeyUpdate milestone and
will require both endpoints to have applied the same number of updates for the
same traffic label.

### Derivation input agreement

```fstar
derivation_inputs_agree key_id client server
```

This packages exactly the inputs required by the `derived_key_id`:

- supported profile agreement;
- shared-secret or base-secret agreement;
- transcript checkpoint and transcript-hash agreement;
- traffic label agreement;
- role/direction mapping;
- KeyUpdate generation count, in the later KeyUpdate milestone.

## Main pure theorem family

Final pure theorem shape:

```fstar
theorem_paired_endpoints_derived_key_agrees :
  key_id:derived_key_id ->
  client:connection_state ->
  server:connection_state ->
  Lemma
    (requires
      client_endpoint_consistent client /\
      server_endpoint_consistent server /\
      paired_endpoint_states_for_key key_id client server /\
      derivation_inputs_agree key_id client server)
    (ensures
      peer_derived_key_material_agrees key_id client server)
```

`peer_derived_key_material_agrees` should instantiate to:

- traffic-secret equality for `TrafficSecret`;
- AEAD key equality for `TrafficKey`;
- AEAD IV equality for `TrafficIV`;
- Finished-key equality for `FinishedKey`;
- updated traffic-secret equality for `TrafficUpdateSecret` in the later
  KeyUpdate milestone.

For record-layer use, lift this to:

```text
client write material for ClientTraffic == server read material for ClientTraffic
server write material for ServerTraffic == client read material for ServerTraffic
```

## Spec proof gates before implementation

Server Pulse implementation is blocked until these gates are complete.

### Gate 1: role clarity

Checklist:

- [x] `ClientEndpoint` and `ServerEndpoint` roles exist in the pure model.
- [x] Client configuration remains behaviorally unchanged.
- [x] Server configuration records supported suite/group/signature policy,
      credential identity, and certificate chain.
- [x] Read/write direction is never interpreted without endpoint role.
- [x] Client read/write key projections reduce to the existing client
      projections.
- [x] Server read/write key projections prove the correct traffic-label mapping.

### Gate 2: transcript precision

Checklist:

- [x] Every supported client and server handshake message transition appends exactly
      `serialize_handshake msg`.
- [ ] Non-transcript messages are explicitly non-transcript.
- [x] `TH_CH`, `TH_SH`, `TH_before_CV`, `TH_before_SF`, `TH_SF`, and `TH_CF`
      are named predicates/lemmas.
- [x] CertificateVerify input uses `hash(TH_before_CV)`.
- [x] Server Finished uses `hash(TH_before_SF)`.
- [x] Client Finished verification uses `hash(TH_SF)`.
- [x] Paired checkpoint state implies equal transcript bytes at each checkpoint.

### Gate 3: X25519/shared-secret boundary

Checklist:

- [x] `paired_x25519_key_shares` records both endpoints' public shares and the
      local private/public correspondence.
- [x] `TLS13.Crypto.Spec` exposes a trusted X25519 agreement lemma.
- [x] The derived-key theorem obtains shared-secret equality from
      `paired_x25519_key_shares` plus the X25519 agreement lemma.
- [x] The crypto TCB boundary is documented in the pure theorem and audit text.
- [x] Same shared secret implies same early, handshake, and master secrets for
      the supported empty-PSK profile.

### Gate 4: derived-key agreement

Checklist:

- [x] `derived_key_id` and `derivation_inputs_agree` are defined.
- [x] Handshake traffic-secret agreement is proved at `TH_SH`.
- [x] Application traffic-secret agreement is proved at `TH_SF`.
- [x] AEAD key/IV agreement is proved by deterministic derivation from traffic
      secret agreement.
- [x] Finished-key agreement is proved by deterministic derivation from the
      relevant traffic secret.
- [x] KeyUpdate agreement is explicitly out of first-milestone scope and tracked
      as later theorem work.
- [x] Out-of-scope derived keys are explicitly not claimed.

### Gate 5: record-material agreement

Checklist:

- [x] Endpoint record read/write projections expose installed key/IV material.
- [x] Client write equals server read for `ClientTraffic`.
- [x] Server write equals client read for `ServerTraffic`.
- [x] Record sequence/epoch consistency is preserved.
- [ ] Sent seal and accepted received decode replay use the agreed material.

## Phase-by-phase implementation plan

### Phase 0: baseline and naming

Checklist:

- [ ] Keep current client verification, extraction, and interop gates green.
- [ ] Choose module names:
      - shared endpoint proof vocabulary: `TLS13.Impl.Endpoint.Types`;
      - role-parametric pure state: refactor `TLS13.Spec.ConnectionState` in
        place first; introduce `TLS13.Spec.EndpointState` only later if the
        in-place refactor becomes too large;
      - server public API: `TLS13.Impl.Server.fsti` / `.fst`;
      - server theorem vocabulary: `TLS13.Impl.Server.Types.fst`;
      - server driver: `TLS13.Impl.Server.Driver.fsti` / `.fst`;
      - server credential TCB: `TLS13.ServerCredentials.fsti` or
        `TLS13.OpenSSL.Server.fsti`;
      - runtime wrapper: `runtime/tls13_server_driver.h` / `.c`.
- [ ] Record that KeyUpdate is deferred for the first server milestone.
- [ ] Record that the first key-agreement theorem uses a trusted X25519
      agreement lemma rather than a bare shared-secret equality premise.

Validation:

- [ ] `make verify`
- [ ] `make check-admits`
- [ ] `make extract-driver-bundle`
- [ ] `make test-extracted-client-driver-slice`
- [ ] `make test-openssl-echo`

### Phase 1: role-parametric pure state and invariants

Checklist:

- [x] Add `ServerEndpoint`.
- [x] Start refactoring `TLS13.Spec.ConnectionState` in place, preserving the existing
      client theorem surface throughout the migration.
- [x] Add server configuration fields.
- [x] Start replacing client-only start/session state with role-aware handshake
      data.
- [x] Add server handshake stages.
- [x] Add initial server local event vocabulary.
- [x] Add initial server legal event predicates and transitions.
- [ ] Add remaining server legal event predicates and transitions.
- [x] Generalize expected traffic secret by role, direction, epoch, and label.
- [x] Add role-parametric record read/write key projection helpers.
- [x] Add role-parametric record-key consistency helper and install
      preservation lemma.
- [x] Promote role-parametric record-key consistency into the full layered
      invariant.
- [x] Prove client projection compatibility for the initial role/key helpers.
- [x] Prove server traffic-label direction mapping for the initial role/key
      helpers.
- [x] Add endpoint-role guards to the existing client-only legal transitions.
- [x] Add role-parametric record-key preservation for legal model steps.
- [x] Add server received-`ClientHello` and sent-`ServerHello` pure network
      transitions, including transcript and raw cleartext classification.
- [x] Add server encrypted-flight prefix pure transitions through
      `CertificateVerify`.
- [x] Generalize record-layer event projection by endpoint role.
- [x] Add server `Finished` and client `Finished` pure transitions.
- [x] Add final server handshake-completion transition into
      `ControlApplicationData` after application keys are installed and client
      `Finished` verifies.
- [x] Add server application-data and close_notify pure legal transitions.
- [x] Add transcript checkpoint extraction helpers.
- [x] Add first derived-key agreement theorem surface.
- [x] Add X25519 key-share pairing predicate and shared-secret agreement lemma.
- [x] Bridge paired X25519 key shares to base-secret and derived-key agreement
      without a bare shared-secret/base-secret equality premise.
- [x] Preserve the legacy Pulse client implementation by threading explicit
      client-role facts through readiness queries, model lemmas, and mutation
      boundaries.
- [x] Generalize event-log, transcript, record-layer, key-schedule, raw replay,
      seal replay, decode replay, and application-log consistency.
- [x] Add transcript checkpoints and derivation-input extraction helpers.

Validation:

- [x] Existing client theorem modules still verify.
- [x] Full `make verify` passes after client-only transition role gates and
      implementation proof repair.
- [x] No client public API behavior changes.

### Phase 2: paired endpoint traces and derived-key theorem family

Checklist:

- [x] Define `paired_wire_logs`.
- [x] Define `paired_handshake_events`.
- [x] Define `paired_x25519_key_shares`.
- [x] Define `same_key_derivation_checkpoint`.
- [x] Define `derivation_inputs_agree`.
- [x] Add the trusted X25519 agreement lemma.
- [x] Prove transcript pairing up to each checkpoint from
      `paired_handshake_events`.
- [x] Prove base-secret agreement.
- [x] Prove traffic-secret agreement.
- [x] Prove AEAD key/IV and Finished-key agreement.
- [x] Prove peer record-material agreement.
- [x] Expose `lemma_paired_x25519_key_shares_derived_key_agrees` and
      `lemma_peer_record_material_agrees`.

Validation:

- [x] This phase verifies in pure/spec modules without server Pulse code.
- [x] The theorem scope lists supported and out-of-scope `derived_key_id` cases.

### Phase 3: shared endpoint/codec predicate refactor

Checklist:

- [x] Extract role-neutral response/status records from client theorem modules
      into a shared endpoint module.
- [ ] Extract role-neutral output-slice and parse/decode helper predicates.
- [ ] Keep client local events, client input well-formedness, and client
      invariants such as `local_input_wf`, `network_input_wf`,
      `client_state_correct`, `client_end_to_end_invariant`, `network_out`, and
      `app_out` in client theorem modules.
- [ ] Point parser and serializer contracts at shared endpoint predicates where
      appropriate.
- [ ] Keep exact consumed-prefix helpers such as `Pulse.Lib.Array.sub` /
      `return_sub` available to client and server drivers.
- [ ] Preserve public client API shape.

Validation:

- [ ] Client verification unchanged.
- [ ] Client extraction and interop unchanged.

### Phase 4: server credential and signing TCB

Checklist:

- [x] Define server credential identity and certificate-chain spec.
- [x] Relate credential identity to leaf public key and supported signature
      scheme.
- [x] Define typed signing postcondition for CertificateVerify.
- [x] Add Pulse/C interface for credential allocation/free from in-memory PEM or
      DER certificate-chain and private-key byte buffers.
- [x] Add signing function for server CertificateVerify input.
- [x] Keep private key bytes outside protocol logic.
- [ ] Do not make file-path loading part of the verified server API; any file IO
      wrapper must live outside the first verified API and feed in-memory bytes
      to `new_server`.
- [ ] Keep Finished HMAC verification outside this TCB.

Validation:

- [x] TCB interface exposes exact typed postconditions.
- [x] C stubs do not return success without establishing the typed postcondition.

### Phase 5: server serializers and codec support

Checklist:

- [ ] Add supported ClientHello acceptability lemmas.
- [x] Add ServerHello serialize/parse-back facts.
- [x] Add cleartext ServerHello record serialization facts, including exact
      raw-record bytes, `parse_record`, and `raw_records_exactly`.
- [x] Add empty EncryptedExtensions serialize/parse-back facts.
- [x] Add Certificate serialize/parse-back facts over configured chain.
- [x] Add CertificateVerify serialize/parse-back facts.
- [x] Add server Finished serialize/parse-back facts.
- [x] Expose exact bytes written and length bounds.
- [ ] Expose record header/AAD facts.
- [ ] Expose protected-record seal facts.
- [ ] Expose transcript-fragment equality for each handshake fragment.
- [x] Add or expose fixed server builders with stable names:
      `serialize_server_hello_from_selection`,
      `serialize_empty_encrypted_extensions`,
      `serialize_certificate_from_credential`,
      `build_server_certificate_verify_input`,
      `serialize_certificate_verify_from_signature`, and
      `serialize_server_finished`.
- [ ] Ensure contracts expose `TLS13.Wire.Spec.parse_record`,
      `TLS13.Record.Spec.seal`, and
      `TLS13.Handshake.Spec.certificate_verify_input(hash(transcript_before_cv))`
      facts where relevant. Fixed server handshake builders already expose
      `parse_tls_message` facts for the handshake fragments.
- [ ] Avoid broad generic serializers unless proof requires them.

Validation:

- [ ] Server serializer contracts are precise enough for transcript and raw-log
      proofs.

### Phase 6: server buffer/event API and theorem surface

Recommended API shape:

```text
new_server certificate_chain_bytes private_key_bytes server_config
next_local_action
process_network_bytes
process_local_event
```

Checklist:

- [x] Define `server_state_correct`.
- [x] Define `server_end_to_end_invariant`.
- [x] Define server response/status types.
- [x] Define server local event kinds.
- [x] Define `server_network_bytes_end_to_end_correct`.
- [x] Define `server_local_event_end_to_end_correct`.
- [x] Constructor establishes the server invariant.
- [ ] Network/local steps preserve the server invariant.
      Initial slices completed: `LocalStartServer`, focused SNI-present
      received `ClientHello`, first public `process_network_bytes` ClientHello
      dispatch, derived traffic-key installs, client Finished verification, and
      generic server application-data/close_notify sends; protected server
      application-data receive byte dispatch is also complete. The focused
      `LocalSelectServerParameters` wrapper also preserves the invariant and now
      has default-profile concrete-array entry points for both supplied-public
      and supplied-private selections. Server private-key-share storage is
      represented in `connection_exactly` and the supplied-private wrapper
      populates it; the low-level server X25519 helper computes the shared
      secret from concrete private bytes plus the stored ClientHello share, and
      the public response wrapper exposes the corresponding local step theorem.
      Random/public-key generation, remaining protected receive cases, and
      scheduler integration remain pending.
- [x] Emitted bytes expose raw-delta, parse-back, seal, and write-key provenance.
- [ ] Consumed bytes expose exact consumed prefix, parse/decode classification,
      open facts, and read-key provenance.
      The C parser backend now decodes canonical supported-profile
      `ClientHello` records and the first server `process_network_bytes` wrapper
      consumes accepted ClientHello prefixes. Its public theorem now exposes the
      exact successful post-state and proves the accepted ClientHello raw bytes
      equal `Seq.slice input 0 consumed_len`. The dispatcher now also accepts
      protected client `Finished`, derives its protected open/decode projection,
      and exposes the exact `received_client_finished_state` post-state with the
      same consumed-prefix equality. This is now centralized in the public
      theorem vocabulary as `server_network_consumed_prefix`,
      `server_network_step_ok_consumed_prefix`, and
      `server_network_consumed_input_projection`, so the public facade and
      focused network module share one receive-side projection predicate.
      The projection now also exposes accepted-message decode facts through
      `server_network_step_ok_received_decode_projection`; protected accepted
      receives use `server_protected_record_decode_correct`, which combines the
      protected open-to-message fact with the `ServerEndpoint` read-key schedule
      projection derived from the server invariant. Protected application-data
      receives now use the same projection, expose the exact
      `received_application_data_state`, and copy the accepted plaintext into the
      response `app_out` prefix. Protected close_notify receives likewise expose
      the exact `received_close_notify_state`, consumed prefix, and read-key
      provenance. Remaining work is to extend this toward the full client
      theorem shape with uniform parse/decode classification and rejected-input
      witnesses for all byte outcomes.
      First focused server receive slice completed for protected client
      `Finished`: `process_client_finished` preserves
      `server_network_event_end_to_end_correct`; the unified
      `process_network_bytes` dispatcher now derives the required protected
      parser/open projection from decoder postconditions before calling it.
- [ ] Server invariants expose facts needed to instantiate
      `theorem_paired_endpoints_derived_key_agrees` with a client state.

Validation:

- [ ] API postconditions are strong enough for the future top-level driver.
- [ ] The server theorem surface does not duplicate the pure key-agreement proof;
      it preserves the invariant needed to instantiate it.

### Phase 7: server state mutations and handlers

Checklist:

- [x] Create small `.fsti` boundaries for server state mutations.
      Initial boundaries cover server start, received ClientHello, and the
      ghost/spec-only server parameter-selection transition; subsequent
      boundaries cover supplied/internal key installs, encrypted-flight state
      mutations, client Finished receive, and stored client Finished
      verification.
- [x] Reuse shared helpers where endpoint-independent.
      `TLS13.Impl.ConnectionState.LocalSend.try_send_application_data` and
      `try_send_close_notify` are now endpoint-neutral for application write
      traffic and are reused by the generic server local dispatcher.
- [ ] Add network handlers:
      - ClientHello accept/reject;
      - compatibility CCS receive complete while handshaking;
      - client Finished receive/open dispatch complete;
      - application data receive/dispatch complete for protected records with a
        fitting `app_out` buffer;
      - close_notify alert receive/dispatch complete for protected records;
      - non-close alert receive/dispatch complete for protected records;
      - decode/decrypt errors enter `LocalFail DecodeError`, with zero-consume
        top-level parser failure and consumed record-level parse/decrypt failure.
- [ ] Add local handlers:
      - server random and key share generation (empty concrete storage for the
        future server private key-share slot is allocated; executable generation
        and spec linkage remain pending; default-profile selection can now be
        recorded from caller-supplied concrete server-random/public-key-share
        arrays);
      - cipher/group/signature selection;
      - shared-secret and traffic-secret derivation (supplied shared-secret
        wrapper and generic 32-byte-payload dispatcher complete; executable
        server X25519 remains);
      - handshake key installation (server write-key and client read-key
        supplied-material and internally derived mutations/wrappers, scheduler
        hints, and generic local dispatcher integration complete for handshake
        keys);
      - server flight emission (focused sent-ServerHello public wrapper,
        serializer-driven cleartext ServerHello record construction, protected
        EncryptedExtensions, Certificate, CertificateVerify, and server Finished
        public wrappers, pure model helpers, and Pulse state mutations for
        EncryptedExtensions, Certificate, CertificateVerify signing/send, and
        server Finished are complete; scheduler hints are complete for
        EncryptedExtensions, credential-backed Certificate, CertificateVerify
        signing, stored CertificateVerify, and ServerFinished; the credential
        certificate-chain copyout TCB, verified L-level one-certificate builder,
        public executable Certificate send wrapper, and concrete-array
        ServerHello builder/send wrapper are in place. Concrete generation and
        persistent selection-to-L-ServerHello storage remain pending);
      - client Finished verification (state mutation, focused receive wrapper,
        focused verify wrapper, and generic local dispatcher integration
        complete; full network parse/open dispatch for received client Finished
        remains pending);
      - application key installation (server write-key and client read-key
        supplied-material and internally derived mutations/wrappers, scheduler
        hints, and generic local dispatcher integration complete);
      - application data and close_notify (generic local dispatcher complete for
        server sends, including explicit unexpected-message failure on seal or
        output-buffer refusal; the verified handlers are factored behind the
        focused `TLS13.Impl.Server.App.fsti` boundary with the facade delegating
        through exact-state rewrites; the low-level model lemma, record mutation,
        and runtime readiness query for received application data are now
        role-parametric, which removes the previous client-only blocker for the
        server receive handler; the server network application-data dispatcher
        branch now accepts protected application data in application control,
        copies plaintext into `app_out`, preserves the server invariant, and
        exposes the exact consumed-prefix/read-key projection).
      - close_notify receive (the low-level model lemma, record mutation, and
        readiness query are now role-parametric with legacy client wrappers
        preserved; the server network alert dispatcher accepts protected
        close_notify in application/closing control, preserves the invariant, and
        exposes the exact consumed-prefix/read-key projection).
      - non-close alert receive (the existing alert-failure model/mutation path
        is reused by the server network dispatcher; protected non-close alerts
        now consume their record, enter `received_alert_failure_state`, preserve
        the invariant, and return `ConnectionFailed`).
      - compatibility CCS receive (cleartext CCS is now accepted while
        handshaking, records the received CCS event, preserves the invariant, and
        exposes the exact consumed-prefix projection; non-handshaking CCS remains
        a zero-consume refusal).
      - decode errors (top-level parser failures now fail the connection without
        consuming input; record-level parsed-buffer failures consume the decoded
        record prefix, fail the connection with `LocalFail DecodeError`, and
        preserve the server invariant).
- [ ] Add failure transitions:
      - unsupported cipher suite;
      - missing/unsupported X25519 key share;
      - unsupported or credential-incompatible signature scheme;
      - malformed ClientHello;
      - bad client Finished;
      - application data before client Finished;
      - short output buffer;
      - decode/decrypt failure.

Validation:

- [ ] Each handler proves it follows the pure transition.
- [ ] Each handler preserves server invariant.
- [ ] No broad catches or success-shaped fallbacks.

Status:

- [x] Initial SNI-present ClientHello accept handler proves the pure
      `Received ClientHello` transition and preserves `server_end_to_end_invariant`.
- [x] First public `process_network_bytes` path handles decoded canonical
      SNI-present ClientHello by calling the focused handler. It also returns
      explicit state-preserving `IllegalTransition` refusals for no SNI,
      overlarge ClientHello fragments, non-ready server states, and unsupported
      decoded message kinds, plus zero-consume `NeedMoreInput`/`DecodeError`
      statuses from the decoder.
- [x] Successful ClientHello byte dispatch now publishes the exact
      `received_client_hello_state` witness and the accepted consumed-prefix
      equality, so downstream server proofs can recover the stored raw receive
      bytes without re-opening the decoder proof.
- [x] Public `process_network_bytes` now handles protected client `Finished`
      records by deriving the decoder/open projection, checking
      `HsServerFinishedSent` readiness and client-handshake read-key presence,
      calling `process_client_finished`, and publishing the exact
      `received_client_finished_state` plus consumed-prefix equality.
- [x] Server network receive/byte-dispatch code has been split into
      `TLS13.Impl.Server.Network` with an `.fsti` boundary. `TLS13.Impl.Server`
      now delegates `process_client_hello`, `process_client_finished`, and
      `process_network_bytes` through explicit `connection_exactly` predicate
      rewrites, keeping the public API stable while shrinking the monolithic
      implementation.
- [x] Server shared-secret derivation has been split into
      `TLS13.Impl.Server.Keys`, establishing the next small-module boundary for
      traffic-key derivation and installation handlers.
- [x] Generic `process_local_event` now handles server
      `LocalSendApplicationData` and `LocalSendCloseNotify` through the shared
      endpoint-neutral `LocalSend` mutations. The server theorem surface now
      admits the same explicit `LocalFail unexpected_message` response shape as
      the client for send refusal, while successful protected sends prove raw
      segmentation, seal projection, and server-role write-key provenance.
- [x] Generic `process_local_event` now handles
      `LocalVerifyClientFinished` through the stored-Finished verification
      wrapper, preserving the server invariant and entering application-data
      control when the application record keys are installed and the client
      Finished verifies against the client handshake traffic secret.
- [x] Public `process_network_bytes` now handles protected application-data
      records after handshake completion. The branch derives the protected
      parser/open projection, checks endpoint-generic receive readiness plus
      concrete `app_out` capacity, calls the role-parametric receive mutation,
      copies the plaintext response prefix, and publishes the exact
      `received_application_data_state` with consumed-prefix equality and
      `ServerEndpoint` read-key provenance.
- [x] Public `process_network_bytes` now handles protected close_notify alert
      records after handshake completion or while already closing. The branch
      derives the protected parser/open projection, checks endpoint-generic
      close_notify readiness, calls the role-parametric close_notify mutation,
      and publishes the exact `received_close_notify_state` with consumed-prefix
      equality and `ServerEndpoint` read-key provenance.
- [x] Public `process_network_bytes` now handles protected non-close alert
      records by deriving the protected parser/open projection, calling the
      alert-failure mutation, and returning `ConnectionFailed` with the exact
      `received_alert_failure_state` post-state.
- [x] Public `process_network_bytes` now handles cleartext compatibility CCS
      while handshaking by calling `mark_received_change_cipher_spec` and
      publishing the exact `received_change_cipher_spec_state` with
      consumed-prefix equality.
- [x] Public `process_network_bytes` now handles decoder failures by calling the
      shared decode-error fail mutation. Parser-level failures consume zero
      bytes; record-level parse/decrypt failures consume the decoded raw-record
      prefix and return `DecodeError` from the exact `LocalFail DecodeError`
      post-state.
- [ ] Rich ClientHello reject/error deltas are still pending: no-SNI policy
      rejection, unsupported cipher/group/signature offers, malformed
      ClientHello consumed-prefix witnesses, and alert-producing failure paths.

### Phase 8: verified top-level server driver

Public driver target:

```text
new_server
accept bind_host bind_host_len port local_fuel fuel
send
receive
close
```

Checklist:

- [ ] `new_server` receives in-memory PEM/DER certificate-chain and private-key
      byte buffers, allocates the credential context, and allocates Pulse-owned
      protocol buffers.
- [ ] `accept` mirrors the client driver's `connect` style: it takes bind-host
      bytes, bind-host length, port, local-action fuel, and network fuel; it
      calls typed `TLS13.IO.listen_tcp` and `TLS13.IO.accept_tcp` internally,
      runs the TLS handshake to completion, closes the listener, and returns a
      connected server handle.
- [ ] The first public driver API does not take a pre-accepted channel or
      externally owned listener handle.
- [ ] `send`, `receive`, and `close` operate on one connected server handle.
- [ ] Driver owns retained receive buffer.
- [ ] Driver owns network output, application output, and signing scratch buffers.
- [ ] Driver maintains exact IO-history relation:
      - server transport sent bytes;
      - server transport received bytes;
      - protocol raw sent/received wire logs;
      - retained buffered read-ahead.
- [ ] Driver uses total-write `TLS13.IO.write` postconditions.
- [ ] Driver uses fueled loops for handshake/receive/close.
- [ ] C wrapper owns only handle/lifetime/error state.

Validation:

- [ ] No TLS scratch buffers owned by runtime C.
- [ ] No TLS handshake polling in runtime C.

### Phase 9: IO, runtime, extraction, and C TCBs

Checklist:

- [ ] Extend IO TCB with `listen_tcp`.
- [ ] Extend IO TCB with `accept_tcp`.
- [ ] Add listener close/free if listener state persists.
- [ ] Add server credential/signing C shim.
- [ ] Credential C shim accepts in-memory PEM/DER buffers; it does not load
      credential files by path in the first verified API.
- [ ] Use concrete C stub names such as
      `c_stubs/tls13_server_credentials_karamel.c`,
      `c_stubs/tls13_server_credentials_karamel.h`,
      `c_stubs/tls13_io_karamel.c`, and `tls13_io_stubs.c`, with
      `c_stubs/tls13_connection_backend.h` extended only for typed serializer
      hooks.
- [ ] Add extraction targets:
      - `extract-server-krml`;
      - `extract-server-bundle`;
      - `extract-server-driver-bundle`.
- [ ] Add test targets:
      - `test-extracted-server-driver-slice`;
      - `test-openssl-sclient`;
      - `test-verified-client-server`.
- [ ] Ensure generated symbols avoid POSIX collisions with `accept`, `listen`,
      `send`, and `close`.

Validation:

- [ ] C wrappers are small and typed.
- [ ] Generated ABI is authoritative.

### Phase 10: validation and audit

Checklist:

- [ ] Pure theorem gates pass.
- [ ] Server object allocation smoke test passes.
- [ ] Credential context creation/free smoke test passes.
- [ ] Serializer parse-back tests pass.
- [ ] Supported ClientHello accepted.
- [ ] Unsupported cipher suite rejected.
- [ ] Missing/unsupported X25519 key share rejected.
- [ ] Unsupported signature scheme rejected.
- [ ] Bad client Finished rejected.
- [ ] Application data before client Finished rejected.
- [ ] OpenSSL `s_client` connects to verified server.
- [ ] Application echo works.
- [ ] close_notify works.
- [ ] KeyUpdate is not accepted as a claimed first-milestone feature.
- [ ] Verified client connects to verified server.
- [ ] Pure paired-endpoint derived-key theorem instantiates on paired
      implementation states.
- [ ] Existing OpenSSL echo client test still passes.
- [ ] Existing client driver slice test still passes.
- [ ] `make verify` passes.
- [ ] `make check-admits` stays at zero.
- [ ] `make check-c-stubs` passes if C stubs are added.

Audit checklist:

- [ ] Supported profile and rejected features are explicit.
- [ ] Public server APIs and usage are documented.
- [ ] Server transcript sequence is documented.
- [ ] Role-correct key-schedule direction mapping is documented.
- [ ] Derived-key theorem names and supported scope are documented.
- [ ] Out-of-scope secrets are documented.
- [ ] X25519/shared-secret TCB boundary is documented.
- [ ] Server credential/signing TCB is documented.
- [ ] Parser/serializer C backend additions are documented.
- [ ] IO listen/accept TCB additions are documented.
- [ ] Runtime C owned code is documented and contains no protocol logic.
- [ ] Validation commands and interop evidence are documented.

## Suggested implementation order

1. Role-parametric pure state, endpoint roles, transcript checkpoints, and
   role-correct key-projection lemmas.
2. Endpoint pairing predicates and derived-key agreement theorem family.
3. Shared endpoint predicate refactor, preserving the client proof.
4. Server credential/signing spec and typed TCB.
5. Server serializer contracts and C backend hooks.
6. Public server buffer/event API and theorem surface.
7. Server state mutation modules and handlers.
8. Server buffer/event API implementation.
9. Verified top-level server driver.
10. Runtime C wrapper and extraction targets.
11. OpenSSL `s_client` interop.
12. Verified client-to-server interop with pure theorem instantiation.
13. Audit documentation updates.

## Proof hardening rules

- Verify `.fsti` before `.fst`.
- Keep public postconditions strong enough for downstream callers.
- No `admit()` or `assume_`.
- No broad C fallback that returns success without a typed TCB postcondition.
- No hidden weakening of parser/serializer contracts.
- No role-ambiguous key projection lemmas.
- No theorem that hides the source of shared-secret equality; derive it from
  `paired_x25519_key_shares` plus the trusted X25519 agreement lemma.
- No implementation phase before pure derived-key theorem gates.
- Keep transcript checkpoint lemmas named and small.
- Keep derived-key agreement lemmas indexed by `derived_key_id`.
- Follow the key-schedule dependency DAG.
- Preserve low rlimits by factoring role-parametric lemmas into small modules.
