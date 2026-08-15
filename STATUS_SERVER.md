# TLS server verification status

Status date: 2026-06-17.

## EverParse Merge Status (2026-06-17)

**Branch:** `tls_server_merge`  
**Status:** Phase 3 in progress (verification at 95%)

The `origin/main` branch has been merged, bringing EverParse/QuackyDucky integration for verified TLS message parsing. This eliminates client-side parser/serializer code from the TCB.

**Completed:**
- ✅ Phase 1: Merged origin/main with all conflicts resolved
- ✅ Phase 2: Built full EverParse toolchain (fstar.exe 77MB, krml 37MB, qd.exe 8.8MB)
- ✅ Generated 65+ TLS13.Wire.Generated.* modules from tls.qd.rfc
- ✅ Verified all generated modules
- ✅ Verified 140+ main codebase modules

**In Progress (Phase 3):**
- ⚠️ 2 temporary admits in TLS13.Impl.Parser.DecoderWF.fst (proofs broken by message type changes)
- 🔄 Full verification running
- ⏳ Interop tests pending

**Remaining:**
- Phase 4: Update documentation (TCB boundaries)
- Phase 5: Implement verified server parsers using generated combinators (8-16h estimated)

See MERGE_PHASE2_COMPLETE.md for detailed status.

## Goal

The end goal is a verified, interoperable TLS 1.3 client/server implementation for
the repository's first supported profile:

- TLS 1.3 only.
- X25519 key exchange.
- `TLS_CHACHA20_POLY1305_SHA256`.
- Certificate-based server authentication using `RsaPssRsaeSha256` or
  `EcdsaSecp256r1Sha256`, whichever the configured credential's key supports.
- No PSK, 0-RTT, HelloRetryRequest, client authentication, resumption, early
  data, or KeyUpdate in the first milestone.

## Parity with the client

The client has since moved past that first profile: it negotiates
`TLS_AES_128_GCM_SHA256` as well as ChaCha20-Poly1305, offers and completes
`secp256r1` as well as X25519, and reassembles a handshake message split across
several records.

The server now matches it on the first of the three: it selects
`TLS_AES_128_GCM_SHA256` when a peer does not offer ChaCha20-Poly1305, via the
deterministic policy `TLS13.Impl.ConnectionState.Model.server_selected_suite`
(prefer ChaCha20, fall back to AES-128-GCM), which is a function of the stored
ClientHello alone, so the ServerHello writer recovers the choice at runtime
rather than having it threaded through the driver.  `secp256r1` and cross-record
reassembly remain server-side gaps.

`secp256r1` is being closed in staged, capability-neutral steps against the
file-and-line plan in `docs/server-p256-plan.md`; the configured
`server_supported_groups` stays `[T.X25519]` until the last of them, so no stage
before that can move a matrix cell.  The first has landed: the server's
selection now carries a per-group keypair and its self-consistency invariant is
group-indexed rather than X25519-specific.  The second has landed too: the
concrete ClientHello mirror now carries a 65-byte secp256r1 key-share slot
alongside the X25519 one, so the remaining stages can fill it without further
structural churn.  Accepting a P-256-only ClientHello (widening the parser's
acceptance gate) was measured to be 169 `ch_extensions` occurrences of work
that buys no capability while the configured groups are X25519-only, so it was
deferred to the stage that actually turns the feature on.  The third has landed:
because an X25519 private key and a P-256 private key are both thirty-two bytes,
and a server runs exactly one ECDH, a single secret derives both publics -- so
the selection now carries a real secp256r1 keypair with no extra randomness and
no change to the driver's payload width.  The fourth and fifth landed together:
the *specification* is now fully group-parametric, recovering the group from the
ServerHello where one exists and from the selection where it does not, exactly
as the client already does.  The implementation still only ever selects X25519,
and now says so through a single named predicate,
`server_selection_group_pinned`, whose deletion is the switch that turns the
feature on in the final stage.

The server also echoes the offered `legacy_session_id` **verbatim**, as
RFC 8446 4.1.3 requires, rather than padding it to 32 bytes: the mirror carries
the id as a zero-padded 32-byte buffer plus an explicit width, and the
ServerHello is `90 + |sid|` bytes (its record `95 + |sid|`), sized at run time.
A peer with middlebox-compatibility mode off -- which sends an empty session id
-- therefore now connects.

Server credentials are no longer pinned to RSA-PSS.  The signature scheme the
server both *allows* and *signs under* is
`TLS13.Crypto.Spec.credential_signature_scheme` of the credential it was
configured with, so an ECDSA P-256 credential negotiates and signs
`ecdsa_secp256r1_sha256` while an RSA credential negotiates and signs
`rsa_pss_rsae_sha256` -- and either one correctly refuses an offer its own key
cannot satisfy.  The wire code written into CertificateVerify comes from the
same credential (`TLS13.OpenSSL.server_credential_signature_scheme`), so the
model-level scheme and the byte on the wire cannot drift.

`docs/server-client-parity.md` is the authoritative gap analysis and interop
test plan.  Two standing gates keep it honest:

- `make test-atlas-loopback` -- the verified client against the verified server.
  The only test in the tree whose ClientHello is the one ATLAS actually sends,
  so it is the gate that fails if the client's offer moves past what the server
  can select.
- `make test-server-matrix` -- the server's capability surface across cipher
  suites, key-exchange groups, signature schemes, the server's own credential
  (RSA or ECDSA P-256), middlebox-compatibility mode, record/TCP framing and
  protocol version.  Thirty-four cells with two-sided expectations: a cell
  recorded as a gap fails if it starts succeeding, so closing a gap must update
  the ledger.  Gaps claimed to be independent of an axis are recorded twice
  (`ecdsa-credential-p256-only`, `aes128-clienthello-across-two-records`) so
  that a fix which closes one only on one axis is visible as such.

Both are part of `make test`, and therefore of CI.

The proof goal has two connected layers.

1. **Spec-level agreement**: the role-parametric TLS state-machine spec should
   prove that paired client/server endpoints derive equal peer read/write key
   material for each supported derived key, provided their ClientHello,
   ServerHello, X25519 shares, transcript checkpoints, and key-schedule lineage
   agree.
2. **Pulse implementation conformance**: the extracted implementation should
   refine the spec from concrete raw network bytes through parsing,
   serialization, transcript evolution, record protection, IO logs, and local
   TLS state-machine events. The top-level server should expose a practical
   buffer/driver-oriented API with external network IO, and the extracted C
   server/client should interoperate on the supported profile.

## Current authoritative plan

`TLS_SERVER_DESIGN_AND_IMPL.md` is the authoritative plan. It supersedes the
older server/transcript planning documents.

## Committed verified status

The latest committed verified server-driver, client-driver, and pairing-theorem
baseline is:

```text
85c7e47 Clarify public-success pairing theorem name
```

At that point the full gate had passed:

```text
git --no-pager diff --check
make check-admits
make verify
make test-extracted-client-driver-slice
make test-extracted-server-driver-slice
make test-openssl-echo
make test-openssl-sclient
```

That committed state includes:

- A role-parametric pure TLS state machine with server role/configuration,
  server handshake stages, server local/network event vocabulary, and server
  transitions through ServerHello, the encrypted server flight, Finished,
  application key installation, application data, alerts, and close_notify.
- Spec-level derived-key agreement vocabulary and theorems in
  `src/spec/TLS13.ConnectionState.Lemmas.fst`, including:
  - `lemma_paired_endpoints_derived_key_agrees`;
  - `lemma_paired_x25519_key_shares_shared_secret_agree`;
  - `lemma_paired_x25519_key_shares_derived_key_agrees`;
  - `lemma_supported_profile_client_server_key_material_agrees`, the aggregate
    supported-profile theorem for all first-milestone derived key material and
    installed peer record key/IV directions.
- Verified public server wrappers for the important local/network state
  mutations, including ClientHello receive, supported selection, shared-secret
  derivation, ServerHello send, handshake/application key installs,
  EncryptedExtensions, Certificate, CertificateVerify, ServerFinished,
  client-Finished verification, application data, and close_notify.
- A server driver with raw-byte IO-history preservation through:
  - TCP listen/accept/start;
  - retained-buffer read/process/compact;
  - `NeedMoreInput` network retry;
  - read until `ClientHello`;
  - driver-owned `server_random || server_private_key` generation;
  - supported-profile selection and X25519 shared-secret derivation;
  - exact cleartext ServerHello emission;
  - a fueled empty-action local drain.
- The composed driver entry
  `accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once`,
  which accepts TCP, starts the server, reads through ClientHello, selects and
  derives the shared secret, emits the matching cleartext ServerHello, and then
  drains scheduler-supported empty local actions. This advances the executable
  driver beyond ServerHello into scheduler-driven payload-free actions, while
  still stopping at credential-bearing actions.
- Since that baseline, the public server facade has been hardened: `accept`
  reaches application-data control on `ServerWorkflowOk` and now exposes
  `server_driver_application_ready`, including
  `ST.server_end_to_end_invariant` and
  `CS.application_record_keys_installed_for_role CS.ServerEndpoint`. The public
  `receive` spec is also tied to the concrete app-output buffer and returns
  `ServerWorkflowOk` exactly when the copied application bytes fit the caller
  and driver buffers. Public `close` now requires the same application-ready
  state exposed by successful `accept`, sends verified `LocalSendCloseNotify`
  via the local-write theorem, and then closes the transport.
- Concrete extracted client/server validation passes for the current facades:
  `make test-extracted-client-driver-slice`, `make test-openssl-echo`,
  `make test-extracted-server-driver-slice`, and `make test-openssl-sclient`
  all complete successfully, including real OpenSSL interop in both directions,
  application echo, and close paths.
- The client top-level driver facade is being hardened symmetrically: successful
  `TLS13.Impl.Client.Driver.connect` now exposes
  `client_driver_application_ready`, proving the connected client state is in
  `ControlApplicationData`, preserves `CT.client_end_to_end_invariant` through
  the recursive Pulse handshake orchestration, and has role-correct client
  application record read/write keys installed.

## What is not complete yet

We do **not** yet have the final verified interoperable server.

The main spec-level key-material agreement theorem is now packaged as an
aggregate supported-profile theorem, and `TLS13.Impl.Driver.Pairing` now provides
the audit-facing driver-pair bridge theorem:
`lemma_client_server_driver_key_material_agrees`. It also provides the explicit
no-read-ahead bridge
`lemma_paired_wire_logs_from_exact_prefix_no_read_ahead`, which upgrades the
public ordered received-prefix facts to full `CS.paired_wire_logs` when each
transport receive history has no retained suffix beyond the protocol
`raw_received` log. Successful public client `connect` and server `accept` now
also expose that no-read-ahead fact. The clearer wrapper
`lemma_client_server_driver_key_material_agrees_from_public_success_components`
takes those public success facts plus the remaining semantic state inputs and
returns historical derived-key agreement, the aggregate key-material input
predicate, exact paired transport/protocol wire logs, and final
`CS.supported_profile_client_server_key_material_agrees`.

What is still missing is the concrete paired-resource theorem that keeps
`paired_transport_histories` as an explicit environment precondition and
establishes the remaining semantic state inputs for live runs: paired X25519
shares, paired transcript checkpoints, and precise current application
record-state facts. The last category is intentionally still explicit:
successful application readiness proves role-correct application record keys are
installed, but it does not yet prove the record epoch/current application
traffic material facts needed by the aggregate record-material theorem,
especially in the presence of post-handshake KeyUpdate behavior.

On the Pulse implementation side, public server `accept` and client `connect`
now both expose application-data readiness on success, exact sent-log equality,
ordered received-prefix facts, and no-read-ahead success facts. Public
client/server `send` operations expose exact local-write sent-log append facts;
public client/server `receive` operations expose exact successful app-output
copyout facts; and public client/server `send`/`receive`/`close` operations
expose the pre-call wire-log projections hidden inside the connected driver
resource. Public client/server `close` operations expose verified
`close_notify` local-write facts before transport shutdown. The remaining
implementation-side gaps are:

- package a concrete paired-run theorem over successful client/server resources
  that takes `paired_transport_histories` as an environment precondition and
  supplies the semantic state inputs required by
  `lemma_client_server_driver_key_material_agrees_from_public_success_components`;
- continue splitting the remaining public driver orchestration into smaller
  `Driver.Handshake`/`Driver.App` modules with narrow `.fsti` boundaries;
- strengthen the private client receive workflow with a factored network-loop
  theorem, analogous to the server `Driver.Network` boundary, so public receive
  can expose the whole workflow theorem rather than only the exact status and
  copyout facts.

## Latest verified in-progress slice

The client facade readiness slice strengthens `connect`. It adds
`client_application_record_keys_installed_runtime` in
`TLS13.Impl.ConnectionState.Queries` and uses it in
`TLS13.Impl.Client.Driver.connect`, so `DriverWorkflowOk` is no longer merely a
connected transport result: it proves application-data control, the client
end-to-end invariant, and installed client application record keys. Focused
verification for
`TLS13.Impl.ConnectionState.Queries` and `TLS13.Impl.Client.Driver` passes, as
do the extracted client driver slice and OpenSSL echo interop tests.

The follow-on client facade slice strengthens public `send`: its postcondition
now exposes `client_driver_send_correct`, tying the returned status to the
verified `LocalSendApplicationData` theorem and proving the transport sent log
is exactly the old sent log appended with the emitted TLS record bytes.

The next client facade slice strengthens public `receive`: its postcondition now
exposes `client_driver_receive_correct`, tying the returned status to the actual
driver workflow status, response app length, and output-buffer capacity split;
on success the caller's output prefix is exactly `CT.response_app_out` from the
driver's concrete app-output buffer.

The latest client facade slice strengthens public `close`: its postcondition now
exposes `client_driver_close_correct`, tying the returned status to a verified
`LocalSendCloseNotify` theorem and exact close-notify sent-log append before the
TCP channel is closed.

The latest theorem-bridge slices add `TLS13.Impl.Driver.Pairing`, which packages
the public client/server application-readiness facts, exact/no-read-ahead
transport log facts, paired transport histories, and explicit semantic
state-machine components into checked bridge theorems. The most audit-facing
entry point is
`lemma_client_server_driver_key_material_agrees_from_public_success_components`;
it proves historical derived-key agreement, the aggregate key-material input
predicate, exact paired wire logs, and
`CS.supported_profile_client_server_key_material_agrees`.

The latest facade-accounting slices expose public
`client_driver_received_log_accounted` and
`server_driver_received_log_accounted` predicates on connected public operations,
and public `send`/`receive`/`close` postconditions expose the pre-call sent-exact
and received-accounted projections hidden inside the connected driver resource.
Successful `connect`/`accept` additionally expose ordered exact-prefix and
no-read-ahead facts, so the pairing bridge can upgrade those success states to
full protocol/transport receive equality.

## Remaining proof gaps

1. **Concrete client/server agreement bridge**
   - Connect concrete client and server driver post-states to the existing
     spec-level paired endpoint predicates.
   - Use the existing derived-key agreement lemmas once the concrete transcript
     and key-share agreement hypotheses are established from wire logs.

2. **Exact received-log pairing**
   - The current driver predicates expose exact sent logs and public received
     accounting, but received transport logs may include retained read-ahead and
     rejected consumed bytes. The next strengthening must carry an ordered
     accepted-prefix/no-rejected/no-retained fact, not just length/count
     accounting, before it can prove exact peer sent/received equality.
   - Both immediate theorem-surface obligations for that strengthening are now
     discharged. Shared spec lemma
     `lemma_legal_connection_delta_local_fail_control_failed` and client/server
     response lemmas expose that `LocalFail`-based decode-error,
     unexpected-message, and bad-Finished responses leave the connection in
     `ControlFailed`. New client/server network predicates
     `network_bytes_nonfailed_received_prefix_accepted` and
     `server_network_nonfailed_received_prefix_accepted` prove that a non-failed
     network step with nonzero consumed input records the consumed prefix as the
     accepted protocol raw-received delta. Driver-side helper lemmas now prove
     exact received-log append for such non-failed network steps when the prior
     consumed transport prefix was exact.
   - The exact-unless-failed property is now folded into the hidden client/server
     driver wire-log witnesses: in every non-failed state, the protocol
     `raw_received` log must be exactly the consumed transport prefix, while
     failed states still retain the weaker accounting relation needed for
     rejected consumed bytes.
   - Successful public client `connect` and server `accept` now expose ordered
     exact-prefix received-log facts, and `TLS13.Impl.Driver.Pairing` composes
     paired transport histories with those facts into a checked
     `paired_protocol_received_logs_exact_prefix` theorem.
   - `TLS13.Impl.Driver.Pairing` also exposes
     `lemma_client_server_driver_key_material_agrees_from_prefixes`, which uses
     those ordered-prefix public facts plus the existing supported-profile
     state-machine input predicate to prove
     `CS.supported_profile_client_server_key_material_agrees` without requiring
     impossible full TCP-history equality in the presence of retained read-ahead.
   - Successful public client `connect` and server `accept` now also expose
     `client_driver_received_no_read_ahead` and
     `server_driver_received_no_read_ahead`: `ServerWorkflowOk` /
     `DriverWorkflowOk` only return on application-ready states whose retained
     input buffer is empty, so the concrete transport receive length equals the
     protocol `raw_received` length.
   - `TLS13.Impl.Driver.Pairing` now also exposes
     `lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead` and
     `lemma_paired_wire_logs_from_exact_prefix_no_read_ahead`: if each endpoint's
     concrete receive history has the same length as its protocol `raw_received`
     log, the ordered-prefix facts collapse to exact transport/protocol
     equality and yield full `CS.paired_wire_logs`.
   - `lemma_client_server_driver_key_material_agrees_from_no_read_ahead` now
     consumes the public application-ready, sent-exact, received-prefix, and
     no-read-ahead facts plus paired transport histories to prove both full
     `CS.paired_wire_logs` and
     `CS.supported_profile_client_server_key_material_agrees`.
   - `client_server_driver_supported_profile_state_inputs` now names only the
     remaining paired semantic state-machine obligations: paired X25519 key
     shares, paired transcript checkpoints, and precise current application
     record-state facts: each endpoint's installed application traffic slots
     match the expected derived key/IV material, and each current read/write
     record direction is at the application epoch. Handshake traffic-key
     agreement remains part of the historical derived-key theorem, while the
     current record-state component is application-only so the application-ready
     theorem surface does not require one endpoint record state to be
     simultaneously at handshake and application epochs. Key-schedule lineage is
     no longer caller-supplied at this bridge:
     `lemma_client_server_driver_supported_profile_derived_key_material_agrees`
     now proves the full historical derived-key agreement theorem from public
     application-ready success plus only paired X25519 shares and transcript
     checkpoints, deriving client/server lineage from endpoint reachability and
     role-correct installed application record keys. The aggregate bridge
     `lemma_client_server_driver_supported_profile_key_material_inputs_agree`
     reuses that derived-key theorem and calls the pure
     `lemma_supported_profile_application_record_material_inputs_agree_from_expected`
     bridge to turn those precise current application record-state facts into
     `supported_profile_application_record_material_inputs_agree`. The component theorem
     `lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`
     proves the aggregate spec input predicate plus the same wire-log and
     key-material conclusions from those explicit components, and
     `lemma_client_server_driver_key_material_agrees_from_public_success_components`
     exposes the same result under an audit-facing public-success name while
     also returning the historical derived-key agreement fact explicitly.
   - `client_driver_application_ready` is now symmetric with
     `server_driver_application_ready` at the invariant layer: it includes the
     client end-to-end invariant, threaded through the Pulse handshake and
     receive helper postconditions.
   - The remaining proof work is to prove the paired supported-profile
     state-machine components from two live successful driver resources, rather
     than requiring them as external theorem premises. Key-schedule lineage is
     now discharged by a pure reachability-shape invariant plus installed
     application keys, and the driver-level derived-key theorem is independent
     of record-material agreement; paired X25519 shares, transcript checkpoints,
     installed application traffic slots matching expected derived material, and
     current application record epochs still need dedicated paired-state
     projection lemmas.

3. **Extraction and interoperability**
   - Keep the public API buffer/driver oriented.
   - Extract the verified server path to C.
   - Validate against the supported client/server profile with concrete
     certificates and network IO.

## Recommended next steps

1. Prove each remaining component of
   `client_server_driver_supported_profile_state_inputs` from successful paired
   driver resources: X25519 shares, transcript checkpoints, installed
   application traffic slots matching expected derived material, and current
   application record epochs.
2. Package those component proofs into a concrete driver-pair theorem that
   instantiates
   `lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`.
3. Re-run extraction and interop tests after each C-facing facade change.

## Engineering note

`TLS13.Impl.Server.Driver.fst` is still large. New work should prefer small
modules and `.fsti` boundaries, following the client-side factoring style. The
largest remaining risk is not the cryptographic theorem itself; it is keeping
the Pulse orchestration proof modular enough that scheduler readiness,
credential resources, raw-byte IO logs, and exact state transitions remain
usable without long verifier iterations.
