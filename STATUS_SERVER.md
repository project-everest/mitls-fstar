# TLS server verification status

Status date: 2026-06-15.

## Goal

The end goal is a verified, interoperable TLS 1.3 client/server implementation for
the repository's first supported profile:

- TLS 1.3 only.
- X25519 key exchange.
- `TLS_CHACHA20_POLY1305_SHA256`.
- Certificate-based server authentication using `RsaPssRsaeSha256`.
- No PSK, 0-RTT, HelloRetryRequest, client authentication, resumption, early
  data, or KeyUpdate in the first milestone.

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

The latest committed verified server-driver baseline before the current client
facade hardening slice is:

```text
e0df22b Record server interop validation
```

At that point the full gate had passed:

```text
git --no-pager diff --check
make check-admits
make verify
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
  `ControlApplicationData` and has role-correct client application record
  read/write keys installed.

## What is not complete yet

We do **not** yet have the final verified interoperable server.

The main spec-level key-material agreement theorem is now packaged as an
aggregate supported-profile theorem, and `TLS13.Impl.Driver.Pairing` now provides
the audit-facing driver-pair bridge theorem:
`lemma_client_server_driver_key_material_agrees`. It also now provides the
explicit no-read-ahead bridge
`lemma_paired_wire_logs_from_exact_prefix_no_read_ahead`, which upgrades the
public ordered received-prefix facts to full `CS.paired_wire_logs` when each
transport receive history has no retained suffix beyond the protocol
`raw_received` log. Successful public client `connect` and server `accept` now
also expose that no-read-ahead fact. What is still missing is the concrete
paired-resource theorem that packages successful client/server resources and
establishes the remaining
`supported_profile_client_server_key_material_inputs_agree` premise for live
runs.

On the Pulse implementation side, public server `accept` and client `connect`
now both expose application-data readiness on success, public client/server
`send` operations expose exact local-write sent-log append facts, public
client/server `receive` operations expose exact successful app-output copyout
facts, public connected send/receive/accept success results expose exact
transport sent-history/protocol sent-log equality plus received-log accounting
facts, and public client/server `close` operations expose verified
`close_notify` local-write facts before transport shutdown. The remaining
implementation-side gaps are:

- prove the exact transport/protocol log obligations named by
  `TLS13.Impl.Driver.Pairing.paired_driver_transport_logs_exact` from complete
  client/server driver resources and raw IO logs;
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
connected transport result: it proves application-data control and installed
client application record keys. Focused verification for
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
the public client/server application-readiness facts, exact paired transport log
obligations, and existing
`supported_profile_client_server_key_material_inputs_agree` predicate into a
single checked theorem that yields both `CS.paired_wire_logs` and
`CS.supported_profile_client_server_key_material_agrees`. The same module now
also exposes `lemma_paired_protocol_received_logs_accounted`, a checked
intermediate bridge from public sent-exact/received-accounted facade facts plus
paired transport histories to cross-endpoint protocol received-log accounting.

The latest facade-accounting slice exposes public
`client_driver_received_log_accounted` and
`server_driver_received_log_accounted` predicates on successful connected
client/server paths. These prove the protocol `raw_received` bytes are
accounted for within the concrete transport receive history. This is deliberately
weaker than ordered exact equality: retained read-ahead and rejected consumed
bytes still prevent deriving `CS.paired_wire_logs` directly.

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
   - `client_server_driver_supported_profile_state_inputs` now names the
     remaining semantic state-machine obligations explicitly: paired X25519
     key shares, client/server key-schedule lineage, paired transcript
     checkpoints, and all record-material input agreement. The component theorem
     `lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`
     proves the aggregate spec input predicate plus the same wire-log and
     key-material conclusions from those explicit components.
   - The remaining proof work is to prove the supported-profile state-machine
     input predicate from two live successful driver resources, rather than
     requiring it as an external theorem premise.

3. **Extraction and interoperability**
   - Keep the public API buffer/driver oriented.
   - Extract the verified server path to C.
   - Validate against the supported client/server profile with concrete
     certificates and network IO.

## Recommended next steps

1. Prove each component of
   `client_server_driver_supported_profile_state_inputs` from successful paired
   driver resources: X25519 shares, key-schedule lineage, transcript
   checkpoints, and record-material inputs.
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
