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
- Concrete extracted-server validation now passes for the current facade:
  `make test-extracted-server-driver-slice` and `make test-openssl-sclient`
  both complete successfully, including a real OpenSSL client handshake,
  application echo, and server close path.
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
`lemma_client_server_driver_key_material_agrees`. What is still missing is the
harder concrete proof that complete Pulse client and server runs automatically
establish that bridge theorem's input predicate, especially the exact
transport/protocol received-log condition in the presence of retained read-ahead
and rejected consumed bytes.

On the Pulse implementation side, public server `accept` and client `connect`
now both expose application-data readiness on success, public client/server
`send` operations expose exact local-write sent-log append facts, public
client/server `receive` operations expose exact successful app-output copyout
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

The current in-progress slice strengthens the client facade rather than the
server driver. It adds
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

The latest theorem-bridge slice adds `TLS13.Impl.Driver.Pairing`, which packages
the public client/server application-readiness facts, exact paired transport log
obligations, and existing
`supported_profile_client_server_key_material_inputs_agree` predicate into a
single checked theorem that yields both `CS.paired_wire_logs` and
`CS.supported_profile_client_server_key_material_agrees`.

## Remaining proof gaps

1. **Concrete client/server agreement bridge**
   - Connect concrete client and server driver post-states to the existing
     spec-level paired endpoint predicates.
   - Use the existing derived-key agreement lemmas once the concrete transcript
     and key-share agreement hypotheses are established from wire logs.

2. **Exact received-log pairing**
   - The current driver predicates expose exact sent logs, but received transport
     logs may include retained read-ahead and currently account protocol
     `raw_received` inside consumed transport bytes rather than proving exact
     peer sent/received equality.
   - Tightening or supplementing this relation is the next proof boundary needed
     before the aggregate key-material theorem can be instantiated from two live
     driver resources alone.

3. **Extraction and interoperability**
   - Keep the public API buffer/driver oriented.
   - Extract the verified server path to C.
   - Validate against the supported client/server profile with concrete
     certificates and network IO.

## Recommended next steps

1. Finish validating and commit the client `connect` readiness hardening slice.
2. Add the smallest pure/driver bridge predicate that relates a connected client
   and connected server with paired exact wire histories to
   `supported_profile_client_server_key_material_inputs_agree`.
3. Strengthen the driver received-log relation enough to prove that bridge
   without hiding retained read-ahead or rejected bytes.
4. Re-run extraction and interop tests after each C-facing facade change.

## Engineering note

`TLS13.Impl.Server.Driver.fst` is still large. New work should prefer small
modules and `.fsti` boundaries, following the client-side factoring style. The
largest remaining risk is not the cryptographic theorem itself; it is keeping
the Pulse orchestration proof modular enough that scheduler readiness,
credential resources, raw-byte IO logs, and exact state transitions remain
usable without long verifier iterations.
