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

The latest committed verified server-driver slice is:

```text
7f2c5d0 Compose server hello empty drain
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
  and driver buffers.

## What is not complete yet

We do **not** yet have the final verified interoperable server.

The main spec-level key-material agreement theorem is now packaged as an
aggregate supported-profile theorem. What is still missing is the concrete bridge
saying that a complete Pulse client run and a complete Pulse server run,
connected through their raw IO logs, automatically establish that theorem's
input predicate. That bridge from concrete driver states to paired endpoint
agreement remains a composition task.

On the Pulse/server side, public `accept` now has a verified success path to
application-data readiness. The remaining implementation-side gaps are:

- build the concrete bridge from complete client/server driver states and raw IO
  logs to the aggregate paired-endpoint key-material theorem's input predicate;
- continue splitting the remaining public driver orchestration into smaller
  `Driver.Handshake`/`Driver.App` modules with narrow `.fsti` boundaries;
- extract and validate the full server facade with the C/runtime IO stubs and
  concrete OpenSSL interop tests.

## Latest verified in-progress slice

After the pause snapshot, the credential/config driver slice was focused-verified
with:

```text
make _cache/TLS13.Impl.Server.Types.fst.checked \
     _cache/TLS13.Impl.Server.Driver.fst.checked
```

The slice updates:

- `src/impl/TLS13.Impl.Server.Driver.fst`
- `src/impl/TLS13.Impl.Server.Types.fst`

It adds:

- `server_driver_config_matches_credentials`, an invariant tying the driver's
  credential resource to the immutable server config stored in the connection
  state;
- theorem-layer local-event config preservation lemmas;
- driver-level local/network config-preservation projections so
  `server_driver_connected` can carry the credential/config invariant across
  processing;
- an extension of the local drain to process scheduler-advertised
  `LocalSendCertificate`.

This slice still needs the repository full gate before it should be considered a
committed checkpoint.

One important finding from this in-progress work: automatic
`LocalSignCertificateVerify` scheduling still needs an additional proof
projection. The scheduler can expose concrete readiness facts for signing, but
the credential-aware signing wrapper also needs the ghost fact that the stored
server selection's credential identity matches the driver's credential identity.
That fact is true by construction for the supported selection path, but it is
not yet available as a stable invariant/query at the scheduler/driver boundary.

## Remaining proof gaps

1. **Credential identity projection for signing**
   - Add a small, stable proof boundary showing that after supported server
     selection, the stored `hs_server_selection.server_selected_credential`
     matches the immutable server config and driver credential resource.
   - Prefer a reusable pure invariant/query over ad hoc assertions inside the
     large driver.

2. **Credential-aware driver drain**
   - Finish and verify the driver credential/config invariant.
   - Let the local drain process `LocalSendCertificate`.
   - Then add a focused step for `LocalSignCertificateVerify`.
   - After signing, reuse the existing generic/stored CertificateVerify send and
     ServerFinished scheduler paths.

3. **Full server handshake driver**
   - Compose accept/start/read ClientHello, select/derive/send ServerHello,
     handshake-key installs, EncryptedExtensions, Certificate, CV signing,
     CertificateVerify, ServerFinished, client-Finished read/verify, and
     application-key installation.
   - Preserve the raw-byte IO-history relation and expose exact branch outcomes.

4. **Concrete client/server agreement bridge**
   - Connect concrete client and server driver post-states to the existing
     spec-level paired endpoint predicates.
   - Use the existing derived-key agreement lemmas once the concrete transcript
     and key-share agreement hypotheses are established from wire logs.

5. **Extraction and interoperability**
   - Keep the public API buffer/driver oriented.
   - Extract the verified server path to C.
   - Validate against the supported client/server profile with concrete
     certificates and network IO.

## Recommended next steps

1. Re-run focused verification for the current in-progress driver after the
   `U64` import:
   `make _cache/TLS13.Impl.Server.Driver.fst.checked`.
2. If it passes, run the full gate and commit the credential/config invariant
   plus Certificate-drain support as a small slice.
3. If it does not pass quickly, split the credential/config invariant and local
   preservation lemmas behind a smaller interface before continuing.
4. Add the selected-credential projection needed for
   `LocalSignCertificateVerify`.
5. Compose and verify the next driver slice through the complete server
   encrypted flight.

## Engineering note

`TLS13.Impl.Server.Driver.fst` is still large. New work should prefer small
modules and `.fsti` boundaries, following the client-side factoring style. The
largest remaining risk is not the cryptographic theorem itself; it is keeping
the Pulse orchestration proof modular enough that scheduler readiness,
credential resources, raw-byte IO logs, and exact state transitions remain
usable without long verifier iterations.
