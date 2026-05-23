# Verified TLS 1.3 in Pulse: implementation plan

## Problem statement

Build a clean, extraction-ready TLS 1.3 client implementation in Pulse, verified against pure F* state-machine specifications for the handshake and record layer, and extracted to C. The extracted C should link against HACL* for cryptographic primitives and OpenSSL for X.509 certificate validation, then first interoperate with a controlled local OpenSSL TLS echo server by negotiating TLS 1.3 and transferring exact application-data bytes. Public HTTPS interop is a later compatibility milestone after the controlled echo path is stable.

The current workspace contains this review plan. A system `fstar.exe` is available for bootstrapping/reference, but the project should not depend on it. Add a repository-local `setup.sh`, modeled after `../pulse-verified-gc/setup.sh`, that downloads the latest F* binary release into `tools/FStar` with `--no-link`, sets up a local KaRaMeL compatibility layout, and lets the Makefile use only `tools/FStar/bin/fstar.exe` and the matching local `krml`. GitHub access through `gh repo view` works for `FStarLang/FStar` and `hacl-star/hacl-star`, but this CLI session does not expose a GitHub MCP semantic-search tool. The requested MCP semantic-search smoke test therefore cannot be completed here; use `gh` and local vendored sources as the available research path unless the MCP server is configured outside this session.

## Initial scope and assumptions

The task is clear enough to proceed with the following pinned initial choices, which affect specs, FFI surfaces, test endpoints, and proof obligations.

1. Initial target is a TLS 1.3 client, not a server.
2. Initial interoperable mode is full 1-RTT, server-authenticated ECDHE handshake with no PSK, no 0-RTT, no client authentication, no resumption, and no key update.
3. Initial key exchange group is X25519 only. P-256 can be added later.
4. Initial cipher suite is `TLS_CHACHA20_POLY1305_SHA256`, using HKDF-SHA256 and ChaCha20-Poly1305.
5. Initial signature schemes should include `rsa_pss_rsae_sha256` and likely `ecdsa_secp256r1_sha256`, because real HTTPS servers commonly use them. Ed25519 alone is not sufficient for broad interop.
6. HelloRetryRequest should be recognized and handled by a verified abort/alert path initially, not silently misparsed. Full HRR retry can be a later milestone.
7. The primary correctness claim is functional/state-machine correctness and memory safety for the Pulse implementation, plus byte-level agreement with the abstract specs. This is not, by itself, a cryptographic security proof for TLS.
8. HACL* and OpenSSL are trusted FFI components. Their Pulse `.fsti` files must specify their expected behavior precisely, but the C implementations remain in the trusted computing base.
9. Pick concrete interop targets early: first a controlled localhost OpenSSL echo server, then a public HTTPS endpoint only after the echo path is stable. Use RFC 8448 test vectors before attempting either network interop target.
10. For the first version, parser/serializer code is deliberately scoped behind trusted `.fsti` interfaces and implemented directly in unverified C stubs. Verified parser/serializer implementation is deferred to a later phase so the first milestone can focus on the core protocol state machine, key schedule, record layer, and handshake logic; do not plan on Low* or LowParse for this project unless that direction is explicitly reintroduced later.
11. The first interop target is a controlled local TLS echo test against OpenSSL, not public HTTPS. Use a local OpenSSL-backed echo server, generated test CA/leaf certificates for `localhost`, TLS 1.3, X25519, `TLS_CHACHA20_POLY1305_SHA256`, no client auth, no PSK/resumption/0-RTT, and no HTTP semantics. Public HTTPS interop is deferred until the controlled echo path is stable.

## Reference material and dependency policy

1. Cache RFC 8446 and RFC 8448 locally for offline reference and test-vector work using `scripts/fetch-rfcs.sh`. Store downloaded RFC text under gitignored `third_party/rfc/`; do not commit RFC text snapshots unless there is a later explicit reason to vendor them.
2. Pin HACL* as a Git submodule under `third_party/hacl-star`, but use only its checked-in C snapshot under `dist/gcc-compatible`. Do not try to reverify HACL* from source, and do not make this project depend on HACL* F* specs; model the required crypto behavior with local abstract/uninterpreted spec functions and trusted Pulse `.fsti` contracts.
3. Treat OpenSSL as a system dependency, not vendored source. Require an installed OpenSSL 3.x executable, headers, and libraries; validate availability with `scripts/check-openssl.sh`.
4. Keep downloaded toolchains, RFC caches, generated extraction output, query logs, and build artifacts out of git.

## Prominent proof-engineering rule: keep modules small and proofs isolated

This project should be structured from the start to avoid large verification contexts. TLS is big enough that proof instability will become the main engineering risk if files accumulate unrelated definitions, helper lemmas, parser details, and Pulse code in one module.

1. Keep files small. Split large modules early, before they become difficult to refactor. Prefer narrowly scoped modules for bytes, wire specs, state-machine definitions, transition lemmas, key-schedule lemmas, record lemmas, handshake steps, and Pulse implementation helpers.
2. Use `.fsti` interfaces aggressively to isolate dependencies. Export only the types, predicates, functions, and lemma statements that downstream modules need.
3. Hide lemma proof bodies in `.fst` files behind `.fsti` declarations. Downstream modules should depend on stable theorem statements, not on proof internals or large helper definitions.
4. Keep dependency edges narrow and acyclic where possible. If a module needs only a lemma statement, depend on the small lemma interface rather than importing the implementation module that contains many unrelated facts.
5. Do not use high rlimits as a normal proof strategy. Start with low rlimits, factor proofs, add intermediate assertions, make definitions opaque, and use explicit lemma calls instead of letting SMT search through large contexts.
6. If a proof needs a high rlimit, becomes flaky, or slows a module noticeably, stop and diagnose it early with `proofdebugging` and `smtprofiling`: run with `--query_stats --split_queries always`, isolate the failing query, log `.smt2` files with `--log_queries --z3refresh`, inspect quantifier profiles, and fix the root cause before building more code on top.
7. Use proof-stability techniques deliberately: split lemmas into smaller modules, use `assert_spinoff` for expensive facts, add `#restart-solver` between large definitions when needed, use `--using_facts_from` to prune problematic facts, keep fuel/ifuel low, and introduce quantified facts manually rather than relying on global triggers.
8. Treat every `.fsti` as a proof-performance boundary as well as an API boundary. A good interface should make callers' VCs smaller and more stable.
9. Do not spawn sub-agents for deep reasoning, design, or proof work. Sub-agents are acceptable only for short, shallow, non-deep tasks; the main agent must own the core reasoning, verification strategy, and proving work.
10. Commit changes frequently as coherent milestones land: after project setup, each verified module or trusted stub, each test harness, and each proof-stability cleanup. Prefer small, reviewable commits with passing relevant checks over large mixed commits.
11. Represent the Pulse-level connection state machine with monotonic ghost state, following the `Pulse.Lib.MonotonicGhostRef` pattern from `Example.SimpleDBModel`: define the pure TLS transition closure as a preorder, store the current ghost state in a monotonic reference, expose duplicable snapshots for previously observed states, and require every state update to prove a legal `TLS13.StateMachine.step` (or its reflexive/transitive closure) before calling the monotonic update. The top-level connection and handshake predicates should carry this ghost token so implementations cannot silently skip or reorder state-machine transitions.

## Proposed repository layout

```text
tls/
├── Makefile
├── .gitignore
├── setup.sh
├── tools/
│   └── FStar/              # created by setup.sh, gitignored
├── src/
│   ├── spec/
│   │   ├── TLS13.Types.fst
│   │   ├── TLS13.Bytes.fst
│   │   ├── TLS13.Crypto.Spec.fst
│   │   ├── TLS13.X509.Spec.fst
│   │   ├── TLS13.Transcript.fst
│   │   ├── TLS13.Keys.fst
│   │   ├── TLS13.Record.Spec.fst
│   │   ├── TLS13.Handshake.Spec.fst
│   │   └── TLS13.StateMachine.fst
│   └── impl/
│       ├── TLS13.MachineTypes.fsti
│       ├── TLS13.Buffer.fsti
│       ├── TLS13.Buffer.fst
│       ├── TLS13.Parse.fsti      # trusted FFI contract in v1
│       ├── TLS13.Serialize.fsti  # trusted FFI contract in v1
│       ├── TLS13.Crypto.fsti
│       ├── TLS13.Crypto.fst
│       ├── TLS13.X509.fsti
│       ├── TLS13.X509.fst
│       ├── TLS13.Record.fsti
│       ├── TLS13.Record.fst
│       ├── TLS13.Handshake.fsti
│       ├── TLS13.Handshake.fst
│       ├── TLS13.Connection.fsti
│       └── TLS13.Connection.fst
├── c_stubs/
│   ├── tls13_hacl_stubs.c
│   ├── tls13_hacl_stubs.h
│   ├── tls13_openssl_stubs.c
│   ├── tls13_openssl_stubs.h
│   ├── tls13_wire_stubs.c
│   ├── tls13_wire_stubs.h
│   ├── tls13_io_stubs.c
│   └── tls13_io_stubs.h
├── test/
│   ├── vectors/
│   │   └── rfc8448/
│   ├── Test.Spec.fst
│   ├── test_vectors.c
│   ├── openssl_echo_server.c
│   ├── test_tls_echo.c
│   └── test_https_client.c
├── snapshot/
└── third_party/
    └── hacl-star/
```

`setup.sh` installs the project-local F*/KaRaMeL toolchain into `tools/FStar`; `.gitignore` should exclude `tools/FStar`, `_cache`, `_output`, `_extract`, and other generated files. `src/spec` contains pure F* specifications using unbounded types, sequences, and mathematical models. `src/impl` contains extraction-ready Pulse/F* using machine integers, arrays/vectors, erased ghost models, and `.fsti` interfaces that expose functional correctness postconditions. In v1, `TLS13.Parse.fsti` and `TLS13.Serialize.fsti` are trusted declaration-only FFI contracts implemented by C stubs, not verified Pulse implementations. `c_stubs` contains the trusted C bindings to HACL*, OpenSSL, parser/serializer code, randomness, clock, and socket/BIO I/O.

## Specification architecture

### Pure TLS model

Define an abstract byte model and TLS wire structures:

1. Protocol versions, content types, alerts, cipher suites, named groups, signature schemes, extension types.
2. Variable-length vectors and length-prefixed structures as pure byte sequences.
3. Handshake messages in the initial scope: ClientHello, ServerHello, EncryptedExtensions, Certificate, CertificateVerify, Finished, and HelloRetryRequest recognition.
4. Record-layer structures: TLSPlaintext, TLSInnerPlaintext, TLSCiphertext, epochs, sequence numbers, nonces, and content-type padding.
5. Error outcomes and alerts for unsupported modes, malformed messages, authentication failure, decryption failure, close_notify, and unexpected messages.

### Ghost state machine

Define `TLS13.StateMachine` as the source of truth for connection state and legal transitions. The state should include:

1. Role: client initially.
2. Handshake phase: start, client_hello_sent, server_hello_received, encrypted_extensions_received, certificate_received, certificate_validated, certificate_verified, server_finished_verified, client_finished_sent, application_data, closing, closed, failed.
3. Transcript state: abstract transcript bytes and hash checkpoints.
4. Key schedule state: abstract traffic-secret identifiers and epochs, not necessarily concrete secret bytes in all invariants.
5. Record-layer state: read/write epochs, sequence numbers, pending partial records, buffered ciphertext/plaintext, and close state.
6. Peer identity state: requested hostname, certificate validation result, extracted public key, and signature scheme.
7. Failure transitions that preserve safety: malformed input, unsupported extension, unsupported group, unsupported signature, HRR abort, bad certificate, bad signature, bad Finished, bad record tag.

The top-level Pulse connection predicate should relate concrete memory to an erased `TLS13.StateMachine.conn_state`, and every public operation should prove that it performs one or more legal state-machine transitions.

### Functional correctness boundary

The main exported correctness property is:

```text
If a Pulse function starts with concrete memory related to spec state S
and returns success, then the resulting concrete memory is related to a
spec state S' such that StateMachine.step* S event S' holds, and any
returned bytes/messages equal the pure spec result for that transition.
```

This includes transcript consistency, key-schedule consistency, record protection/unprotection correctness relative to the AEAD spec, and correct binding between validated certificate identity, CertificateVerify, and the transcript. In v1, wire parser/serializer byte-level correctness is assumed through trusted `.fsti` contracts and validated with C/vector tests; the C parser/serializer implementation itself is not verified until a later parser/serializer verification phase.

## Trusted FFI specifications

### HACL* C snapshot crypto interface

Create `TLS13.Crypto.fsti` as a Pulse interface over trusted C stubs linked to the HACL* checked-in C snapshot at `third_party/hacl-star/dist/gcc-compatible`. The interface should be extraction-safe and expose pure postconditions tied to local `TLS13.Crypto.Spec` definitions, not to HACL* F* spec modules.

`TLS13.Crypto.Spec` should be an abstract specification layer for the trusted C snapshot, not a reimplementation or proof of the cryptographic algorithms. For example, expose uninterpreted functions such as `sha256 : bytes -> digest32`, `hkdf_extract : salt -> ikm -> secret`, `hkdf_expand_label : secret -> label -> context -> len -> bytes`, `x25519_shared : private_key -> public_key -> option shared_secret`, and AEAD functions for ChaCha20-Poly1305 seal/open. The Pulse `.fsti` wrappers for HACL* C calls should prove memory safety, ownership, length, aliasing, and state-machine integration, and should specify that successful outputs equal these abstract spec functions. Only add axioms or lemmas for structural facts needed by TLS, such as output lengths, determinism of pure functions, and success/failure shape; do not assert cryptographic security properties or import HACL* proof internals.

Initial functions:

1. Secure random bytes for ClientHello random and X25519 private key material.
2. X25519 key generation/shared secret.
3. SHA-256 hash and incremental or one-shot transcript hash.
4. HKDF-Extract, HKDF-Expand, and TLS 1.3 HKDF label expansion.
5. HMAC-SHA256.
6. ChaCha20-Poly1305 seal/open with TLS 1.3 nonce construction.
7. Signature verification for the selected initial signature schemes, either through the HACL* C snapshot where practical or OpenSSL EVP if HACL* coverage is insufficient for deployed certificate algorithms.

Each `.fsti` declaration must specify buffer lengths, aliasing/disjointness requirements, ownership, mutation effects, and exact pure functional result. The C stubs are trusted to implement these declarations and must map failures explicitly to verified error results.

### OpenSSL X.509 interface

Create `TLS13.X509.fsti` as a Pulse interface over trusted OpenSSL C stubs. The main certificate validation function should return an extracted public key and signature metadata, not just a boolean:

```text
validate_chain(hostname, validation_time, trust_store, certificate_list)
  returns Some(peer_identity)
  iff the chain is valid for the hostname/time/trust store and peer_identity
  contains the leaf SPKI/public key and permitted signature schemes.
```

The handshake proof must connect this result to CertificateVerify: the signature is verified using the public key from the validated leaf certificate over the RFC 8446 CertificateVerify transcript input.

### Trusted wire parser/serializer interface

Create `TLS13.Parse.fsti` and `TLS13.Serialize.fsti` as Pulse/F* interfaces over trusted C stubs in `c_stubs/tls13_wire_stubs.c`. These interfaces should expose exact pure-spec contracts while treating the C implementation as trusted:

1. Parse success returns a message equal to the pure parser result for the consumed bytes and advances by the specified encoded length.
2. Parse failure returns a specified TLS error/alert outcome and does not silently normalize malformed input.
3. Serialize success writes exactly the pure serialized bytes for the abstract message and reports the exact encoded length.
4. Serialize failure corresponds to explicit output-buffer-too-small or unsupported-message results.
5. Contracts include all length bounds, output buffer ownership, cursor advancement, and mutation effects.

The verified core protocol code should operate on the abstract messages and byte sequences exposed by these contracts. Replacing these trusted stubs with verified parser/serializer code is a separate later phase, but Low* and LowParse are not part of the current plan.

## Implementation architecture

### Extraction-ready representation

Use only extraction-ready concrete types in implementation code: `UInt8.t`, `UInt16.t`, `UInt32.t`, `UInt64.t`, `SizeT.t`, `bool`, stack arrays, heap boxes/vectors, and erased ghost state. Avoid `nat`, `int`, `list`, `string`, and `Seq.seq` in extractable positions.

Reuse existing Pulse and F* libraries wherever possible instead of rebuilding basic data structures or proofs from scratch. Use the standard libraries for arrays/buffers, references, machine integers, options/results, sequences, lists, and common list/sequence/length lemmas; pure `FStar.Seq`/`FStar.List.Tot`-style structures are appropriate in specs and ghost code, while extraction-facing code should use the existing Pulse/F* array, buffer, ownership, and integer libraries. Add a local wrapper only when it gives a TLS-specific abstraction or narrows an interface, not to reimplement a generic container such as an array, linked list, vector, option, or byte buffer. Do not introduce Low* as a project implementation strategy.

Core predicates:

1. Buffer ownership predicate relating byte arrays/vectors to erased spec byte sequences.
2. Parser cursor predicate relating pointer/length/offset to unconsumed spec bytes.
3. Record-state predicate relating keys, sequence numbers, buffers, and epochs to the ghost state machine.
4. Connection predicate abstracting the full client context and exposing only its spec relation.

### Parser and serializer strategy for v1

Keep parser/serializer work behind trusted FFI in the first version. This intentionally reduces the initial verification burden and keeps the focus on the core TLS protocol logic.

The v1 parser/serializer plan is:

1. Define pure parser/serializer specs for supported TLS records, handshake messages, and extensions.
2. Expose trusted `.fsti` contracts that connect C parser/serializer stubs to those pure specs.
3. Implement the parser/serializer directly in C for the scoped message surface.
4. Test the C parser/serializer with RFC 8448 vectors and malformed-input cases.
5. Treat parser/serializer C code as part of the trusted computing base until a later verified parser/serializer phase replaces it.

### Record layer

Implement record protection and unprotection for ChaCha20-Poly1305 only:

1. Maintain per-direction sequence numbers with overflow checks.
2. Derive nonce as RFC 8446 static IV XOR sequence number.
3. Construct additional authenticated data from record header.
4. Encode/decode TLSInnerPlaintext including content type and padding.
5. Prove successful open returns bytes/content type equal to `TLS13.Record.Spec.open`.
6. Prove successful seal writes bytes equal to `TLS13.Record.Spec.seal`.
7. Model partial TCP reads and buffered ciphertext in the state machine.

### Handshake layer

Implement the initial client handshake as a sequence of verified transitions:

1. Build ClientHello with supported_versions, supported_groups, key_share(X25519), signature_algorithms, server_name, and optionally ALPN.
2. Parse ServerHello and verify selected version, cipher suite, group, and key share.
3. Derive handshake traffic secrets and install handshake read/write keys.
4. Decrypt and parse EncryptedExtensions.
5. Parse Certificate and validate it through the OpenSSL FFI.
6. Verify CertificateVerify using the validated leaf key and transcript-specific signature input.
7. Verify server Finished.
8. Derive application traffic secrets and install application-data keys.
9. Send client Finished.
10. Transition to application data.

Unsupported but recognized paths such as HRR, PSK, early_data, client_certificate_request, unsupported ciphers, unsupported groups, or unsupported signatures should transition to a verified failure/alert state.

### Top-level API

Expose a small C-oriented API from `TLS13.Connection.fsti`, with postconditions referencing only abstract spec types and the state machine:

1. `client_new`: allocate and initialize a connection context for a hostname/trust store/config.
2. `client_free`: release all owned memory.
3. `client_connect`: drive the verified handshake over trusted I/O callbacks or a socket wrapper.
4. `client_write`: protect and send application data, proving record-state transition and byte correspondence.
5. `client_read`: receive, decrypt, buffer, and return application data, proving record-state transition and byte correspondence.
6. `client_close`: send/consume close_notify and close the connection state.

The `.fsti` must expose enough of the abstract state predicates and transition postconditions for callers to reason about connection state without depending on implementation internals.

### Controlled OpenSSL TLS echo interop

Before any public HTTPS endpoint, add a local OpenSSL interop test that exercises exactly the TLS functionality we intend to verify:

1. Build a tiny OpenSSL-based TLS 1.3 echo server in `test/openssl_echo_server.c`, or use `openssl s_server` only if it provides the exact byte-for-byte behavior needed by the harness.
2. Generate a local test CA and localhost leaf certificate during the test setup; do not depend on the host trust store.
3. Pin the server to X25519 and `TLS_CHACHA20_POLY1305_SHA256` so the test exercises the scoped first-version key exchange and record algorithm.
4. Disable client authentication, PSK, session resumption, 0-RTT, and ALPN initially.
5. Have the extracted client connect to `localhost`, validate the test certificate chain/hostname through the OpenSSL X.509 FFI, complete the handshake, send known application-data byte strings, and require exact echoed bytes in response.
6. Include short payloads, payloads spanning more than one record, and server-side fragmentation/partial-read cases so the connection driver and buffering logic are tested before public-network interop.
7. Treat this as a TLS application-data interop milestone. It does not prove HTTP parsing, HTTP semantics, WebPKI behavior, or broad endpoint compatibility.

## Current verified interop status and full-client roadmap

The controlled OpenSSL echo test now defaults to the extracted-wrapper client path:

1. The extracted-wrapper path is now the only OpenSSL echo client path. It runs extracted `TLS13.Connection`, extracted `TLS13.Handshake`, extracted `TLS13.Handshake.Driver`, extracted `TLS13.Handshake.ByteDriver`, extracted `TLS13.Handshake.Transcript`, extracted `TLS13.KeySchedule`, extracted `TLS13.Record`, extracted `TLS13.Record.Framing`, and extracted `TLS13.Handshake.Framing` in the default interop test. This path proves the modeled connection/handshake sequencing, extracted scoped ClientHello serialization, extracted scoped ServerHello parsing/key-share extraction, encrypted-handshake message scheduling for the scoped OpenSSL server flight, extracted server-handshake record open sequence/nonce/AEAD orchestration, extracted client-Finished record seal sequence/nonce/AEAD orchestration, one-shot transcript hash routing for both the ClientHello||ServerHello handshake-secret checkpoint and the scoped full transcript shape, extracted Finished compare, key-schedule label/derivation orchestration, Finished verify-data routing, CertificateVerify input construction, Certificate leaf-DER offset parsing, CertificateVerify body length/scheme parsing, application record seal/open wrapper behavior, and no-padding application record framing before calling the remaining trusted byte backend.
2. The legacy direct C probe and older extracted-driver OpenSSL routes have been removed from the Makefile, shell harness, test sources, and `tls13_connection_probe.c` preprocessor branches. Future work should deepen the single extracted-wrapper route rather than restoring parallel interop paths.

For the purposes of this project, "full verified TLS client from Pulse to C in the interop tests" means that the OpenSSL echo path should execute extracted verified Pulse/F* code for all TLS protocol logic we own: handshake state progression, transcript bookkeeping, key schedule orchestration, record sequence/nonce/AAD/inner-plaintext handling, supported-message parsing/serialization, application-data buffering, and connection read/write/close state. HACL*'s checked-in C snapshot, OpenSSL X.509/signature validation, OS randomness, clock, and socket I/O remain explicit trusted components with precise local `.fsti` contracts unless the user later expands the scope.

The remaining trusted TLS-owned backend pieces to eliminate, in order, are:

1. **Transcript and handshake byte driver**: the first extracted `TLS13.Handshake.ByteDriver` slice now owns the scoped encrypted server-flight schedule: it reads until a complete pending handshake message exists using a fuelled recursive helper bounded by `max_encrypted_records_per_message`, enforces the exact EncryptedExtensions, Certificate, CertificateVerify, Finished order, and maps wrong type, incomplete flight, or lower-layer failure to handshake failure. `TLS13.Record` now owns server-handshake record open and client-Finished record seal sequence/nonce/AEAD orchestration in the wrapper path. `TLS13.Handshake.FlightState` now owns the server-flight cursor, parsed-message offset, CertificateVerify offset, Finished transcript checkpoint lengths, and encrypted-handshake completion flags in extracted code. `TLS13.Handshake.Transcript` now routes both the ClientHello || ServerHello handshake-secret checkpoint and scoped ClientHello || ServerHello || server-flight transcript hash through extracted code, and performs the Finished verify-data equality check in extracted code. The remaining work is to move raw transcript byte storage/copying and encrypted-handshake buffering out of `tls13_connection_probe.c`; keep only primitive I/O, HACL*, OpenSSL X.509/signature calls, and low-level parser/serializer calls behind trusted ABIs during this step.
2. **Record framing and TLSInnerPlaintext**: route the scoped no-padding application-data and encrypted-handshake framing through verified extracted code. The extracted `TLS13.Record` wrapper owns AEAD seal/open state; `TLS13.Record.Framing` now provides extracted no-padding TLSInnerPlaintext encoding for the application-data write path, no-padding content-type/payload-length decoding for the application-data read path and encrypted-handshake read path, TLS 1.3 application-data record-header construction for writes, and record-header parsing for the read path. Padding support and advanced read/write buffering are deferred to the verified wire-code and connection-I/O milestones.
3. **Scoped parser/serializer replacement**: replace trusted C parser/serializer stubs for the supported ClientHello, ServerHello, EncryptedExtensions, Certificate, CertificateVerify, Finished, TLSPlaintext, and TLSInnerPlaintext structures with verified extraction-ready Pulse/F* implementations tied to `TLS13.Wire.Spec`. This is the largest remaining TLS-owned trusted boundary.
4. **Connection buffering and partial I/O**: the first extracted `TLS13.Connection` application-I/O slice now owns multi-record write chunking, bounded read-record scheduling, extracted-owned application keys, and extracted-owned application record-state objects. The backend ABI has been narrowed from bulk `client_write`/`client_write_all`/`client_read`/`client_read_exact` operations to per-application-record hooks. Remaining work is to move each per-record seal/open and raw record read/write operation fully into Pulse, handle arbitrary partial socket reads/writes, handshake records during application reads, close_notify, and error propagation according to `TLS13.StateMachine`.
5. **ABI and TCB audit**: after the interop path no longer depends on TLS-owned trusted byte logic, audit all remaining external calls: HACL* wrappers, OpenSSL X.509/signature wrappers, randomness, time, socket I/O, allocation, and the small Pulse support shims. Each must have a documented local contract, tests for precondition edge cases, and no silent success-shaped fallback.
6. **Interop gate update**: the extracted-wrapper path is now the only `make test-openssl-echo` client path. The direct C probe and older extracted-driver diagnostic routes have been deleted. Remaining interop-gate work is adding fragmentation/partial-read and close_notify coverage to the wrapper path before considering public HTTPS.

## Build, verification, and extraction plan

1. Add `.gitignore`, `setup.sh`, `Makefile`, and directory skeleton.
2. Add dependency helpers for local RFC caches, the HACL* submodule, and OpenSSL system-dependency checks.
3. Implement `setup.sh` to download the latest F* binary release into `tools/FStar`, with an optional version override for reproducibility, and create the local KaRaMeL compatibility layout.
4. Configure the Makefile with `FSTAR_HOME ?= tools/FStar`, `FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe`, and `KRML_EXE`/`KRML_HOME` pointing at the local install. The build should fail with a clear message if `./setup.sh` has not been run.
5. Configure verification with the local `fstar.exe`, cache directories, includes for `src/spec` and `src/impl`, and separate `.fsti` then `.fst` verification.
6. Configure extraction with one `.krml` file per extracted module, bundle spec/proof modules away, expose only `TLS13.Connection` as the public C API, and link trusted external stubs for crypto, X.509, wire parsing/serialization, randomness, clock, and I/O.
7. Add C build rules linking extracted C with the HACL* `dist/gcc-compatible` C snapshot, OpenSSL, and trusted C stubs.
8. Add snapshot generation for extracted C headers/source.
9. Add test targets for pure spec tests, RFC 8448 vector tests, extracted C vector tests, parser/serializer C tests, controlled OpenSSL TLS echo interop tests, and later HTTPS interop tests.

## Incremental milestones

1. Project skeleton and toolchain
   - Create layout, `setup.sh`, Makefile, include paths, extraction directories, and empty modules.
   - `setup.sh` installs the latest F* binary release under `tools/FStar`, creates the local KaRaMeL compatibility layout, and leaves the system `fstar.exe` unused by the Makefile.
   - Verify a minimal Pulse module and extract a trivial C API.

2. Pure spec baseline
   - Define bytes, TLS enums, wire structures, errors, and state-machine states.
   - Define transition relations for the scoped handshake and record layer.
   - Add lemmas for determinism and safety of selected transitions.

3. Crypto and X.509 abstract specs
   - Define local abstract specs for SHA-256, HKDF labels, transcript hashes, X25519, signatures, and ChaCha20-Poly1305 sufficient for TLS proof obligations, using uninterpreted functions where appropriate. Do not attempt to reverify HACL*, reimplement crypto algorithms in F*, or import HACL* F* specs into this project.
   - Define X.509 validation as an abstract trusted relation returning peer identity and leaf public key.

4. FFI shells and C stubs
   - Write Pulse `.fsti` files for crypto and X.509 with precise ownership, length, aliasing, and postconditions.
   - Implement C stubs against HACL* and OpenSSL.
   - Add C smoke tests independent of TLS.

5. Trusted parser/serializer integration
   - Write `TLS13.Parse.fsti` and `TLS13.Serialize.fsti` contracts for supported messages and extensions.
   - Implement scoped parser/serializer C stubs behind those contracts.
   - Add C/vector tests for round-trip behavior, RFC 8448 inputs, and malformed-input rejection.
   - Defer parser/serializer verification to a later phase; do not plan on LowParse for this project.

6. Transcript and key schedule
   - Implement transcript hashing and TLS 1.3 key schedule.
   - Validate against RFC 8448 handshake/key-schedule vectors before networking.
   - Prove Pulse implementation matches pure key-schedule spec.

7. Record layer
   - Implement ChaCha20-Poly1305 record seal/open.
   - Prove nonce, AAD, sequence-number, and epoch correctness.
   - Validate with RFC 8448 record vectors.

8. Handshake receive/send flights
   - Implement ClientHello construction.
   - Implement ServerHello through server Finished parsing/verification.
   - Implement client Finished.
   - Prove each step advances the ghost state machine correctly.

9. Connection driver and I/O
   - Implement trusted I/O wrapper with explicit specs for partial reads/writes and errors.
   - Drive the handshake loop without hidden state changes on retry/partial I/O.
   - Implement application read/write with buffering.

10. Controlled OpenSSL TLS echo interop
    - Run RFC 8448 vector tests against extracted C.
    - Start the local OpenSSL-backed TLS 1.3 echo server with the generated localhost test certificate.
    - Connect with the extracted client, validate the test certificate/hostname, complete the handshake, send application bytes, and require exact echoed bytes.
    - Cover short payloads, multi-record payloads, partial reads/writes, record fragmentation, and close_notify.
    - Treat this as the first end-to-end interop gate before any public HTTPS endpoint.

11. Public HTTPS interop, after echo is stable
    - Connect to the selected HTTPS endpoint.
    - Send a minimal HTTP/1.1 request and read/decrypt the response as an application-data interop test, not as a verified HTTP-client milestone.
    - Treat real public HTTPS interop as extra compatibility work beyond the core TLS proof: SNI and hostname binding, WebPKI chain validation through OpenSSL, deployed signature schemes, ALPN/HTTP/1.1 selection, extension tolerance, partial TCP reads, record fragmentation, close_notify behavior, and endpoint-specific cipher/group constraints.

12. Hardening and cleanup
    - Remove all temporary admits and assumptions.
    - Run query stats and split queries on unstable modules.
    - Keep rlimits low by factoring pure lemmas and reducing SMT fuel where needed.
    - Audit `.fsti` files for complete functional postconditions and caller-usable spec exposure.

## Verification discipline

1. No `admit()` and no `assume`.
2. Verify every `.fsti` before its `.fst`.
3. Keep files small and split large modules before proof contexts become unstable.
4. Use `.fsti` files to hide proof bodies, isolate dependencies, and expose only caller-usable theorem statements.
5. Keep implementation postconditions connected to pure spec functions and state-machine transitions.
6. Put difficult mathematical facts in pure F* lemma modules rather than inline Pulse proof blocks.
7. Use explicit lemmas for sequence lengths, parser offsets, record nonce arithmetic, sequence-number bounds, HKDF label lengths, and transcript checkpoints.
8. Do not raise rlimits as the first response to failures. Use `proofdebugging` and `smtprofiling` early to identify failing queries, quantifier cascades, excessive unfolding, or context pollution.
9. Use `--query_stats --split_queries always` for failures before increasing rlimits; use `--log_queries --z3refresh` and Z3 quantifier profiling for slow or flaky queries.
10. Avoid broad error fallbacks. Every error result should correspond to a specified state-machine failure transition.
11. Treat HACL*, OpenSSL, parser/serializer C stubs, randomness, clock, trust store, and socket I/O as trusted boundaries with precise `.fsti` contracts.
12. Before introducing a custom data structure, helper library, or lemma family, check the existing Pulse and F* libraries and reuse their arrays, buffers, references, lists, sequences, machine integers, options/results, and proof lemmas when they fit.

## Main risks

1. Real HTTPS interop is substantially more work than the controlled OpenSSL TLS echo test because public endpoints require a non-trivial extension, WebPKI certificate, signature, ALPN, fragmentation, and I/O surface; keep it out of the first end-to-end gate.
2. Parser/serializer C code is trusted in v1; tests can reduce interop risk but do not provide a proof. A later verified parser/serializer should replace this trusted boundary, without assuming a Low* or LowParse direction.
3. OpenSSL X.509 verification is a trusted boundary; the proof can only show correct use of the validated identity, not correctness of OpenSSL itself.
4. HACL* FFI specs must match the checked-in C snapshot preconditions exactly, including buffer sizes, disjointness, aliasing, and failure behavior, without assuming HACL* is reverified in this repository.
5. Transcript/key-schedule byte exactness is fragile; RFC 8448 vector validation should precede network testing.
6. Partial network I/O must be modeled in the state machine from the start.
7. Downloading the latest F* release improves freshness but can reduce reproducibility; once a baseline verifies, pin a known-good release through a `setup.sh --version` path.
8. Large modules and globally visible proof helpers can make verification slow or flaky; enforce small modules, `.fsti` boundaries, low rlimits, and early SMT profiling from the beginning.
9. The GitHub MCP semantic-search requirement is not currently satisfiable in this CLI environment because no MCP semantic-search tool is exposed.

## Current trusted boundary audit

The default `make test-openssl-echo` client path now uses a concrete extracted connection wrapper type, extracted handshake wrapper state transitions, extracted handshake driver control flow, extracted encrypted-handshake byte-driver scheduling, extracted transcript hash routing and Finished comparison, extracted key schedule, extracted record seal/open, extracted no-padding TLSInnerPlaintext encode/decode, extracted record header construction/parsing, extracted ClientHello serialization, extracted ServerHello parsing/key-share extraction, extracted handshake header parsing, extracted Certificate parsing, and extracted CertificateVerify input/body parsing. The remaining trusted code in the default wrapper interop path is:

1. `tls13_connection_probe.c`
   - Raw socket orchestration, encrypted-record read/append, transcript byte storage, OpenSSL peer handle storage, per-record application-data seal/open hooks, and the remaining backend handle for the extracted connection.
   - Legacy cleanup completed: this file no longer has direct-probe or older extracted-driver preprocessor branches; it is built only as the backend for the extracted-wrapper OpenSSL interop path.
   - Replaced in the wrapper path so far: public `TLS13.Connection.connection` is now an extracted struct containing a trusted backend handle, runtime lifecycle marker, and extracted-owned client/server application traffic key/IV buffers populated after connect through a narrow backend key-export call, rather than a typedef alias of the C backend connection.
   - Default wrapper interop now links layered extracted `TLS13.Handshake` plus `TLS13.Handshake.Driver`, so the top-level handshake boundary is the explicit `TLS13.Handshake.External` ABI instead of direct `TLS13_Handshake_*` driver callbacks.
   - Replaced in the wrapper path so far: encrypted server-flight scheduling with a fuelled extracted recursive helper instead of a hard-coded nested cascade, server-handshake record open and client-Finished record seal sequence/nonce/AEAD orchestration, expected handshake message order, complete-message polling, wrong-type/incomplete-flight failure routing, and extracted flight-state ownership of cursor/checkpoint/saw-flag plus Certificate leaf/signature metadata and server Finished verify-data bookkeeping. `TLS13.Handshake.ByteDriver.External.fsti` now tracks an abstract progress state and proves successful extracted scheduling reaches `Complete`.
   - Replaced in the wrapper path so far: scoped transcript hash routing for both the handshake-secret checkpoint and server-flight checkpoints plus server Finished equality checking now run through extracted `TLS13.Handshake.Transcript`; the trusted SHA-256 primitive remains behind `TLS13.Handshake.Transcript.External`.
   - Replaced in the wrapper path so far: extracted `TLS13.Connection` now owns application-data write chunking and bounded read scheduling over extracted-owned application traffic keys and extracted application record-state objects; the C backend no longer exposes bulk application read/write functions and now only provides per-record hooks for this path.
   - Remaining TLS-owned work to replace: transcript byte-array ownership/copying, encrypted-handshake buffering, per-record application seal/open hooks, OpenSSL peer lifetime, raw partial-I/O buffering, close_notify and fragmentation handling.
2. `tls13_wire_stubs.c`
   - Still trusted for standalone parser/serializer C tests and for any future low-level parser/serializer ABI calls that have not yet moved into extracted code.
   - Replaced in the wrapper path so far: ClientHello serialization, record header write/read, TLSInnerPlaintext no-padding write/read including encrypted-handshake inner plaintext, scoped ServerHello parsing/key-share extraction, handshake header parse, CertificateVerify input construction, Certificate leaf-DER offset parsing for the scoped generated-certificate flight, and CertificateVerify body scheme/signature-length parsing.
3. `tls13_hacl_stubs.c` plus HACL* C snapshot
   - Trusted for SHA-256, HMAC, HKDF, X25519, nonce construction in non-wrapper paths, and ChaCha20-Poly1305 primitives. Extracted wrappers now orchestrate key schedule and record state, but cryptographic algorithms remain HACL* C.
4. `tls13_crypto_external.c`
   - Trusted ABI glue from extracted key-schedule/record modules to the HACL* C wrappers.
5. `tls13_openssl_stubs.c` plus OpenSSL
   - Trusted X.509 chain/hostname validation and signature verification.
6. `tls13_io_stubs.c`
   - Trusted TCP connect/read/write/close wrapper.
7. `tls13_pulse_shims.c`
   - Trusted shim for extracted Pulse array-copy helper.
8. Test harnesses
   - `test/openssl_echo_server.c`, generated test certificates, and the shell harness are test infrastructure, not verified code.

The next highest-value implementation step is to deepen the extracted byte driver by moving transcript accumulation, encrypted-handshake buffering, and Finished transcript checkpoint materialization out of `tls13_connection_probe.c`, while keeping HACL*, OpenSSL, raw I/O, and any not-yet-replaced parsers behind explicit trusted ABIs.

## Todos

1. [done] Use the pinned initial scope decisions: client-only, X25519, `TLS_CHACHA20_POLY1305_SHA256`, supported signature schemes, HRR abort behavior, controlled OpenSSL echo parameters, later public HTTPS endpoint, and trusted parser/serializer boundary for v1.
2. [done] Add dependency helpers and local caches: HACL* submodule, RFC 8446/RFC 8448 fetch script, OpenSSL availability check, and gitignore rules for downloaded/generated artifacts.
3. [done] Create the repository skeleton, `setup.sh`, Makefile, cache/extraction directories, and minimal verify/extract smoke modules using `tools/FStar`.
4. [done] Implement the pure TLS byte/types/state-machine specification modules. Initial abstract byte, TLS type, crypto spec, X.509 spec, transcript, key, record, handshake, wire, state-machine, and state-machine lemma modules verify with the repository-local F* toolchain, including a controlled-handshake path lemma that reaches application data for the scoped supported server hello.
5. [done] Define pure crypto and X.509 spec interfaces, including trusted-boundary documentation. Crypto is intentionally abstract/uninterpreted and tied to trusted FFI contracts rather than HACL* proof imports.
6. [in progress] Add Pulse `.fsti` contracts and C stubs for HACL*, OpenSSL, parser/serializer, randomness, clock, and I/O. Initial Pulse interfaces and placeholder C stub files are present and verify/compile-syntax; HACL* C snapshot wrappers for SHA-256, HMAC-SHA256, HKDF-SHA256/TLS HKDF labels, X25519, TLS record nonce construction, ChaCha20-Poly1305, contiguous TLS ciphertext+tag AEAD wrappers, and random bytes have C tests; OpenSSL X.509 validation has generated localhost certificates, hostname-validation tests, PEM-chain and DER-leaf validation tests, and RSA-PSS-RSAE-SHA256 signature verification tests over the validated leaf key; POSIX fd read/write and localhost TCP connect/close wrappers have tests. Remaining work is extracted-name wiring plus fuller wire/I/O implementations and broader vectors.
7. [in progress] Implement trusted C parser/serializer support for the scoped TLS messages and extensions, with `.fsti` contracts and vector tests. Initial TLS record-header, handshake-header, TLSInnerPlaintext encode/decode, scoped ClientHello serialization, scoped supported ServerHello parsing for TLS 1.3/X25519/`TLS_CHACHA20_POLY1305_SHA256`, Certificate leaf-DER extraction, CertificateVerify parsing support, and RFC 8446 server CertificateVerify input construction plus Pulse parse/serialize contracts and malformed-input tests are present. `TLS13.Wire.Spec.fsti` is no longer an uninterpreted wire boundary: it now has a concrete total F* implementation for the scoped handshake/record parse and serialize model, so the Pulse parse/serialize contracts refer to executable spec definitions instead of abstract functions. The wrapper path now uses extracted `TLS13.Handshake.Framing` for scoped ClientHello serialization, scoped ServerHello parsing/key-share extraction, Certificate leaf-DER offset parsing, and CertificateVerify body parsing; remaining C parser/serializer stubs are standalone test/TCB surfaces to eliminate, not alternate interop paths.
8. [in progress] Implement and verify transcript hash and TLS 1.3 key schedule; validate with RFC 8448 vectors. The pure key-schedule spec now includes fixed TLS 1.3 labels, early/handshake/master secret derivation, handshake/application traffic secrets, Finished-key/verify-data computation, exporter/resumption master secrets, and traffic key/IV derivation; `TLS13.KeySchedule.fsti` exposes Pulse-facing contracts for the named derivation steps; HACL wrapper tests include RFC 8448 simple 1-RTT handshake-secret extraction, client handshake traffic-secret HKDF-Expand-Label, transcript-hash, Finished-key, and server Finished verify-data vectors. `TLS13.KeySchedule.fst` now provides a verified Pulse implementation of the key-schedule wrapper layer: it constructs the exact TLS 1.3 labels with byte literals, uses stack-local Pulse arrays for temporaries, sequences the trusted crypto primitives, and proves each exported function writes the corresponding pure `TLS13.Keys` result. `TLS13.Handshake.Transcript.fst` now provides an extracted wrapper for the scoped ClientHello || ServerHello || server-handshake transcript hash plus an extracted 32-byte Finished comparison. The implementations still rely on trusted primitive boundaries for SHA-256/HKDF/HMAC/AEAD.
9. [done] Implement and verify the scoped no-padding ChaCha20-Poly1305 record protection/framing path for controlled echo interop. `TLS13.Record.fst` implements the Pulse-facing record-state wrapper with concrete vector-backed key/IV storage, boxed sequence/install state, verified key installation, application-data seal, and application-data open operations tied to `TLS13.Record.Spec`; the record epoch remains ghost/spec-only because it has no runtime role in AEAD protection. `TLS13.Record.Framing.fst` verifies and extracts no-padding TLSInnerPlaintext encoding for application-data writes, no-padding content-type/payload-length decoding for application-data reads, TLS 1.3 application-data record-header construction for writes, and record-header parsing for reads; the extracted-wrapper OpenSSL interop path uses these around extracted `TLS13.Record` seal/open. `extract-record-c` and `extract-record-framing-c` translate the verified code to C against the trusted crypto ABI and small Pulse shims, and binding/OpenSSL tests check uninstalled-state rejection, application-data seal/open, tamper rejection, and multi-record echo. Padding support, advanced buffering, and broader RFC record vectors remain under the verified wire-code and connection-I/O milestones.
10. [in progress] Implement and verify the scoped client handshake. The pure handshake spec now models RFC 8446 server CertificateVerify input with the 64-space prefix, context string, separator, and transcript hash, and exposes Finished verification against the key-schedule verify-data function. `TLS13.Handshake.fst` now implements the Pulse-facing handshake wrapper: it carries a monotonic `TLS13.State.state_ref`, calls a lower trusted byte-operation ABI, and proves each per-flight operation advances the state token to the corresponding success phase or to `Failed` on error. The default wrapper interop now links layered extracted `TLS13.Handshake` plus `TLS13.Handshake.Driver`, so these state transitions are in the runtime path. The extracted byte-driver layer has a stronger local progress contract (`ExpectEncryptedExtensions` through `Complete`) for the encrypted server flight, and `TLS13.Handshake.FlightState` now owns the runtime server-flight cursor/checkpoint/saw-flag state plus Certificate leaf and CertificateVerify signature metadata. `TLS13.Handshake.External.fsti` is still a broad trusted boundary for the top-level per-flight calls. The pure state machine makes successful certificate-chain validation an explicit `ValidateCertificate` event that stores the validated peer before CertificateVerify can advance. A ghost-only `TLS13.Handshake.StateDriver` verifies the controlled handshake by advancing the monotonic state token through every expected handshake event to `ApplicationData`, and `TLS13.Handshake.Driver` verifies the non-ghost control-flow spine that sequences the trusted handshake operations to either `ApplicationData` or `Failed`. `extract-handshake-c`, `extract-handshake-driver-c`, `extract-handshake-layered-c`, and `extract-handshake-flight-state-c` now emit C for the verified wrapper/driver/flight-state pieces; binding/OpenSSL tests check success and failure paths. Remaining work is to collapse the top-level `Handshake.External` trusted calls into extracted byte-driver/parser/transcript operations with payload-bearing postconditions.
11. [in progress] Implement and verify top-level connection read/write/close APIs. `TLS13.Connection.fst` now implements the top-level Pulse connection wrapper with a concrete extracted runtime `connection` struct around a lower trusted backend handle: allocation creates the backend handle, a runtime lifecycle marker, extracted-owned client/server application traffic key/IV buffers, extracted-owned client/server application record-state objects, and the monotonic state token; connect proves the controlled handshake transition to `ApplicationData` or `Failed` and installs exported application keys into extracted buffers; write/read advance record sequence state on successful application-data operations; and close advances to `Closing` or `Failed`. `TLS13.Connection` now also owns the application-data multi-record write chunking loop and bounded read scheduling loop over those extracted-owned keys/record states, replacing the old trusted bulk `client_write`/`client_write_all`/`client_read`/`client_read_exact` external calls with per-record backend hooks. `TLS13.Connection.Driver.connect_write_read_exact` verifies the end-to-end connect/write/read control-flow spine to either remain in `ApplicationData` on success or reach `Failed` on failure. Application-data and close_notify state-machine transitions advance the corresponding record-layer read/write sequence state, and a ghost-only `TLS13.Connection.StateDriver` verifies application-data send/receive echo transitions and close_notify progress over the same monotonic token. `extract-connection-c` and `extract-connection-driver-c` now emit C for the verified wrapper and driver; binding/OpenSSL tests check success and failure paths. Remaining connection work is to replace the per-record C hooks with Pulse-owned record framing/seal/open and raw socket read/write calls.
12. [in progress] Configure extraction and C linking with HACL* and OpenSSL. A first `extract-smoke`/`test-extract-smoke` path verifies a small extraction-safe F* module, emits C through KaRaMeL, compiles it, and checks exported TLS version/cipher-suite constants; `extract-key-schedule-c`, `extract-record-c`, `extract-record-framing-c`, `extract-handshake-framing-c`, `extract-handshake-flight-state-c`, `extract-handshake-transcript-c`, `extract-handshake-byte-driver-c`, `extract-handshake-c`, `extract-handshake-driver-c`, `extract-handshake-layered-c`, `extract-connection-c`, and `extract-connection-driver-c` now translate verified Pulse/F* modules to C against explicit trusted ABIs. Binding tests link the generated C against mock or HACL-backed implementations to check success/failure paths and key/record vectors. The OpenSSL echo smoke now has a single client route: `test/test_extracted_connection_wrapper_openssl` runs extracted `TLS13.Connection`, extracted `TLS13.Handshake`, extracted handshake driver, extracted encrypted-handshake byte driver, extracted handshake flight-state, extracted handshake transcript wrapper, extracted key schedule, extracted record wrapper, extracted no-padding record framing, extracted ClientHello/ServerHello/Certificate/CertificateVerify framing, and extracted CertificateVerify input framing against the scoped HACL*/OpenSSL/I/O probe backend, and checks both successful multi-record echo and wrong-CA rejection. Replacing the remaining trusted X.509, crypto, raw I/O, and connection-buffering backend pieces remains pending.
13. [in progress] Add RFC 8448 and extracted C vector tests. Initial RFC 8448 key-schedule vectors are covered through the HACL C wrapper test, and `test-key-schedule-bindings` now checks extracted key-schedule C for the RFC 8448 handshake secret and client handshake traffic secret plus traffic key/IV derivation against direct HACL* wrappers; full extracted TLS vector tests remain pending.
14. [done] Add the controlled OpenSSL TLS echo interop test as the first end-to-end networking target. A local OpenSSL TLS 1.3 echo server and `openssl s_client` smoke script exist for the pinned X25519/`TLS_CHACHA20_POLY1305_SHA256` server side, covering both short and multi-record-sized payloads; the single extracted-wrapper interop client routes through extracted `TLS13.Connection`, extracted handshake driver, extracted `TLS13.KeySchedule`, extracted `TLS13.Record`, extracted record/handshake framing, extracted transcript routing, and extracted handshake flight-state before reaching the remaining trusted byte operations. It checks both successful multi-record echo and rejection under a wrong generated CA. Replacing the remaining trusted byte parser, X.509, crypto, and I/O backend pieces remains tracked under the implementation work above.
15. [pending] Add public HTTPS interop tests only after the controlled echo test is stable.
16. [pending] Audit specs, interfaces, file sizes, proof stability, trusted boundaries, rlimits, and extraction output before declaring the implementation complete.
17. [in progress] Implement the extracted handshake byte driver so the OpenSSL echo path no longer relies on `tls13_connection_probe.c` for TLS-owned encrypted-handshake orchestration. The first extracted slice is now in the default interop path and owns complete-message polling, bounded encrypted-record scheduling, expected message order, and handshake failure routing for the scoped server flight. Remaining work: move transcript accumulation storage/copying, encrypted-handshake buffering, Finished transcript checkpoint materialization, and body parser implementations out of trusted C.
18. [pending] Implement extracted record framing around `TLS13.Record`, including TLS record header/AAD construction, TLSInnerPlaintext encode/decode, sequence overflow checks, and application-data buffering.
19. [pending] Replace trusted C parser/serializer stubs with verified extraction-ready Pulse/F* parsers/serializers for the scoped TLS 1.3 message set, tied to `TLS13.Wire.Spec`.
20. [in progress] Implement extracted connection I/O loops for partial reads/writes, multi-record app data, close_notify, and handshake records observed during application reads, leaving only raw socket read/write as trusted. First slice complete: extracted `TLS13.Connection` owns application write chunking, bounded read scheduling, and application record-state ownership; the backend only handles one application record at a time for this path.
21. [done] Delete the legacy OpenSSL interop paths. `make test-openssl-echo` now builds/runs only the extracted-wrapper client; the direct C probe target, older extracted-driver target, shell harness branch, and `tls13_connection_probe.c` preprocessor alternatives have been removed.
22. [pending] Perform the final TCB/ABI audit for HACL*, OpenSSL, randomness, time, socket I/O, allocation, and Pulse support shims, with explicit documentation of what remains outside the verified TLS client.
