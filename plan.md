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
10. For the first version, parser/serializer code is deliberately scoped behind trusted `.fsti` interfaces and implemented directly in unverified C stubs. Verified EverParse/LowParse parser generation is deferred to a later phase so the first milestone can focus on the core protocol state machine, key schedule, record layer, and handshake logic.
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
│       ├── TLS13.LowTypes.fsti
│       ├── TLS13.LowTypes.fst
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

This includes transcript consistency, key-schedule consistency, record protection/unprotection correctness relative to the AEAD spec, and correct binding between validated certificate identity, CertificateVerify, and the transcript. In v1, wire parser/serializer byte-level correctness is assumed through trusted `.fsti` contracts and validated with C/vector tests; the C parser/serializer implementation itself is not verified until the later EverParse/LowParse phase.

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

The verified core protocol code should operate on the abstract messages and byte sequences exposed by these contracts. Replacing these trusted stubs with EverParse/LowParse-generated verified code is a separate later phase.

## Implementation architecture

### Low-level representation

Use only extraction-ready concrete types in implementation code: `UInt8.t`, `UInt16.t`, `UInt32.t`, `UInt64.t`, `SizeT.t`, `bool`, stack arrays, heap boxes/vectors, and erased ghost state. Avoid `nat`, `int`, `list`, `string`, and `Seq.seq` in extractable positions.

Reuse existing Pulse, Low*, and F* libraries wherever possible instead of rebuilding basic data structures or proofs from scratch. Use the standard libraries for arrays/buffers, references, machine integers, options/results, sequences, lists, and common list/sequence/length lemmas; pure `FStar.Seq`/`FStar.List.Tot`-style structures are appropriate in specs and ghost code, while extraction-facing code should use the existing Pulse/Low* array, buffer, ownership, and integer libraries. Add a local wrapper only when it gives a TLS-specific abstraction or narrows an interface, not to reimplement a generic container such as an array, linked list, vector, option, or byte buffer.

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
5. Treat parser/serializer C code as part of the trusted computing base until a later EverParse/LowParse phase replaces it.

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
   - Defer EverParse/LowParse verification to a later phase.

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
12. Before introducing a custom data structure, helper library, or lemma family, check the existing Pulse, Low*, and F* libraries and reuse their arrays, buffers, references, lists, sequences, machine integers, options/results, and proof lemmas when they fit.

## Main risks

1. Real HTTPS interop is substantially more work than the controlled OpenSSL TLS echo test because public endpoints require a non-trivial extension, WebPKI certificate, signature, ALPN, fragmentation, and I/O surface; keep it out of the first end-to-end gate.
2. Parser/serializer C code is trusted in v1; tests can reduce interop risk but do not provide a proof. EverParse/LowParse should replace this trusted boundary in a later phase.
3. OpenSSL X.509 verification is a trusted boundary; the proof can only show correct use of the validated identity, not correctness of OpenSSL itself.
4. HACL* FFI specs must match the checked-in C snapshot preconditions exactly, including buffer sizes, disjointness, aliasing, and failure behavior, without assuming HACL* is reverified in this repository.
5. Transcript/key-schedule byte exactness is fragile; RFC 8448 vector validation should precede network testing.
6. Partial network I/O must be modeled in the state machine from the start.
7. Downloading the latest F* release improves freshness but can reduce reproducibility; once a baseline verifies, pin a known-good release through a `setup.sh --version` path.
8. Large modules and globally visible proof helpers can make verification slow or flaky; enforce small modules, `.fsti` boundaries, low rlimits, and early SMT profiling from the beginning.
9. The GitHub MCP semantic-search requirement is not currently satisfiable in this CLI environment because no MCP semantic-search tool is exposed.

## Todos

1. [done] Use the pinned initial scope decisions: client-only, X25519, `TLS_CHACHA20_POLY1305_SHA256`, supported signature schemes, HRR abort behavior, controlled OpenSSL echo parameters, later public HTTPS endpoint, and trusted parser/serializer boundary for v1.
2. [done] Add dependency helpers and local caches: HACL* submodule, RFC 8446/RFC 8448 fetch script, OpenSSL availability check, and gitignore rules for downloaded/generated artifacts.
3. [done] Create the repository skeleton, `setup.sh`, Makefile, cache/extraction directories, and minimal verify/extract smoke modules using `tools/FStar`.
4. [done] Implement the pure TLS byte/types/state-machine specification modules. Initial abstract byte, TLS type, crypto spec, X.509 spec, transcript, key, record, handshake, wire, state-machine, and state-machine lemma modules verify with the repository-local F* toolchain, including a controlled-handshake path lemma that reaches application data for the scoped supported server hello.
5. [done] Define pure crypto and X.509 spec interfaces, including trusted-boundary documentation. Crypto is intentionally abstract/uninterpreted and tied to trusted FFI contracts rather than HACL* proof imports.
6. [in progress] Add Pulse `.fsti` contracts and C stubs for HACL*, OpenSSL, parser/serializer, randomness, clock, and I/O. Initial Pulse interfaces and placeholder C stub files are present and verify/compile-syntax; HACL* C snapshot wrappers for SHA-256, HMAC-SHA256, HKDF-SHA256/TLS HKDF labels, X25519, TLS record nonce construction, ChaCha20-Poly1305, contiguous TLS ciphertext+tag AEAD wrappers, and random bytes have C tests; OpenSSL X.509 validation has generated localhost certificates, hostname-validation tests, PEM-chain and DER-leaf validation tests, and RSA-PSS-RSAE-SHA256 signature verification tests over the validated leaf key; POSIX fd read/write and localhost TCP connect/close wrappers have tests. Remaining work is extracted-name wiring plus fuller wire/I/O implementations and broader vectors.
7. [in progress] Implement trusted C parser/serializer support for the scoped TLS messages and extensions, with `.fsti` contracts and vector tests. Initial TLS record-header, handshake-header, TLSInnerPlaintext encode/decode, scoped ClientHello serialization, scoped supported ServerHello parsing for TLS 1.3/X25519/`TLS_CHACHA20_POLY1305_SHA256`, Certificate leaf-DER extraction, CertificateVerify parsing support, and RFC 8446 server CertificateVerify input construction plus Pulse parse/serialize contracts and malformed-input tests are present.
8. [in progress] Implement and verify transcript hash and TLS 1.3 key schedule; validate with RFC 8448 vectors. The pure key-schedule spec now includes fixed TLS 1.3 labels, early/handshake/master secret derivation, handshake/application traffic secrets, Finished-key/verify-data computation, exporter/resumption master secrets, and traffic key/IV derivation; `TLS13.KeySchedule.fsti` exposes Pulse-facing contracts for the named derivation steps; HACL wrapper tests include RFC 8448 simple 1-RTT handshake-secret extraction, client handshake traffic-secret HKDF-Expand-Label, transcript-hash, Finished-key, and server Finished verify-data vectors. Concrete Pulse implementation remains pending.
9. [in progress] Implement and verify ChaCha20-Poly1305 record protection/unprotection. A Pulse-facing `TLS13.Record.fsti` contract now exposes record-state allocation/free, key installation, application-data seal, and application-data open operations tied to `TLS13.Record.Spec`; C smoke coverage now combines TLSInnerPlaintext, record AAD, nonce construction, ChaCha20-Poly1305 seal/open, and tamper rejection. Concrete Pulse implementation and RFC record vectors remain pending.
10. [in progress] Implement and verify the scoped client handshake. The pure handshake spec now models RFC 8446 server CertificateVerify input with the 64-space prefix, context string, separator, and transcript hash, and exposes Finished verification against the key-schedule verify-data function. A Pulse-facing `TLS13.Handshake.fsti` exposes the client handshake context and per-flight send/receive contracts, each tied to `TLS13.StateMachine.step`; the context predicate now carries a monotonic `TLS13.State.state_ref` so all transitions must preserve the same ghost state token. The pure state machine now makes successful certificate-chain validation an explicit `ValidateCertificate` event that stores the validated peer before CertificateVerify can advance. A ghost-only `TLS13.Handshake.StateDriver` verifies the controlled handshake by advancing the monotonic state token through every expected handshake event to `ApplicationData`, and `TLS13.Handshake.Driver` now verifies the non-ghost control-flow spine that sequences the trusted handshake operations to either `ApplicationData` or `Failed`. Concrete byte-level trusted-operation implementations remain pending.
11. [in progress] Implement and verify top-level connection read/write/close APIs. The top-level Pulse `.fsti` connection contract exists and ties allocation, connect, read, write, close, and free to `TLS13.StateMachine` phases and the trusted I/O boundary; the connection predicate now carries the monotonic state token that concrete implementations must advance through legal transitions. `client_connect` now returns a success bit whose postcondition distinguishes `ApplicationData` from `Failed`, making it composable for verified callers. Trusted `client_write_all` and `client_read_exact` contracts plus `TLS13.Connection.Driver.connect_write_read_exact` now verify the end-to-end connect/write/read control-flow spine to either remain in `ApplicationData` on success or reach `Failed` on failure. Application-data and close_notify state-machine transitions now advance the corresponding record-layer read/write sequence state, and a ghost-only `TLS13.Connection.StateDriver` verifies application-data send/receive echo transitions and close_notify progress over the same monotonic token. Concrete byte-level implementation remains pending.
12. [in progress] Configure extraction and C linking with HACL* and OpenSSL. A first `extract-smoke`/`test-extract-smoke` path verifies a small extraction-safe F* module, emits C through KaRaMeL, compiles it, and checks exported TLS version/cipher-suite constants; `extract-connection-driver-krml` now emits KRML for the verified `TLS13.Connection.Driver` control-flow spine using the verified project cache. `extract-connection-driver-c` now translates that KRML to C against an explicit external C ABI for the trusted driver-used `TLS13.Connection` operations, and `test-connection-driver-bindings` links the generated driver against a mock implementation to check success and short-circuit failure paths. The real trusted `TLS13.Connection` C implementation and full extracted-client linking remain pending.
13. [in progress] Add RFC 8448 and extracted C vector tests. Initial RFC 8448 key-schedule vectors are covered through the HACL C wrapper test, and extraction smoke covers generated C compilation; full extracted TLS vector tests remain pending.
14. [in progress] Add the controlled OpenSSL TLS echo interop test as the first end-to-end networking target. A local OpenSSL TLS 1.3 echo server and `openssl s_client` smoke script exist for the pinned X25519/`TLS_CHACHA20_POLY1305_SHA256` server side, now covering both short and multi-record-sized payloads; a C probe sends the scoped ClientHello built by our wire serializer, parses OpenSSL's ServerHello, Certificate, and CertificateVerify with the trusted parser stubs, derives handshake/application traffic keys with the HACL* wrappers, decrypts OpenSSL encrypted handshake records, validates the server DER leaf certificate against the generated test CA, verifies CertificateVerify using the reusable RFC 8446 input builder and verifies server Finished against the transcript, sends client Finished, sends a multi-record application-data payload, and decrypts/reassembles the exact OpenSSL echo. The same probe is also checked to reject the OpenSSL server under a wrong generated CA. The extracted verified client still needs to replace both `s_client` and the C probe for the full verified echo path.
15. [pending] Add public HTTPS interop tests only after the controlled echo test is stable.
16. [pending] Audit specs, interfaces, file sizes, proof stability, trusted boundaries, rlimits, and extraction output before declaring the implementation complete.
