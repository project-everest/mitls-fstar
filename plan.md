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
10. Parser/serializer code is deliberately scoped, but the default path has moved past the original trusted-C-stub plan: supported record and handshake framing now lives in extracted Pulse/F* modules tied to `TLS13.Wire.Spec`. Do not reintroduce trusted C byte parsers or Low*/LowParse unless that direction is explicitly chosen and documented in the TCB audit.
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
│       ├── TLS13.Record.Framing.fsti
│       ├── TLS13.Record.Framing.fst
│       ├── TLS13.Handshake.Framing.fsti
│       ├── TLS13.Handshake.Framing.fst
│       ├── TLS13.Handshake.FlightState.fsti
│       ├── TLS13.Handshake.FlightState.fst
│       ├── TLS13.Handshake.Transcript.fsti
│       ├── TLS13.Handshake.Transcript.fst
│       ├── TLS13.Handshake.ByteDriver.fst
│       ├── TLS13.Crypto.fsti
│       ├── TLS13.Crypto.fst
│       ├── TLS13.X509.fsti
│       ├── TLS13.X509.fst
│       ├── TLS13.Record.fsti
│       ├── TLS13.Record.fst
│       ├── TLS13.Connection.Backend.fsti
│       ├── TLS13.Handshake.fsti
│       ├── TLS13.Handshake.fst
│       ├── TLS13.Connection.fsti
│       └── TLS13.Connection.fst
├── c_stubs/
│   ├── tls13_hacl_stubs.c
│   ├── tls13_hacl_stubs.h
│   ├── tls13_openssl_stubs.c
│   ├── tls13_openssl_stubs.h
│   ├── tls13_io_stubs.c
│   ├── tls13_io_stubs.h
│   ├── tls13_connection_backend.h
│   └── tls13_connection_backend_openssl.c
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

`setup.sh` installs the project-local F*/KaRaMeL toolchain into `tools/FStar`; `.gitignore` should exclude `tools/FStar`, `_cache`, `_output`, `_extract`, and other generated files. `src/spec` contains pure F* specifications using unbounded types, sequences, and mathematical models. `src/impl` contains extraction-ready Pulse/F* using machine integers, arrays/vectors, erased ghost models, and `.fsti` interfaces that expose functional correctness postconditions. Extraction-facing implementation APIs must use C-shaped data (`array U8.t`, `vec U8.t`, machine integers, booleans, structs, and out-parameters); `TLS13.Bytes.bytes = Seq.seq byte` is only the erased/spec model used in ghost snapshots and postconditions. The old declaration-only `TLS13.Parse.fsti` and `TLS13.Serialize.fsti` implementation interfaces have been deleted because they returned spec-level messages/`Seq` values and were not extraction-safe runtime APIs. `c_stubs` contains the trusted C bindings to HACL*, OpenSSL, randomness, clock, socket/BIO I/O, and temporary test-backend glue.

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

This includes transcript consistency, key-schedule consistency, record protection/unprotection correctness relative to the AEAD spec, and correct binding between validated certificate identity, CertificateVerify, and the transcript. For the current scoped message set, wire parser/serializer byte-level correctness is implemented by extracted Pulse/F* framing modules and tied back to `TLS13.Wire.Spec`; the remaining proof task is strengthening exported postconditions and vector breadth, not trusting standalone C parsers.

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

### Scoped wire parser/serializer interface

`TLS13.Wire.Spec`, `TLS13.Record.Framing`, and `TLS13.Handshake.Framing` now form the scoped parser/serializer boundary. Earlier trusted C wire stubs have been removed from the default build, and the legacy declaration-only `TLS13.Parse.fsti`/`TLS13.Serialize.fsti` implementation interfaces have been deleted because they exposed extraction-hostile spec-level return values. The remaining work is to strengthen the exposed functional specs and broaden vectors for the currently supported TLS 1.3 message surface:

1. Pure spec functions may return abstract messages over `TLS13.Bytes.bytes`.
2. Extraction-facing parsing/framing functions must consume `array U8.t` plus lengths and return booleans, machine integers, or write to caller-provided output buffers; they must not return `Seq`, lists, or spec-level messages at runtime.
3. Parse success must expose, in ghost postconditions, equality to the pure parser result for the consumed bytes and the specified encoded length/cursor advancement.
4. Parse failure returns a specified TLS error/alert outcome and does not silently normalize malformed input.
5. Serialize success writes exactly the pure serialized bytes into an output buffer and reports success/length through extraction-safe values.
6. Serialize failure corresponds to explicit output-buffer-too-small or unsupported-message results.
7. Contracts include all length bounds, output buffer ownership, cursor advancement, and mutation effects.

The verified core protocol code should operate on concrete arrays/vectors at runtime while using erased snapshots and `TLS13.Wire.Spec` facts to relate those bytes to abstract messages. Low* and LowParse are not part of the current plan; if parser/serializer scope grows beyond the current handwritten extracted modules, extend the same `TLS13.Wire.Spec`-connected approach before adding another trusted byte parser.

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

The v1 parser/serializer strategy has moved past the original trusted-C-stub plan. The scoped record and handshake framing/parsing logic used by the default OpenSSL wrapper path is extracted Pulse/F* code tied to `TLS13.Wire.Spec`; parser/serializer C stubs are no longer built.

The remaining v1 parser/serializer work is:

1. Keep pure parser/serializer specs for supported TLS records, handshake messages, and extensions executable and caller-usable.
2. Ensure every exported framing/parsing `.fsti` postcondition refers to the `TLS13.Wire.Spec` model or a small interface predicate that exposes the same correctness fact, while keeping runtime signatures extraction-safe.
3. Broaden vector coverage for RFC 8448 bytes, supported OpenSSL server flights, fragmented encrypted handshake records, padded TLSInnerPlaintext, malformed lengths, wrong handshake message order, unsupported versions/groups/ciphers, and HRR-as-abort.
4. Keep unsupported message surfaces explicit failures; do not silently accept, normalize, or skip malformed input.
5. If a future parser/serializer expansion needs a new trusted byte boundary, document it in the TCB audit before it enters the default interop path.

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

### Layered ghost-log specification model

The connection invariant should be organized around append-only ghost logs, with each layer deriving a more semantic view from the lower layer:

1. **Raw network truth**: the trusted I/O/backend channel owns two monotonic byte streams, `raw_sent` and `raw_received`, representing exactly the TCP bytes written to and read from the socket so far. This is the lowest-level ghost truth. `write` appends the exact bytes successfully written to `raw_sent`; `read` appends the exact bytes returned by the OS to `raw_received`. Partial reads/writes are ordinary log-prefix extensions, not hidden state changes.
2. **TLS wire view**: pure prefix parsers and serializers relate the raw byte streams to a stream view of TLS records and, after record protection is applied, to handshake, alert, and application-data messages. This view must carry residual bytes for incomplete TCP prefixes. It must not require every current raw prefix to parse as a complete message: a live TCP stream can end in the middle of a record or in the middle of a fragmented handshake message. Malformed complete prefixes produce explicit failure facts/events.
3. **Record and handshake message view**: encrypted TLS 1.3 records are related to semantic messages only through the current record direction state, traffic keys, sequence numbers, AAD, AEAD open/seal, and TLSInnerPlaintext decoding. Handshake messages may be fragmented or coalesced across records, so the message view is a reassembly view over decrypted handshake bytes, not a one-record-to-one-message relation.
4. **Host state-machine trace**: the TLS message view plus local semantic events, such as certificate-validation success/failure and CertificateVerify verification, determines a list of `TLS13.StateMachine.event` values. The connection predicate should prove `TLS13.StateMachine.step_many TLS13.StateMachine.initial events == Some state`, and the monotonic state token should be the current endpoint of that trace.
5. **Application projection**: the public API exposes only the application-level projection of the trace: application bytes successfully sent, application bytes received, close/failure status, and possibly peer identity after connect. Internal TLS handshake, record, alert, key-schedule, transcript, and raw-byte facts remain hidden behind caller-usable abstract predicates and lemmas.

This becomes the main internal invariant of `TLS13.Connection`: the runtime connection object, the backend channel, record states, transcript/key material, pending plaintext buffer, state token, raw byte logs, TLS message logs, state-machine trace, and application projection all describe the same history at different abstraction levels.

Current implementation status for this model:

1. `TLS13.ConnectionLog` is a verified pure vocabulary for the layered view. It defines raw sent/received byte logs, prefix TLS stream views with residuals, host traces, application-log projection, a combined `connection_view`, public application projection predicates, and monotonic view-transition helpers for state sync, handshake completion/failure/close, and application send/receive events.
2. `TLS13.State` now owns two erased monotonic ghost resources: the existing state-machine token and a new connection-log token. The new `log_ref`, `log_current`, `alloc_initial_log`, and `advance_log` helpers mirror the state-token pattern and are ghost-only.
3. `TLS13.Connection.fsti/.fst` thread the log token through the public connection predicate. The main predicate is now explicitly raw-founded: `is_connection c st s lg raw app` owns the backend/handshake context at `raw`, owns `ST.log_current lg view`, requires `view.raw_log == raw`, requires the sent/received stream residuals to be the raw-byte suffixes of `raw.raw_sent`/`raw.raw_received`, and requires the public `app` log to be the application-data projection of `view.host_trace`. Public API postconditions still expose application-level deltas for successful writes/reads, plus ghost-only monotonic raw-log extension facts for the internal invariant.
4. `TLS13.Connection.Driver` propagates the same app-log projection and raw-log monotonicity through the end-to-end connect/write/read-exact control-flow spine, so callers can reason about the public application history while the proof keeps the raw TCP foundation explicit.
5. The runtime ABI remains extraction-safe: all new log state is erased ghost state and no runtime `Seq`, list, or spec-level TLS message value is introduced into extracted positions.
6. Raw-log ownership has been pushed through the TLS-facing backend and verified stack: `TLS13.Connection.Backend.fsti` carries `CL.raw_io_log`, raw read/write contracts append exact buffer slices, `TLS13.Handshake`, `TLS13.Handshake.ByteDriver`, `TLS13.Handshake.Driver`, `TLS13.Connection`, and `TLS13.Connection.Driver` thread those logs, and the top-level `TLS13.Connection.is_connection` now makes the raw log an explicit ghost argument tying the backend raw log to `ST.log_current` for the layered connection view.
7. The top-level layered view now includes an explicit TLS record prefix layer. `TLS13.ConnectionLog` stores sent/received `stream_view tls_record` values, recomputes them from `raw.raw_sent`/`raw.raw_received` with `TLS13.Wire.Spec.parse_record`, and proves the resulting parser views have consumed/residual prefix shape. This makes raw bytes -> parsed record prefixes evident before the later AEAD/TLSInnerPlaintext/handshake-message semantic relation.
8. The record prefix layer now has a parser/serializer soundness theorem. `TLS13.Wire.Spec.lemma_parse_record_serializes` proves that every accepted parsed record serializes back to the exact raw prefix it consumed, and `TLS13.ConnectionLog.lemma_parse_record_prefix_serializes` lifts that to whole parsed record-prefix streams.
7. Validation after wiring this slice: `make verify` and `make test test-openssl-echo` pass with the repository-local toolchain. After removing the transcript-specific C shim, `make extract-handshake-transcript-c`, `make test-openssl-echo`, and `make test` also pass.

The remaining refinement is below the current raw-stream-shaped connection view, not more trusted C protocol logic. `TLS13.ConnectionLog.bytes_extends` now expresses true byte-prefix preservation, not just length monotonicity: `old` must equal the prefix slice of `next`, and raw sent/received append lemmas prove exact prefix preservation. `TLS13.ConnectionLog.connection_view_record_stream_shaped` is now part of the top-level connection invariant, so sent/received TLS record views are the prefix parses of the raw sent/received byte streams and their residuals are the unparsed raw suffixes. `TLS13.ConnectionLog.connection_view_raw_stream_shaped` is also part of the invariant for the staged TLS message streams, and `TLS13.ConnectionLog.connection_view_app_projected` ensures the public application log is not an ad hoc field: it is the projection of the internal host trace. The next proof-surface tasks are to refine this staged raw/TLS relation into AEAD/TLSInnerPlaintext/handshake-reassembly views with residual prefixes, and optionally move the raw-log token from the TLS-facing backend boundary into `TLS13.IO.fsti` if we want the abstract channel itself, rather than the backend wrapper around it, to own the lowest-level ghost log.

Important design details:

1. The raw-to-TLS relation should be a prefix relation with residual buffers, not a total parse of the whole current TCP stream.
2. Sent-side TLS records are related to raw bytes by serialization plus record sealing; received-side TLS records are related by parsing plus record opening. For encrypted epochs, "serialize message equals raw bytes" is false unless the relation includes the record state and AEAD result.
3. ChangeCipherSpec compatibility records and ignored post-handshake handshake messages should appear in the TLS wire view but should either map to no state transition or to an explicitly specified ignored-event relation.
4. Certificate validation is not a network message. It should be a local event in the host trace linked to the preceding Certificate message, the backend/X.509 trusted boundary, and the peer identity installed in the state machine.
5. Failures must be specified as trace/log facts too: malformed records, bad tags, wrong-order messages, unsupported parameters, bad certificates, and I/O errors should advance to a specified failure event instead of disappearing behind `false`/`ok` postconditions.

### Controlled OpenSSL TLS echo interop

Before any public HTTPS endpoint, add a local OpenSSL interop test that exercises exactly the TLS functionality we intend to verify:

1. Build a tiny OpenSSL-based TLS 1.3 echo server in `test/openssl_echo_server.c`, or use `openssl s_server` only if it provides the exact byte-for-byte behavior needed by the harness.
2. Generate a local test CA and localhost leaf certificate during the test setup; do not depend on the host trust store.
3. Pin the server to X25519 and `TLS_CHACHA20_POLY1305_SHA256` so the test exercises the scoped first-version key exchange and record algorithm.
4. Disable client authentication, PSK, session resumption, 0-RTT, and ALPN initially.
5. Have the extracted client connect to `localhost`, validate the test certificate chain/hostname through the OpenSSL X.509 FFI, complete the handshake, send known application-data byte strings, and require exact echoed bytes in response.
6. Include short payloads, payloads spanning more than one record, and server-side fragmentation/partial-read cases so the connection driver and buffering logic are tested before public-network interop.
7. Treat this as a TLS application-data interop milestone. It does not prove HTTP parsing, HTTP semantics, WebPKI behavior, or broad endpoint compatibility.

## Status checkpoint: 2026-05-24

We are past the first end-to-end milestone: the repository-local toolchain verifies the current F*/Pulse modules, extracts the scoped TLS client pieces to C, links them with HACL*/OpenSSL/IO stubs, and the default controlled OpenSSL echo path uses the extracted wrapper route rather than a direct trusted C TLS probe. The current default path is a scoped TLS 1.3 client for X25519, `TLS_CHACHA20_POLY1305_SHA256`, no PSK, no 0-RTT, no client auth, no resumption, and no key update.

Current evidence:

1. A clean validation run, `make clean && make test test-openssl-echo`, passes with the local `tools/FStar` F*/KaRaMeL toolchain and the generated OpenSSL echo harness.
2. `make test-connection-bindings` covers short raw transport reads/writes, split reads from one decrypted record, multi-record `read_exact`, padded application records, encrypted close_notify, and every currently mapped encrypted fatal alert description.
3. `make test-openssl-echo` passes against the generated localhost CA/leaf certificate and pinned OpenSSL TLS 1.3 echo server; the extracted wrapper now performs repeated application writes/reads on one TLS connection for 1-byte, small split-read, 4096-byte record-boundary, 4097-byte record-plus-one, and 40000-byte multi-record payloads before sending close_notify, and the harness still checks wrong-CA rejection.
4. The default interop client path runs extracted `TLS13.Connection`, `TLS13.Handshake`, `TLS13.Handshake.Driver`, `TLS13.Handshake.ByteDriver`, `TLS13.Handshake.FlightState`, `TLS13.Handshake.Transcript`, `TLS13.KeySchedule`, `TLS13.Record`, `TLS13.Record.Framing`, and `TLS13.Handshake.Framing` before reaching trusted HACL*, OpenSSL X.509/signature validation, randomness, raw socket I/O, and small extraction/Pulse shims.

Relative to the end goal, the core scoped TLS-owned protocol path exists and interoperates locally, but it is not ready to call complete. The gap is no longer "build a TLS client from scratch"; it is now "harden and audit the extracted scoped client until the only trusted components are the intended crypto/X.509/randomness/time/socket/allocation boundaries, with enough vectors and spec exposure to support a credible verification claim."

The shortest path to completion is:

1. Continue fragmentation and buffering hardening for the already-extracted wrapper path. Repeated application writes on one connection, record-boundary reads, multi-record reads, split reads from buffered plaintext, short raw reads/writes, post-handshake handshake-record skipping, close_notify send/receive shape, and encrypted alert mapping now have initial coverage; remaining work is to add malformed and adversarial vectors, peer close_notify interop assertions where observable, and encrypted-handshake fragmentation/wrong-order coverage.
2. Continue strengthening `.fsti` surfaces. The connection API now exposes application-log deltas through the layered ghost-log model, and `TLS13.Connection.Backend.fsti` now owns the TLS-facing raw byte log with exact read/write append contracts. The next step is to refine the internal TLS wire/message view against `TLS13.Wire.Spec`, `TLS13.Keys`, `TLS13.Record.Spec`, and the state-machine trace; `TLS13.IO.fsti` remains an opaque lower POSIX channel boundary below the backend unless we decide to move the same raw-log token one layer lower.
3. Broaden RFC/OpenSSL vectors for scoped parser/framing, key schedule, record protection, handshake transcript, CertificateVerify input, Finished verification, malformed inputs, wrong message order, and unsupported features that should fail.
4. Keep the residual backend ABI limited to raw transport plus explicit OpenSSL certificate/signature calls; do not reintroduce TLS-owned byte parsing, buffering, key scheduling, record protection, alert policy, or application-data loops in trusted C.
5. Perform the final TCB/proof-stability audit: no project `admit`/`assume`, no silent fallbacks, stable low-rlimit verification, documented KaRaMeL warnings, and precise contracts/tests for every trusted C boundary.
6. Only then consider public HTTPS interop as a compatibility milestone, not as part of the core local verified-client claim.

## Current verified interop status and full-client roadmap

The controlled OpenSSL echo test now defaults to the extracted-wrapper client path:

1. The extracted-wrapper path is now the only OpenSSL echo client path. It runs extracted `TLS13.Connection`, extracted `TLS13.Handshake`, extracted `TLS13.Handshake.Driver`, extracted `TLS13.Handshake.ByteDriver`, extracted `TLS13.Handshake.FlightState`, extracted `TLS13.Handshake.Transcript`, extracted `TLS13.KeySchedule`, extracted `TLS13.Record`, extracted `TLS13.Record.Framing`, and extracted `TLS13.Handshake.Framing` in the default interop test. This path proves the modeled connection/handshake sequencing, extracted scoped ClientHello serialization, extracted scoped ServerHello parsing/key-share extraction, encrypted-handshake message scheduling for the scoped OpenSSL server flight, extracted server-handshake record open sequence/nonce/AEAD orchestration, extracted client-Finished record seal sequence/nonce/AEAD orchestration, one-shot transcript hash routing for both the ClientHello||ServerHello handshake-secret checkpoint and the scoped full transcript shape, extracted Finished compare, key-schedule label/derivation orchestration, Finished verify-data routing, CertificateVerify input construction, Certificate leaf-DER offset parsing, CertificateVerify body length/scheme parsing, application record seal/open wrapper behavior, application read record-header parsing/open/decode/copy, and no-padding application record framing before calling the remaining trusted backend.
2. The legacy direct C probe and older extracted-driver OpenSSL routes have been removed from the Makefile, shell harness, and test sources. The old core protocol `External.fsti` files (`TLS13.Connection.External`, `TLS13.Handshake.External`, and `TLS13.Handshake.ByteDriver.External`) and their C ABI headers have been deleted. `TLS13.Handshake.Transcript.External.fsti` and `tls13_handshake_transcript_external.c/.h` are also gone: transcript concatenation is now verified Pulse code in `TLS13.Handshake.Transcript.fst`, which calls the existing `TLS13.Crypto.sha256` primitive ABI.

For the purposes of this project, "full verified TLS client from Pulse to C in the interop tests" means that the OpenSSL echo path should execute extracted verified Pulse/F* code for all TLS protocol logic we own: handshake state progression, transcript bookkeeping, key schedule orchestration, record sequence/nonce/AAD/inner-plaintext handling, supported-message parsing/serialization, application-data buffering, and connection read/write/close state. HACL*'s checked-in C snapshot, OpenSSL X.509/signature validation, OS randomness, clock, and socket I/O remain explicit trusted components with precise local `.fsti` contracts unless the user later expands the scope.

The remaining work to reach the scoped verified-client goal, in order, is:

1. **Handshake byte-driver hardening**: the extracted handshake path now owns ClientHello construction, ClientHello transcript storage, TCP connect sequencing, exact-byte writes over raw short transport calls, exact-byte reads over raw short transport calls, TLS record-header parsing for the initial ServerHello record and encrypted server-flight records, scoped ServerHello body parsing/key-share extraction, encrypted server-flight scheduling, CCS compatibility handling, expected EncryptedExtensions/Certificate/CertificateVerify/Finished order, and failure routing for wrong type or incomplete flight. Remaining work is to add vectors for fragmented encrypted-handshake records, wrong-order encrypted handshake messages, HRR-as-abort, unsupported groups/ciphers/signature schemes, and malformed encrypted server-flight boundaries.
2. **Record framing and TLSInnerPlaintext**: the extracted `TLS13.Record` wrapper owns AEAD seal/open state; `TLS13.Record.Framing` provides no-padding application-data writes, padded application-data reads, encrypted-handshake no-padding reads, TLS 1.3 application-data record-header construction, and record-header parsing. New connection/OpenSSL vectors cover repeated records on one connection, exact record-boundary payloads, record-plus-one payloads, split reads, multi-record reads, padded application records, encrypted close_notify, and mapped encrypted fatal alerts. Remaining work is vector breadth for empty-ish inner plaintext edge cases, malformed record lengths, non-application outer content types after the handshake, AEAD failure, sequence-number overflow behavior, and RFC 8448 record bytes where available.
3. **Scoped parser/serializer spec exposure**: trusted C wire stubs are gone from the default build. The remaining parser/serializer task is to make the extracted `.fsti` surfaces obviously useful to callers: postconditions should reference concrete `TLS13.Wire.Spec` functions for ClientHello, ServerHello, Certificate leaf extraction, CertificateVerify body/input parsing, Finished bytes, record headers, and TLSInnerPlaintext, with exported lemmas for length/cursor facts that downstream modules need.
4. **Connection buffering and partial I/O**: the extracted `TLS13.Connection` application-I/O slice owns multi-record write chunking, bounded read-record scheduling, exact-byte loops over short raw transport reads/writes, read record-header parse/open/decode/copy, pending plaintext buffering for oversized application records, post-handshake handshake-record skipping, receive-side close_notify, receive-side peer-alert routing, and send-side close_notify seal/write. Newly added binding/OpenSSL vectors cover the main happy-path fragmentation cases and all currently mapped encrypted alert descriptions; remaining work is adversarial malformed input coverage, more close_notify interop observability, and negative tests for buffering boundary failures.
5. **Residual C backend boundary**: the backend is now `TLS13.Connection.Backend.fsti`, `c_stubs/tls13_connection_backend.h`, and `c_stubs/tls13_connection_backend_openssl.c`. It exposes only backend allocation/free, TCP connect, raw short read/write, certificate validation, CertificateVerify signature verification, and close. Its Pulse contract owns the TLS-facing raw sent/received byte log: successful writes append exactly the slice written to `raw_sent`, successful reads append exactly the slice returned into the caller buffer to `raw_received`, and connect/validation/signature/close preserve that raw log. The backend C header is scoped to this ABI; extraction rules include the crypto primitive header explicitly instead of hiding that dependency behind the backend header. It keeps host/port/CA-path/fd/validated-peer lifetime, but it does not parse TLS records/handshake messages, derive keys, seal/open records, buffer application data, map alerts, or run exact-read/exact-write protocol loops.
6. **ABI and TCB audit**: audit HACL* wrappers, OpenSSL X.509/signature wrappers, randomness, time, socket I/O, allocation, and small Pulse support shims. Each trusted function needs a local `.fsti` contract, C-side precondition checks, negative tests for edge cases, and no silent success-shaped fallback.
7. **Interop gate update**: the extracted-wrapper path is the only `make test-openssl-echo` client path. The direct C probe and older extracted-driver diagnostic routes have been deleted. Once fragmentation/alert/close coverage is broad enough, freeze this as the local interop gate before starting public HTTPS compatibility.

## Build, verification, and extraction plan

1. Add `.gitignore`, `setup.sh`, `Makefile`, and directory skeleton.
2. Add dependency helpers for local RFC caches, the HACL* submodule, and OpenSSL system-dependency checks.
3. Implement `setup.sh` to download the latest F* binary release into `tools/FStar`, with an optional version override for reproducibility, and create the local KaRaMeL compatibility layout.
4. Configure the Makefile with `FSTAR_HOME ?= tools/FStar`, `FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe`, and `KRML_EXE`/`KRML_HOME` pointing at the local install. The build should fail with a clear message if `./setup.sh` has not been run.
5. Configure verification with the local `fstar.exe`, cache directories, includes for `src/spec` and `src/impl`, and separate `.fsti` then `.fst` verification.
6. Configure extraction with one `.krml` file per extracted module, bundle spec/proof modules away, expose only `TLS13.Connection` as the public C API, and link trusted external stubs only for crypto primitives, X.509/signature validation, randomness, raw I/O, runtime support, and the narrowed connection backend.
7. Add C build rules linking extracted C with the HACL* `dist/gcc-compatible` C snapshot, OpenSSL, and trusted C stubs.
8. Add snapshot generation for extracted C headers/source.
9. Add test targets for pure spec tests, RFC 8448 vector tests, extracted C vector tests, extracted parser/serializer/framing tests, controlled OpenSSL TLS echo interop tests, and later HTTPS interop tests.

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

5. Scoped parser/serializer integration
   - Write extraction-safe `TLS13.Record.Framing.fsti` and `TLS13.Handshake.Framing.fsti` contracts for supported messages and extensions.
   - Implement scoped parser/serializer/framing code in extraction-ready Pulse/F* tied to `TLS13.Wire.Spec`; the original trusted-C-stub approach is no longer the default build path.
   - Add extracted C/vector tests for round-trip behavior, RFC 8448 inputs, and malformed-input rejection.
   - Defer broader parser-generator work to a later phase; do not plan on LowParse for this project.

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
10. Specify connection correctness through layered ghost logs: raw byte streams, TLS record/message stream views with residual prefixes, host state-machine traces, and application projections. The public API should expose application-level deltas while the internal invariant maintains the lower-level correspondences. The current `is_connection` already carries raw-derived record prefix parsing, raw stream residual shape, and application projection; the remaining proof work is the semantic AEAD/TLSInnerPlaintext/handshake parsing relation above the parsed record layer.
11. Avoid broad error fallbacks. Every error result should correspond to a specified state-machine failure transition.
12. Treat HACL*, OpenSSL, randomness, clock, trust store, and socket I/O as trusted boundaries with precise `.fsti` contracts. Parser/serializer logic should be extracted verified code, not a trusted C-stub boundary.
13. Before introducing a custom data structure, helper library, or lemma family, check the existing Pulse and F* libraries and reuse their arrays, buffers, references, lists, sequences, machine integers, options/results, and proof lemmas when they fit.

## Main risks

1. Real HTTPS interop is substantially more work than the controlled OpenSSL TLS echo test because public endpoints require a non-trivial extension, WebPKI certificate, signature, ALPN, fragmentation, and I/O surface; keep it out of the first end-to-end gate.
2. The default scoped parser/serializer path is now extracted Pulse/F* code rather than trusted C, but its proof value depends on caller-usable `.fsti` postconditions and vector breadth. Tests reduce interop risk; the next proof task is exposing enough `TLS13.Wire.Spec` facts for downstream modules without reopening implementation internals.
3. OpenSSL X.509 verification is a trusted boundary; the proof can only show correct use of the validated identity, not correctness of OpenSSL itself.
4. HACL* FFI specs must match the checked-in C snapshot preconditions exactly, including buffer sizes, disjointness, aliasing, and failure behavior, without assuming HACL* is reverified in this repository.
5. Transcript/key-schedule byte exactness is fragile; RFC 8448 vector validation should precede network testing.
6. Partial network I/O must be modeled in the state machine from the start.
7. Downloading the latest F* release improves freshness but can reduce reproducibility; once a baseline verifies, pin a known-good release through a `setup.sh --version` path.
8. Large modules and globally visible proof helpers can make verification slow or flaky; enforce small modules, `.fsti` boundaries, low rlimits, and early SMT profiling from the beginning.
9. The GitHub MCP semantic-search requirement is not currently satisfiable in this CLI environment because no MCP semantic-search tool is exposed.

## Current trusted boundary audit

The default `make test-openssl-echo` client path now uses a concrete extracted connection wrapper type, extracted handshake wrapper state transitions, extracted handshake driver control flow, extracted encrypted-handshake byte-driver scheduling, extracted flight-state storage/parsing helpers, extracted transcript hash routing and Finished comparison, extracted key schedule, extracted record seal/open, extracted TLSInnerPlaintext encode/decode, extracted record header construction/parsing, extracted ClientHello serialization, extracted ServerHello parsing/key-share extraction, extracted handshake header parsing, extracted Certificate parsing, and extracted CertificateVerify input/body parsing. Runtime extracted APIs expose C-shaped buffers and lengths; any `TLS13.Bytes.bytes`/`Seq.seq` values in implementation interfaces are erased ghost snapshots or pure spec facts, not C data.

The old core protocol external layers have been removed from the source tree and build: `TLS13.Connection.External.fsti`, `TLS13.Handshake.External.fsti`, `TLS13.Handshake.ByteDriver.External.fsti`, `TLS13.Handshake.Transcript.External.fsti`, their C ABI headers/stubs, and the stale handshake binding test are deleted. The remaining trusted code in the default wrapper interop path is:

1. `TLS13.Connection.Backend.fsti`, `tls13_connection_backend.h`, and `tls13_connection_backend_openssl.c`
   - Trusted only for backend handle/config lifetime, TCP connect, raw short read/write, OpenSSL-backed leaf-certificate validation, OpenSSL-backed CertificateVerify signature verification, and close/free.
   - Owns the TLS-facing raw byte ghost log. Its read/write postconditions expose exact raw append facts to the verified handshake and connection code; the C implementation remains trusted to implement those effects.
   - The backend header intentionally contains only backend ABI declarations; generated extraction units include the crypto primitive header separately.
   - The backend config is a non-erased runtime value, so extracted C receives the port and CA path explicitly instead of relying on erased ghost parameters.
   - The backend stores host, port, CA path, fd, and validated peer identity for later signature verification. It does not own TLS protocol state, handshake scheduling, transcript buffers, key schedule, record sequence numbers, record protection, alert policy, application-data buffering, exact-read/exact-write loops, or any TLS parser/serializer.
2. `tls13_hacl_stubs.c` plus the HACL* C snapshot
   - Trusted for SHA-256, HMAC, HKDF, X25519, randomness, and ChaCha20-Poly1305 primitives. Extracted wrappers orchestrate key schedule, nonce construction, and record state, but cryptographic algorithms remain HACL* C.
3. `tls13_crypto_external.c`
   - Trusted ABI glue from extracted key-schedule/record modules to the HACL* C wrappers.
4. `tls13_openssl_stubs.c` plus OpenSSL
   - Trusted X.509 chain/hostname/IP-SAN validation and signature verification over the validated leaf public key.
5. `tls13_io_stubs.c`
   - Trusted TCP connect/read/write/close wrapper.
6. `tls13_pulse_shims.c`, KaRaMeL/Pulse runtime support, and allocation
   - Trusted extraction/runtime support for helper operations not implemented in verified TLS code.
7. Test harnesses
   - `test/openssl_echo_server.c`, generated test certificates, and the shell harness are test infrastructure, not verified code.

The next highest-value implementation step is not more C rewiring; it is hardening and proof-surface work around the extracted path: adversarial encrypted-handshake/record vectors, unsupported-feature failure vectors, a stronger raw/TLS relation inside `TLS13.ConnectionLog`, possible relocation of the raw-log token from `TLS13.Connection.Backend` to `TLS13.IO` if we want the opaque channel itself to own the log, and a final TCB audit that documents exactly the crypto/X.509/raw-I/O/runtime assumptions above.

## Todos

1. [done] Use the pinned initial scope decisions: client-only, X25519, `TLS_CHACHA20_POLY1305_SHA256`, supported signature schemes, HRR abort behavior, controlled OpenSSL echo parameters, later public HTTPS endpoint, and a scoped parser/serializer boundary for v1 that has since moved from trusted C stubs to extracted Pulse/F* framing/parsing tied to `TLS13.Wire.Spec`.
2. [done] Add dependency helpers and local caches: HACL* submodule, RFC 8446/RFC 8448 fetch script, OpenSSL availability check, and gitignore rules for downloaded/generated artifacts.
3. [done] Create the repository skeleton, `setup.sh`, Makefile, cache/extraction directories, and minimal verify/extract smoke modules using `tools/FStar`.
4. [done] Implement the pure TLS byte/types/state-machine specification modules. Initial abstract byte, TLS type, crypto spec, X.509 spec, transcript, key, record, handshake, wire, state-machine, connection-log vocabulary, and state-machine lemma modules verify with the repository-local F* toolchain, including a controlled-handshake path lemma that reaches application data for the scoped supported server hello.
5. [done] Define pure crypto and X.509 spec interfaces, including trusted-boundary documentation. Crypto is intentionally abstract/uninterpreted and tied to trusted FFI contracts rather than HACL* proof imports.
6. [in progress] Add Pulse `.fsti` contracts and C stubs for HACL*, OpenSSL, randomness, clock, and I/O, plus extracted parser/serializer/framing contracts for scoped TLS bytes. HACL* C snapshot wrappers for SHA-256, HMAC-SHA256, HKDF-SHA256/TLS HKDF labels, X25519, TLS record nonce construction, ChaCha20-Poly1305, contiguous TLS ciphertext+tag AEAD wrappers, and random bytes have C tests; OpenSSL X.509 validation has generated localhost certificates, DNS/IP-SAN validation tests through the OpenSSL echo path, PEM-chain and DER-leaf validation tests, and RSA-PSS-RSAE-SHA256 signature verification tests over the validated leaf key; POSIX fd read/write and localhost TCP connect/close wrappers have tests. The old trusted C wire stubs and the old core protocol external interfaces are no longer in the default path. Remaining work is broader negative vectors, final contract audit, and documenting or removing any unused clock/time surface.
7. [in progress] Implement verified extracted parser/serializer support for the scoped TLS messages and extensions, with `.fsti` contracts and vector tests. Initial TLS record-header, handshake-header, TLSInnerPlaintext encode/decode, scoped ClientHello serialization, scoped supported ServerHello parsing for TLS 1.3/X25519/`TLS_CHACHA20_POLY1305_SHA256`, Certificate leaf-DER extraction, CertificateVerify parsing support, and RFC 8446 server CertificateVerify input construction plus Pulse framing contracts and malformed-input tests are present. `TLS13.Wire.Spec.fsti` is no longer an uninterpreted wire boundary: it now has a concrete total F* implementation for the scoped handshake/record parse and serialize model, so the Pulse framing contracts refer to executable spec definitions instead of abstract functions. The wrapper path now uses extracted `TLS13.Handshake.Framing` for scoped ClientHello serialization, scoped ServerHello parsing/key-share extraction, Certificate leaf-DER offset parsing, CertificateVerify body parsing, and CertificateVerify input construction. The old trusted C wire stubs and their standalone tests have been deleted, and the legacy `TLS13.Parse.fsti`/`TLS13.Serialize.fsti` implementation interfaces have been deleted because they exposed spec-level return values in `src/impl`.
8. [in progress] Implement and verify transcript hash and TLS 1.3 key schedule; validate with RFC 8448 vectors. The pure key-schedule spec now includes fixed TLS 1.3 labels, early/handshake/master secret derivation, handshake/application traffic secrets, Finished-key/verify-data computation, exporter/resumption master secrets, and traffic key/IV derivation; `TLS13.KeySchedule.fsti` exposes Pulse-facing contracts for the named derivation steps; HACL wrapper tests include RFC 8448 simple 1-RTT handshake-secret extraction, client handshake traffic-secret HKDF-Expand-Label, transcript-hash, Finished-key, and server Finished verify-data vectors. `TLS13.KeySchedule.fst` now provides a verified Pulse implementation of the key-schedule wrapper layer: it constructs the exact TLS 1.3 labels with byte literals, uses stack-local Pulse arrays for temporaries, sequences the trusted crypto primitives, and proves each exported function writes the corresponding pure `TLS13.Keys` result. `TLS13.Handshake.Transcript.fst` now provides verified Pulse transcript concatenation for ClientHello || ServerHello and ClientHello || ServerHello || server-handshake bytes, calls the existing `TLS13.Crypto.sha256` ABI on the constructed buffer, and implements extracted 32-byte Finished comparison. The implementations still rely on trusted primitive boundaries for SHA-256/HKDF/HMAC/AEAD, but no longer have a separate transcript-hash C shim.
9. [done] Implement and verify the scoped no-padding ChaCha20-Poly1305 record protection/framing path for controlled echo interop. `TLS13.Record.fst` implements the Pulse-facing record-state wrapper with concrete vector-backed key/IV storage, boxed sequence/install state, verified key installation, application-data seal, and application-data open operations tied to `TLS13.Record.Spec`; the record epoch remains ghost/spec-only because it has no runtime role in AEAD protection. `TLS13.Record.Framing.fst` verifies and extracts no-padding TLSInnerPlaintext encoding for application-data writes, no-padding content-type/payload-length decoding for application-data reads, TLS 1.3 application-data record-header construction for writes, and record-header parsing for reads; the extracted-wrapper OpenSSL interop path uses these around extracted `TLS13.Record` seal/open. `extract-record-c` and `extract-record-framing-c` translate the verified code to C against the trusted crypto ABI and small Pulse shims, and binding/OpenSSL tests check uninstalled-state rejection, application-data seal/open, tamper rejection, padded application records, and multi-record echo. Additional padding edge cases, malformed records, and broader RFC record vectors remain under the verified wire-code and connection-I/O milestones.
10. [done] Implement and verify the scoped client handshake for the controlled OpenSSL echo profile. The pure handshake spec models RFC 8446 server CertificateVerify input with the 64-space prefix, context string, separator, and transcript hash, and exposes Finished verification against the key-schedule verify-data function. `TLS13.Handshake.fst` carries a monotonic `TLS13.State.state_ref`, calls the narrowed backend ABI, and proves each per-flight operation advances the state token to the corresponding success phase or to `Failed` on error. The extracted handshake layer builds the scoped ClientHello, stores it into extracted flight state for transcript use, connects through the backend, exact-writes the ClientHello record, exact-reads the initial ServerHello record, parses the ServerHello/key share, invokes the extracted encrypted-flight byte driver directly, validates the leaf certificate through the backend, verifies CertificateVerify through the backend using the validated peer, verifies server Finished, and exact-writes the generated client Finished record. `TLS13.Handshake.FlightState` owns the runtime server-flight cursor/checkpoint/saw-flag state plus Certificate leaf, CertificateVerify signature metadata, Finished data, and handshake/application traffic material. `TLS13.Handshake.Driver` verifies the non-ghost control-flow spine to either `ApplicationData` or `Failed`. Remaining work is hardening, not initial implementation: fragmented/wrong-order encrypted-handshake vectors, unsupported-feature failure vectors, and stronger exported postconditions.
11. [done] Implement and verify top-level connection read/write/close APIs for the controlled profile. `TLS13.Connection.fst` implements the top-level Pulse connection wrapper with a concrete extracted runtime `connection` struct around the backend handle: allocation creates the backend handle, lifecycle marker, extracted-owned application traffic key/IV buffers, extracted-owned application record-state objects, pending-read plaintext buffer, and monotonic state token; connect proves the controlled handshake transition to `ApplicationData` or `Failed`, derives application keys from extracted flight state, installs those keys into extracted buffers and record states, and preserves backend lifetime for application I/O. `TLS13.Connection` owns multi-record write chunking, per-record write framing/seal construction, bounded read scheduling, exact-byte loops over short raw transport reads/writes, raw record-header parsing, application record open, padded TLSInnerPlaintext decode, payload copy, pending plaintext buffering for oversized records, post-handshake handshake-record skipping, receive-side close_notify handling, receive-side peer-alert routing, and close_notify seal/write. `TLS13.Connection.Driver.connect_write_read_exact` verifies the end-to-end connect/write/read control-flow spine. Remaining connection work is adversarial malformed input coverage, peer close_notify interop assertions where observable, unsupported-feature failure coverage, and stronger functional postconditions.
12. [done] Configure extraction and C linking for the current scoped client with HACL* and OpenSSL. `extract-key-schedule-c`, `extract-record-c`, `extract-record-framing-c`, `extract-handshake-framing-c`, `extract-handshake-flight-state-c`, `extract-handshake-transcript-c`, `extract-handshake-byte-driver-c`, `extract-handshake-c`, `extract-handshake-driver-c`, `extract-handshake-layered-c`, `extract-connection-c`, and `extract-connection-driver-c` translate verified Pulse/F* modules to C against explicit trusted ABIs. The connection extraction target now uses a combined bundle so generated C contains the full public connection API and all dependent extracted modules. Binding tests link generated C against mock or HACL-backed implementations. The OpenSSL echo smoke has a single client route: `test/test_extracted_connection_wrapper_openssl` runs the extracted connection/handshake/byte-driver/flight-state/transcript/key-schedule/record/framing stack against `TLS13.Connection.Backend` implemented by `tls13_connection_backend_openssl.c`, and checks repeated successful echo cases on one connection for 1-byte, small split-read, record-boundary, record-plus-one, and large multi-record payloads plus wrong-CA rejection. Final warning cleanup remains tracked separately.
13. [in progress] Add RFC 8448 and extracted C vector tests. Initial RFC 8448 key-schedule vectors are covered through the HACL C wrapper test, and `test-key-schedule-bindings` now checks extracted key-schedule C for the RFC 8448 handshake secret and client handshake traffic secret plus traffic key/IV derivation against direct HACL* wrappers; full extracted TLS vector tests remain pending.
14. [done] Add the controlled OpenSSL TLS echo interop test as the first end-to-end networking target. A local OpenSSL TLS 1.3 echo server and `openssl s_client` smoke script exist for the pinned X25519/`TLS_CHACHA20_POLY1305_SHA256` server side, covering short, record-boundary, record-plus-one, and multi-record-sized payloads plus split application reads; the single extracted-wrapper interop client routes through extracted `TLS13.Connection`, extracted handshake driver, extracted `TLS13.KeySchedule`, extracted `TLS13.Record`, extracted record/handshake framing, extracted transcript routing, and extracted handshake flight-state before reaching the remaining backend/crypto/X.509/raw-I/O operations. It checks repeated successful echo on one connection, sends close_notify, and verifies rejection under a wrong generated CA.
15. [pending] Add public HTTPS interop tests only after the controlled echo test is stable.
16. [pending] Audit specs, interfaces, file sizes, proof stability, trusted boundaries, rlimits, and extraction output before declaring the implementation complete.
17. [in progress] Harden the extracted handshake byte driver. The current extracted slices are in the default interop path and own ClientHello construction, ClientHello flight-state storage, backend connect sequencing, ClientHello exact raw-write loops, direct extracted invocation of encrypted-flight byte-driver orchestration, complete-message polling/type checks, bounded encrypted-record scheduling, initial ServerHello and encrypted-handshake exact-byte raw-read loops, client-Finished exact raw-write loops, TLS record-header parsing, scoped supported-ServerHello body parsing/key-share extraction, ServerHello transcript hashing and handshake/application traffic-key derivation, ChangeCipherSpec compatibility handling, expected message order, EncryptedExtensions acceptance, Certificate body parsing/leaf metadata extraction, CertificateVerify body parsing/signature metadata extraction, Finished body parsing/verify_data storage, server Finished transcript/MAC verification, client Finished verify_data/framing/record construction, handshake failure routing for the scoped server flight, ClientHello/ServerHello transcript buffers, encrypted server-handshake message storage and append, server-handshake record state/open, encrypted-handshake TLSInnerPlaintext decode, server-flight cursor/checkpoint state, Certificate/CertificateVerify/Finished metadata, CertificateVerify verification-success state, and long-lived handshake traffic material. Remaining work is fragmented/wrong-order encrypted-handshake vectors, unsupported-feature failure vectors, malformed server-flight boundary coverage, and stronger caller-visible specs.
18. [done] Implement extracted record framing around `TLS13.Record`, including TLS record header/AAD construction, TLSInnerPlaintext encode/decode, sequence-aware seal/open through extracted record state, close_notify send framing, and application-data buffering. Remaining record work is hardening/vector breadth, not initial implementation.
19. [in progress] Replace trusted C parser/serializer stubs with verified extraction-ready Pulse/F* parsers/serializers for the scoped TLS 1.3 message set, tied to `TLS13.Wire.Spec`. Trusted C wire stubs are no longer built, and the legacy extraction-unsafe `TLS13.Parse.fsti`/`TLS13.Serialize.fsti` declaration-only implementation interfaces have been removed from `src/impl`; remaining work is stronger extracted parser/serializer specs and broader vectors.
20. [in progress] Harden extracted connection I/O loops for partial reads/writes, multi-record app data, close_notify, encrypted alerts, and handshake records observed during application reads, leaving only raw socket read/write/close as trusted transport operations. Current slices: extracted `TLS13.Connection` owns application write chunking, application write record construction/seal, bounded read scheduling, application record-state ownership, application record-key installation, exact-byte loops over short raw reads/writes, read record-header parsing, application record open, padded TLSInnerPlaintext decode, payload copy, pending plaintext buffering for oversized application records, post-handshake handshake-record skipping, receive-side close_notify alert recognition/state advancement, receive-side peer-alert routing with mapped TLS alert descriptions, and send-side close_notify alert record construction/seal/write. Covered vectors: repeated app writes on one OpenSSL connection, 1-byte/small/record-boundary/record-plus-one/large payloads, multi-record reads, split reads from one record, padded application records, encrypted close_notify, and all currently mapped encrypted alert descriptions. Next vectors: malformed record lengths, empty-ish TLSInnerPlaintext edge cases, AEAD failures, unsupported-feature failures, and fragmented/wrong-order encrypted handshake records.
21. [done] Delete the legacy OpenSSL interop paths and obsolete core externals. `make test-openssl-echo` now builds/runs only the extracted-wrapper client; the direct C probe target, older extracted-driver target, shell harness branch, old core `External.fsti` files, old core external C headers, and stale handshake binding test have been removed. The backend C implementation has been renamed to `tls13_connection_backend_openssl.c` to reflect that it is a backend, not TLS protocol probe logic.
22. [in progress] Perform the final TCB/ABI audit for HACL*, OpenSSL, randomness, time, socket I/O, allocation, and Pulse support shims, with explicit documentation of what remains outside the verified TLS client. The core protocol external cleanup is complete; remaining audit work is to tighten contracts, add negative tests, document KaRaMeL/runtime assumptions, and decide whether any unused time/clock surface should be removed.
23. [pending] Audit all exported `.fsti` files using the functional-correctness checklist: every public operation should expose a caller-usable postcondition tied to pure specs/state-machine transitions, and any abstract predicate that hides key facts should be refined or accompanied by exported lemmas.
24. [pending] Stabilize extraction/build warnings before declaring completion. Current KaRaMeL output includes non-constant stack allocation warnings for some extracted handshake helpers and a generated C parentheses warning in `TLS13_Connection.c`; either eliminate them or document why they are acceptable for the supported C toolchain.
25. [done] Introduce the layered ghost-log specification as the main connection invariant. `TLS13.ConnectionLog` defines the layered ghost vocabulary, `TLS13.State` owns a monotonic erased connection-log token, `TLS13.Connection` carries that token in its predicate, and `TLS13.Connection.fsti` exposes application-level log deltas for connect/write/read/close without adding runtime spec-level data. The predicate now requires both raw-stream residual shape (`connection_view_raw_stream_shaped`) and application projection from the host trace (`connection_view_app_projected`).
26. [done] Push the layered log model down to the TLS-facing trusted transport boundary. `TLS13.Connection.Backend.fsti` now owns a `CL.raw_io_log`; raw reads/writes append exact raw bytes to sent/received ghost logs; connect, validation, signature verification, and close preserve the log; and `TLS13.Handshake`, `TLS13.Handshake.ByteDriver`, `TLS13.Handshake.Driver`, `TLS13.Connection`, and `TLS13.Connection.Driver` connect those raw logs to the top-level application projection. The main top-level predicate is explicitly raw-founded as `TLS13.Connection.is_connection c st s lg raw app`, tying the backend raw log to the current layered `ConnectionLog` view before projecting to `app`. `TLS13.IO.fsti` remains an opaque lower POSIX channel token below this backend boundary.
27. [in progress] Refine `TLS13.ConnectionLog` from the current staged raw-stream-shaped relation to the final prefix relation over record parsing, AEAD seal/open, TLSInnerPlaintext decoding, handshake reassembly, alerts, application data, and residual incomplete prefixes. The monotonic byte-extension primitive is now strengthened: `bytes_extends old next` requires `old` to be the exact prefix slice of `next`, with verified reflexive, append, transitive, raw-sent-append, and raw-received-append lemmas. The top-level invariant now also proves that sent/received TLS record views are computed by `TLS13.Wire.Spec.parse_record` over the raw sent/received logs, that those parser views have consumed/residual prefix shape, and that the serialized parsed-record prefix is exactly the consumed raw prefix; the staged sent/received TLS message views still have raw-byte suffix shape; and the exposed app log is the host-trace application projection. Remaining work is the semantic record-to-message view: AEAD seal/open correspondence, TLSInnerPlaintext decoding, fragmented handshake reassembly, alert/application projection, and failure-event facts.
28. [pending] Decide whether to move the raw byte ghost log one layer lower, from `TLS13.Connection.Backend` into `TLS13.IO`, so the abstract channel itself owns the lowest-level log. This is a proof-boundary cleanup; the verified TLS protocol code already sees exact raw append facts through the backend contract.
