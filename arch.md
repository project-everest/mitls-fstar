# TLS 1.3 client architecture

**Last updated:** 2025-05-26 (Clean Makefile with F* dependency analysis)

## Build Infrastructure

The project uses a clean Makefile structure following F* community best practices:
- **Dependency analysis**: `make .depend` generates full module dependency graph via `fstar.exe --dep full`
- **Incremental builds**: Only changed modules and their dependents are re-verified
- **Generic rules**: Single rules for `.checked`, `.krml`, and `.c` files driven by the dependency graph
- **Parallel builds**: Can use `make -j` for faster verification/extraction

Key targets:
- `make verify` - Verify all F*/Pulse modules
- `make extract-connection` - Extract full TLS connection bundle to C
- `make test` - Run all unit tests
- `make test-openssl-echo` - OpenSSL echo interop test

## Architecture Overview

This document describes the current architecture of the scoped TLS 1.3 client after the core-protocol external cleanup. The controlled interop path is a client-only TLS 1.3 profile: X25519, `TLS_CHACHA20_POLY1305_SHA256`, no PSK, no 0-RTT, no client authentication, no resumption, and no key update.

Legend:

- Blue: pure F* specification/proof modules. These are verified and erased from the C runtime.
- Yellow: logical specification assumptions. These are not runtime code, but they are part of the verification TCB.
- Green: Pulse/F* implementation modules verified by F* and extracted to C for the default client path.
- Red: unverified trusted boundary code or trusted declaration-only implementation interfaces.
- Gray: generated/runtime/test infrastructure.

## Runtime/module dependency diagram

Solid arrows are runtime calls or ownership dependencies in the extracted client path. Dashed arrows are proof/specification relationships.

![TLS 1.3 client architecture and unverified boundaries](arch.svg)

The editable source for this diagram is `arch.dot`. Regenerate the preview image with:

```sh
dot -Tsvg arch.dot -o arch.svg
```

## End-to-end ownership path

1. `TLS13.Connection` is the public extracted client API. It owns connection allocation/free, connect, application write/read/exact-read, pending plaintext buffering, alert/close_notify handling, close_notify send, and top-level state transitions.
2. `TLS13.Handshake.Driver` and `TLS13.Handshake` own the handshake control flow: ClientHello send, ServerHello receive, encrypted server flight, certificate validation callout, CertificateVerify signature callout, Finished verification, client Finished, and transition to application data.
3. `TLS13.Handshake.ByteDriver` owns encrypted server-flight scheduling and raw exact-read loops over the backend. It checks the scoped message order and routes encrypted records into `TLS13.Handshake.FlightState`.
4. `TLS13.Handshake.FlightState` owns runtime handshake buffers and derived material: ClientHello, ServerHello, server encrypted-handshake bytes, certificate leaf metadata, CertificateVerify metadata, Finished data, handshake/application traffic secrets, and record states.
5. `TLS13.KeySchedule`, `TLS13.Record`, `TLS13.Record.Framing`, `TLS13.Handshake.Framing`, and `TLS13.Handshake.Transcript` own TLS-owned cryptographic orchestration, record framing/protection, and scoped parser/serializer logic before crossing into the remaining trusted primitive/backend ABIs.

## Specification view: layered ghost logs

The top-level connection specification is being organized as a set of layered append-only ghost logs:

| Layer | Ghost state | Derived by | Exposed to callers |
| --- | --- | --- | --- |
| Raw network truth | `raw_sent`, `raw_received` byte streams owned by the trusted I/O/backend channel | `read`/`write` append the exact bytes exchanged with the OS | No, except through abstract connection predicates |
| TLS wire/message view | TLS records, decrypted TLSInnerPlaintext values, reassembled handshake messages, alerts, application-data messages, and residual incomplete prefixes | Pure prefix parsing/serialization with record parser/serializer soundness, record seal/open specs, TLSInnerPlaintext decode, and handshake-message reassembly | No, except through lemmas used by the connection spec |
| Host state-machine trace | `TLS13.StateMachine.event` list plus local validation/signature events | Projection from the TLS message view plus trusted X.509/signature callout results | Mostly hidden; postconditions expose phase, peer, failure, and app projection facts |
| Application projection | Application bytes sent/received, close/failure status, and validated peer identity after connect | Projection from the host trace | Yes; this is the public API contract |

The main internal invariant says that all four layers describe the same history. The runtime connection object and backend channel are related to the raw byte logs; the raw logs determine a TLS wire/message view up to a residual incomplete prefix; that view and local validation events determine the state-machine trace; and the public API exposes only the application projection of that trace.

Current wiring status: `TLS13.ConnectionLog` defines the layered pure vocabulary, `TLS13.State` owns an erased monotonic connection-log token, and `TLS13.Connection` carries that token in its public predicate. The main connection predicate is now explicitly raw-founded as `is_connection c st s lg raw app`: the backend/handshake context owns `raw`, the current layered log view has `view.raw_log == raw`, the sent/received TLS stream residuals are suffixes of `raw.raw_sent`/`raw.raw_received`, the sent/received TLS record views are computed by a prefix parser over those raw streams using `TLS13.Wire.Spec.parse_record`, each accepted parsed record serializes back to the exact consumed raw prefix, and the public application log is the application-data projection of the internal host trace. The connection API exposes application-log deltas for successful application writes/reads and preserves the application projection across failure/close paths, while ghost-only raw-log extension facts maintain monotonicity internally. The TLS-facing raw byte log is now owned by `TLS13.Connection.Backend.fsti`: raw writes append exact sent slices, raw reads append exact received slices, and handshake/connection code threads those raw logs into the layered connection view. `TLS13.IO.fsti` remains an opaque lower POSIX-channel token below the backend. The remaining proof refinement is the semantic record-to-message relation: AEAD seal/open, TLSInnerPlaintext decoding, and handshake reassembly are still staged rather than the final end-to-end semantic view.

Two details are essential for TLS 1.3:

1. The raw-to-message relation is prefix-based. A TCP stream can end in the middle of a record, and decrypted handshake messages can be fragmented or coalesced across records, so the invariant carries residual bytes rather than requiring a total parse of the whole stream after every read.
2. Encrypted records are not directly "serialized messages". Sent records are related to messages by TLSInnerPlaintext encoding, AAD construction, sequence-numbered AEAD sealing, and record serialization. Received records are related by record parsing, sequence-numbered AEAD opening, TLSInnerPlaintext decoding, and handshake reassembly.

## Module inventory

| Area | Module/file | Status | Role and main relationships |
| --- | --- | --- | --- |
| Spec | `TLS13.Bytes` | Verified pure F* | Ghost/spec byte model (`Seq.seq byte`); not used as runtime C data. |
| Spec | `TLS13.Types` | Verified pure F* | TLS enums/constants over `TLS13.Bytes`. |
| Spec assumption | `TLS13.Crypto.Spec.fsti` | Logical TCB | Abstract crypto functions used in specs and Pulse postconditions. Runtime implementation is HACL* C through trusted ABIs. |
| Spec assumption | `TLS13.X509.Spec.fsti` | Logical TCB | Abstract X.509 validation and peer signature model. Runtime validation is OpenSSL through the backend. |
| Spec | `TLS13.Transcript` | Verified pure F* | Transcript model over `Crypto.Spec.sha256`. |
| Spec | `TLS13.Keys` | Verified pure F* | TLS 1.3 key schedule model over `Crypto.Spec`. |
| Spec | `TLS13.Record.Spec` | Verified pure F* | Record seal/open state-machine model over `Crypto.Spec`. |
| Spec | `TLS13.Handshake.Spec` | Verified pure F* | Scoped handshake model, CertificateVerify input/Finished relationships, peer validation facts. |
| Spec | `TLS13.Wire.Spec.fsti/.fst` | Verified pure F* | Executable scoped wire parse/serialize model for the supported message surface. |
| Spec | `TLS13.StateMachine` | Verified pure F* | Connection phase model tying handshake, record, transcript, and peer state together. |
| Spec | `TLS13.ConnectionLog` | Verified pure F* | Layered ghost-log vocabulary for raw network byte logs, parsed TLS record prefix views, TLS message stream views with residual prefixes, host traces, state-machine trace consistency, and application-log projections; wired into `TLS13.Connection` so the top-level invariant requires raw-record parsing shape, raw-stream shape, and app projection while exposing public app-log deltas. |
| Spec | `TLS13.StateMachine.Lemmas` | Verified pure F* | Proof lemmas over the state machine. |
| Impl support | `TLS13.MachineTypes.fsti` | Verified aliases | Machine integer aliases for extraction-shaped code. |
| Impl support | `TLS13.State` | Verified/extracted | Monotonic state token used by handshake and connection predicates, plus erased monotonic connection-log token used by the top-level connection invariant. |
| Impl support | `TLS13.Handshake.StateDriver`, `TLS13.Connection.StateDriver` | Verified/extracted | Small state-transition drivers used by proof/control-flow tests. |
| Trusted ABI | `TLS13.Crypto.fsti` | Runtime TCB | Pulse contract for random bytes, SHA-256, HMAC, HKDF, X25519, nonce construction, ChaCha20-Poly1305. Implemented by C glue/HACL*. |
| Impl | `TLS13.KeySchedule.fsti/.fst` | Verified/extracted | Builds exact TLS 1.3 HKDF labels and derives handshake/application traffic material through `TLS13.Crypto`. |
| Trusted ABI | `TLS13.X509.fsti` | Runtime TCB, not default path | Declared Pulse X.509/signature ABI matching `TLS13.X509.Spec`; the current interop path uses `TLS13.Connection.Backend` -> OpenSSL instead. |
| Impl | `TLS13.Record.fsti/.fst` | Verified/extracted | Runtime record-state wrapper, key installation, application seal/open through `TLS13.Crypto`, tied to `TLS13.Record.Spec`. |
| Impl | `TLS13.Record.Framing.fsti/.fst` | Verified/extracted | TLSInnerPlaintext encode/decode, application-data record-header build, record-header parse. |
| Trusted ABI | `TLS13.IO.fsti` | Runtime TCB | Abstract lower POSIX channel and raw connect/read/write/close contract. The current backend C uses `tls13_io_stubs.c` for fd operations; the TLS-facing verified stack receives raw-log facts through `TLS13.Connection.Backend.fsti`. |
| Trusted ABI | `TLS13.Connection.Backend.fsti` | Runtime TCB | The only connection backend boundary: allocation/free, connect, raw short read/write, certificate validation, CertificateVerify signature verification, close. Owns the TLS-facing raw byte ghost log and exposes exact raw sent/received append facts to the verified handshake/connection code. |
| Impl | `TLS13.Handshake.Framing.fsti/.fst` | Verified/extracted | Scoped ClientHello serialization, ServerHello parsing/key-share extraction, handshake header parsing, Certificate leaf offsets, CertificateVerify body/input construction. |
| Impl | `TLS13.Handshake.Transcript.fsti/.fst` | Verified/extracted | Transcript buffer concatenation, SHA-256 routing through `TLS13.Crypto`, and 32-byte Finished comparison. |
| Impl | `TLS13.Handshake.FlightState.fsti/.fst` | Verified/extracted | Runtime storage for handshake bytes, cert/CV/Finished metadata, traffic material, and handshake record states. |
| Impl | `TLS13.Handshake.ByteDriver.fst` | Verified/extracted | Encrypted server-flight byte driver using backend raw reads plus extracted record/framing/flight-state helpers. |
| Impl | `TLS13.Handshake.fsti/.fst` | Verified/extracted | Handshake orchestration and state transitions; calls backend only for raw transport plus certificate/signature checks. |
| Impl | `TLS13.Handshake.Driver.fst` | Verified/extracted | Non-ghost handshake control-flow spine. |
| Impl | `TLS13.Connection.fsti/.fst` | Verified/extracted | Public client API, application-data I/O logic, state/log invariant ownership, and caller-visible application-log deltas. |
| Impl | `TLS13.Connection.Driver.fst` | Verified/extracted | End-to-end connect/write/read-exact control-flow spine for extracted tests, preserving public app-log facts. |
| Test/smoke | `TLS13.Extract.Smoke.fst` | Verified/extracted test | Minimal extraction smoke module. |

## Precise unverified runtime boundaries

| Boundary | Files | Trusted for | Must not contain |
| --- | --- | --- | --- |
| Backend ABI and OpenSSL/TCP backend | `src/impl/TLS13.Connection.Backend.fsti`, `c_stubs/tls13_connection_backend.h`, `c_stubs/tls13_connection_backend_openssl.c` | Backend handle/config lifetime; hostname, port, CA path, fd, and validated peer lifetime; TCP connect; raw short read/write; exact raw-log append facts for bytes read/written; leaf certificate validation; CertificateVerify signature verification; close/free. | TLS record parsing, handshake parsing, message scheduling, key schedule, transcript logic, AEAD seal/open, alert policy, application buffering, exact-read/exact-write protocol loops. |
| Raw socket I/O | `src/impl/TLS13.IO.fsti`, `c_stubs/tls13_io_stubs.c/.h` | OS TCP connect/read/write/close behavior and fd error mapping. | TLS protocol logic or cryptographic logic. |
| HACL*/crypto primitives | `src/impl/TLS13.Crypto.fsti`, `c_stubs/tls13_crypto_external.c/.h`, `c_stubs/tls13_hacl_stubs.c/.h`, `third_party/hacl-star/dist/gcc-compatible/*` | SHA-256, HMAC, HKDF, X25519, randomness, TLS nonce construction, ChaCha20-Poly1305, and ABI glue from extracted code to those primitives. | TLS transcript scheduling, transcript buffer concatenation, HKDF label selection, record sequence state, record header construction, or TLS parse/serialize decisions. |
| OpenSSL validation/signature | `c_stubs/tls13_openssl_stubs.c/.h`, OpenSSL library | X.509 chain validation, DNS/IP-SAN hostname matching, validated peer public-key lifetime, RSA-PSS-RSAE-SHA256 CertificateVerify verification. | TLS handshake scheduling, Certificate message parsing, CertificateVerify input construction. |
| Extraction/runtime support | `c_stubs/tls13_pulse_shims.c`, KaRaMeL/Pulse runtime, C allocator/libc/compiler | Runtime support for generated C and small helper operations not implemented in verified TLS code. | Protocol-specific behavior. |
| Standalone extraction/test shims | `c_stubs/tls13_record_for_flight_state.h`, `c_stubs/tls13_connection_driver_test_shim.h`, `c_stubs/tls13_handshake_driver_test_shim.h` | Macro/header adaptation for standalone generated binding tests. | Production protocol logic. |
| Test harness | `test/*`, `scripts/test-openssl-echo.sh`, generated certificates | Controlled local interop environment and assertions. | Verification claim for production correctness. |

## Logical assumptions in the proof

These are not C runtime components, but they are still part of the trusted reasoning base:

1. `TLS13.Crypto.Spec.fsti` abstracts cryptographic behavior. Proofs show extracted TLS code calls the right primitive contracts with the right bytes, not that SHA-256/HKDF/X25519/AEAD themselves are mathematically implemented by this repository.
2. `TLS13.X509.Spec.fsti` abstracts certificate validation and signature verification. The runtime behavior is delegated to OpenSSL through the backend boundary.
3. F*, Pulse, KaRaMeL, generated C compilation, the C memory allocator, and platform libraries are trusted infrastructure.

## What is no longer trusted core protocol logic

The old core protocol external layers have been removed from the source tree and build:

- `src/impl/TLS13.Connection.External.fsti`
- `src/impl/TLS13.Handshake.External.fsti`
- `src/impl/TLS13.Handshake.ByteDriver.External.fsti`
- `src/impl/TLS13.Parse.fsti`
- `src/impl/TLS13.Serialize.fsti`
- `src/impl/TLS13.Handshake.Transcript.External.fsti`
- `c_stubs/tls13_connection_external*.h`
- `c_stubs/tls13_handshake_external*.h`
- `c_stubs/tls13_handshake_byte_driver_external.h`
- `c_stubs/tls13_handshake_transcript_external.c/.h`
- `c_stubs/tls13_connection_probe.c`

The important invariant is that TLS-owned behavior stays in verified/extracted modules: supported-message parsing/serialization, handshake ordering, transcript selection, key-schedule orchestration, record sequence/nonce/AAD handling, AEAD call sequencing, alert policy, application-data buffering, and connection read/write/close state. The remaining red boundaries are primitive/backend/runtime assumptions only.
