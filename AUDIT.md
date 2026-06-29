# TLS 1.3 client audit guide

This repository contains a verified, extraction-oriented TLS 1.3 client core for
the supported client profile, plus endpoint-driven C glue for client/server
interop. The core proof boundary is the buffer/event API in `TLS13.Impl.Client`;
the public runtime path now routes through the shared `Common.ProtocolEndpoint`
and `Common.TCP` architecture, with small C wrappers preserving the runtime ABIs.

## Supported profile

The theorem and implementation target this profile:

- TLS 1.3 client mode;
- X25519 key exchange;
- `TLS_CHACHA20_POLY1305_SHA256`;
- no PSK, no 0-RTT, no client authentication;
- certificate validation and CertificateVerify through explicit external TCBs;
- application data, close_notify, NewSessionTicket ignore, and KeyUpdate response
  behavior as implemented.

This is not a proof of all TLS 1.3 modes. Unsupported modes should be treated as
outside the theorem statement, not as implicitly verified.

## Main verified API

The public proof/API boundary is:

- `src/impl/TLS13.Impl.Client.fsti`
- `src/impl/TLS13.Impl.Client.fst`
- `src/impl/TLS13.Impl.Client.Types.fst`

The exported constructors establish `CT.client_state_correct` and
`CT.client_end_to_end_invariant`. The exported step functions return compact
end-to-end predicates:

- `process_network_bytes` returns `CT.network_bytes_end_to_end_correct`;
- `process_local_event` returns `CT.local_event_end_to_end_correct`.

These predicates preserve the concrete ownership predicate
`TLS13.Impl.Client.connection_exactly`, the pure TLS connection-state model, and
the layered invariant connecting:

```text
raw network bytes
  -> TLS outer records
  -> decoded TLS messages / protected-record open facts
  -> transcript and traffic-secret evolution
  -> connection state-machine events
  -> application-log projection
```

The trace-level theorem surface is in `TLS13.Impl.Client.Types`, including
`CT.driver_trace_end_to_end`, `CT.lemma_driver_trace_end_to_end`, and
`CT.lemma_driver_trace_from_initial_end_to_end`.

## What the proof guarantees

For accepted network/local steps, the public postconditions prove that:

- concrete buffers are tied to legal TLS state-machine deltas;
- non-empty consumed network prefixes parse as one TLS outer record and have
  recursive raw-record segmentation facts;
- successful non-decode-error network input projects to decoded TLS messages and
  legal received events;
- protected received records expose record-layer open facts and read-key/IV
  provenance from the installed key schedule;
- emitted protected records expose seal facts and write-key/IV provenance;
- transcript, record epoch/sequence, traffic-key, pending app-buffer, KeyUpdate,
  and application-log projections are preserved;
- cumulative accepted raw sent/received events replay into the connection-state
  log;
- cumulative sent-seal replay and accepted received-decode replay are preserved;
- application output prefixes correspond to spec-level received application data,
  and local application sends correspond to spec-level sent application data.

Rejected consumed input is intentionally weaker: it is classified per network
step by `network_bytes_end_to_end_correct` witnesses. Rejected bytes are not yet
accumulated into the connection-state log. This is the deliberate
accepted-event-log design currently used by the trace theorem.

## Endpoint-driven runtime path

The migration path from handwritten C orchestration into a shared verified
endpoint architecture is:

- `common/Common.ProtocolImplementation.fst`
- `common/Common.ProtocolEndpoint.fst`
- `common/Common.ProtocolDriver.fst`
- `common/Common.TCP.fsti`
- `src/impl/TLS13.Impl.Client.Endpoint.fst`
- `src/impl/TLS13.Impl.Server.Endpoint.fst`

`Common.ProtocolImplementation` is the auditable refinement contract for
network/local handlers. `Common.ProtocolEndpoint` adds scheduling, concrete
frames, I/O resources, and first-order local/API events. `Common.ProtocolDriver`
is a fuel-bounded proof-generic loop over a `Common.TCP.channel`; extraction uses
monomorphic endpoint/runtime wrappers where that gives a simpler C ABI.

The implementation/runtime path owns extracted TLS state, typed OpenSSL auth or
credential contexts, connected `Common.TCP` channels, retained receive lengths,
and scratch buffers in endpoint-specific frames or thin C wrapper structs. It
routes:

- TCP connect/listen/accept/read/write/close through `Common.TCP`;
- network bytes through endpoint `pi_process_network` handlers;
- certificate validation, CertificateVerify verification/signing, server
  parameter selection, shared-secret derivation, application sends, and
  close_notify sends through ordinary local/API events;
- buffered-prefix network processing and suffix compaction before fresh reads;
- application-data receive copyout from Pulse-owned scratch storage.

The top-level workflows treat short writes as failures: a `StepOk` local or
network step only continues or reports success when the `Common.TCP.write` return
count equals the verified response `network_out_len`.

For certificate validation, the Pulse workflow copies the parsed leaf DER into
the OpenSSL input buffer, asks the typed OpenSSL TCB to produce the peer identity,
then splits the authentication payload buffer to the exact returned identity
prefix before calling `process_local_event LocalValidateCertificate`. The
verified local event therefore installs the exact validated bytes, not a padded
scratch-buffer value.

The retained-buffer read-append function is the important receive-buffer bridge.
`Common.TCP.read` writes into the free suffix of a caller-owned retained buffer,
while `process_network_bytes` requires a raw array whose logical length is
exactly the buffered bytes being processed. The Pulse driver uses
`Pulse.Lib.Array.sub` / `return_sub` to split the read suffix, rejoin the full
buffer, split the buffered prefix, call `process_network_bytes` on that exact
prefix, and restore ownership of the full retained buffer. The processed prefix
is carried as an erased proof field, so it does not change the generated C
layout.

The same split/restore pattern is also exposed for retained receive buffers by
`driver_process_buffered_network_bytes_once` and
`driver_process_buffered_network_bytes_compact_once`: the C runtime owns a
capacity-sized buffer and a buffered-byte count, while Pulse splits only the
buffered prefix, routes the protocol step and any response write through the
verified driver helper layer, and compacts the unconsumed suffix after successful
consumption.

`driver_read_buffered_network_bytes_compact_once` additionally splits the free
suffix of the retained buffer, calls `Common.TCP.read` on that suffix, rejoins the
full buffer, and then runs the same verified buffered-prefix processing and
compaction path. The concrete runtime now uses this entry point when it needs
more network input; the C code no longer performs a direct socket read into the
retained receive buffer.

Exact-buffer receive, standalone read-prefix receive, helper buffered-record
loops, auth copyout, local-action drains, and legacy driver records are private
implementation slices rather than caller APIs. The generated endpoint/canonical C
ABI uses prefixed names, while the stable public ABI remains in `runtime/`.

The endpoint-driven runtime API is tested by `make test-openssl-echo
test-openssl-sclient`.

## Concrete C runtime

The reusable concrete runtime API is:

- `runtime/tls13_client_driver.h`
- `runtime/tls13_client_driver.c`
- `runtime/tls13_server_driver.h`
- `runtime/tls13_server_driver.c`

These C drivers are thin ABI wrappers around the extracted endpoint/canonical
runtime path:

- `tls13_client_driver_connect` opens a `Common.TCP` channel and drives the
  endpoint handshake;
- `tls13_client_driver_send_application_data` and
  `tls13_client_driver_receive_application_data` route application traffic
  through endpoint/canonical handlers;
- `tls13_client_driver_close` sends close_notify and closes the channel;
- the server wrapper mirrors this structure around listen/accept and the server
  endpoint.

The C wrapper now stores only the extracted `client_driver` value, a connected
flag, and the last error string. It no longer exposes a separate handshake
entry point because the verified `connect` performs the TLS handshake. It also
no longer owns TLS scratch buffers, copies received plaintext, performs the
local-action drain, auth copyout/completion, retained-buffer read/process loop,
or close-notify wait loop itself.

## Trusted computing base

The active TCB surface is intentionally explicit.

| TCB component | Files | Role |
| --- | --- | --- |
| Crypto primitives and entropy | `src/impl/TLS13.Crypto.fsti`, `c_stubs/tls13_crypto_external.c`, `c_stubs/tls13_hacl_stubs.c`, HACL* sources | Trusted to match `TLS13.Crypto.Spec`, including AEAD, hashes, HKDF/HMAC, random bytes, and X25519. |
| X509/signature validation | `src/impl/TLS13.OpenSSL.fsti`, `c_stubs/tls13_openssl_karamel.*`, `c_stubs/tls13_openssl_stubs.c` | Typed OpenSSL auth TCB. The Pulse workflow calls this interface directly; successful returns are trusted to establish `CT.local_input_wf` for certificate validation over the exact returned peer-identity prefix and for CertificateVerify. |
| TCP bridge | `common/Common.TCP.fsti`, `c_stubs/common_tcp_stubs.c`, `c_stubs/common_tcp_karamel.*` | Trusted connect/listen/accept/read/write/close bridge with ghost-indexed received/sent byte histories. Endpoint predicates expose those histories and relate their contents to the protocol wire log: sent transport bytes equal the protocol raw-sent log, while received transport bytes split into consumed bytes plus retained read-ahead, with the protocol raw-received log content-accounted inside the consumed prefix. `Common_TCP.krml` is included in the bundle so KaRaMeL typechecks the exact TCP ABI; the C shim is deliberately small. Read-prefix handling, retained-buffer read-append, and retained-buffer prefix/compaction are verified in Pulse. |
| Extracted runtime infrastructure | F*, Pulse, KaRaMeL, generated C, C compiler/runtime | Trusted extraction/runtime substrate and C platform behavior. |
| Concrete C ABI wrapper | `runtime/tls13_client_driver.c` | Trusted allocation of the small wrapper object, status-to-error translation, and lifetime tracking around the extracted Pulse workflow. |

## What is implemented in C

The C code is kept to glue and TCB responsibilities:

- POSIX socket connect/listen/accept/read/write/close in `common_tcp_stubs.c`;
- the tiny extracted-TCP ABI shim in `common_tcp_karamel.c`;
- the typed OpenSSL ABI shim in `tls13_openssl_karamel.c`;
- crypto/X509 bridge code;
- the small client/server runtime ABI wrappers.

Protocol state transitions, key-schedule logic, record-layer logic, client step
theorems, parser/serializer facades, local-action drain,
auth copyout/completion boundaries, response writes, top-level
connect/send/receive/close workflows, OpenSSL auth orchestration, caller receive
copyout, and the driver
receive-prefix/buffered-prefix/read-append/compaction paths are in F*/Pulse and
extracted.

## What is not claimed yet

The current theorem does not yet claim:

- cumulative logging of rejected consumed bytes inside `connection_state`;
- full TLS 1.3 feature coverage beyond the supported profile;
- verified crypto/X509 implementations;
- liveness: the top-level Pulse workflows are fuel-bounded and may return
  exhaustion rather than proving global protocol progress;
- full lifecycle support for closing a freshly allocated but never-connected
  `client_driver`; today failed `connect` is terminal and frees driver-owned
  IO/auth/buffer resources, while successful `connect` must be followed by
  `close`;
- transport honesty beyond the trusted `Common.TCP` bridge contract;
- general multi-record local application-data send correctness beyond the current
  supported one-record send theorem.

## Audit entry points

Start with these files:

1. `src/impl/TLS13.Impl.Client.fsti` for the public API.
2. `src/impl/TLS13.Impl.Client.Types.fst` for the theorem predicates and trace
   theorem surface.
3. `src/spec/TLS13.Spec.ConnectionState.fst` for the core pure connection-state
   model, invariants, and legal deltas; proof-only support lives in
   `src/spec/TLS13.ConnectionState.Lemmas.fst`.
4. `src/spec/TLS13.ConnectionLog.fst` and `src/spec/TLS13.StateMachine.fst` for
   layered logs and the small client-only trace automaton used by log/projection
   proofs.
5. `common/Common.ProtocolImplementation.fst`,
   `common/Common.ProtocolEndpoint.fst`, `common/Common.ProtocolDriver.fst`, and
   `common/Common.TCP.fsti` for the shared endpoint/driver/TCP architecture.
6. `src/impl/TLS13.OpenSSL.fsti` and `c_stubs/tls13_openssl_karamel.*` for the
   typed OpenSSL TCB boundary called by the Pulse workflow.
7. `runtime/tls13_client_driver.c` and `runtime/tls13_server_driver.c` for the
   small C ABI wrappers around the extracted endpoint/canonical runtime path.
8. `src/impl/TLS13.Impl.Parser.*` and `src/impl/TLS13.Impl.Serializer.*` for
   the verified parser/serializer facades and their `TLS13.Wire.Spec`
   postconditions.
9. `c_stubs/common_tcp_karamel.*`, `c_stubs/common_tcp_stubs.*`,
   `c_stubs/tls13_crypto_external.*`, and `c_stubs/tls13_openssl_stubs.*` for
   the remaining C boundary.

## Validation commands

The main gates are:

```sh
make verify
make test
make test-openssl-echo
make check-admits
```

`make test-extracted-client-driver-slice` specifically checks extraction and C
linkage for the narrowed Pulse driver API.
