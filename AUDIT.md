# TLS 1.3 client audit guide

This repository contains a verified, extraction-oriented TLS 1.3 client core for
the supported client profile, plus C glue for interop. The core proof boundary is
the buffer/event API in `TLS13.Impl.Client`; the public runtime shape is now
implemented by extracted Pulse workflows in `TLS13.Impl.Client.Driver`, with a
small C wrapper preserving the `runtime/tls13_client_driver.h` ABI.

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

## Verified Pulse top-level driver

The migration path from handwritten C orchestration into verified Pulse is:

- `src/impl/TLS13.Impl.Client.Driver.fsti`
- `src/impl/TLS13.Impl.Client.Driver.fst`

The public `TLS13.Impl.Client.Driver.fsti` surface is intentionally narrow:
`client_driver`, its live/connected/closed predicates, `driver_workflow_status`,
`client_receive_result`, and exactly these Pulse entry points:
`new_client`, `connect`, `send`, `receive`, and `close`.

The implementation owns the extracted client, typed OpenSSL auth context,
connected channel slot, retained receive length, and all scratch buffers inside
`client_driver`. Its private helper layer still contains the lower-level
`driver`/`top_driver` workflow used to prove and extract:

- TCP connect through `TLS13.IO.connect_tcp`;
- typed client/auth construction in `new_client`;
- TCP connect plus TLS handshake in `connect`;
- control-state snapshots;
- certificate leaf DER, CertificateVerify input, and CertificateVerify signature
  copyout;
- externally validated local-event completion;
- one ready internal local action;
- bounded local-action drain;
- top-level fueled handshake and receive workflows that orchestrate internal
  local actions, network reads, retained-buffer processing, and typed OpenSSL
  auth calls in Pulse;
- buffered-prefix network processing and suffix compaction for full-capacity
  retained receive buffers;
- retained-buffer read-append into the free suffix followed by buffered-prefix
  processing and suffix compaction;
- application-data send through `send`;
- application-data receive through `receive`, including copyout to the caller
  buffer from Pulse-owned scratch storage;
- close_notify, optional peer close_notify wait, channel close, and auth-context
  free through `close`.

The top-level workflows treat short writes as failures: a `StepOk` local or
network step only continues or reports success when the `TLS13.IO.write` return
count equals the verified response `network_out_len`.

For certificate validation, the Pulse workflow copies the parsed leaf DER into
the OpenSSL input buffer, asks the typed OpenSSL TCB to produce the peer identity,
then splits the authentication payload buffer to the exact returned identity
prefix before calling `process_local_event LocalValidateCertificate`. The
verified local event therefore installs the exact validated bytes, not a padded
scratch-buffer value.

The retained-buffer read-append function is the important receive-buffer bridge.
`TLS13.IO.read` writes into the free suffix of a caller-owned retained buffer,
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
suffix of the retained buffer, calls `TLS13.IO.read` on that suffix, rejoins the
full buffer, and then runs the same verified buffered-prefix processing and
compaction path. The concrete runtime now uses this entry point when it needs
more network input; the C code no longer performs a direct socket read into the
retained receive buffer.

Exact-buffer receive, standalone read-prefix receive, helper buffered-record
loops, auth copyout, local-action drains, and the old `driver`/`top_driver`
records are private implementation slices rather than caller APIs. The generated
C ABI uses prefixed names such as `TLS13_Impl_Client_Driver_connect` to avoid
colliding with POSIX `connect`/`send`/`close`, but the F*/Pulse public API is the
five-operation workflow above.

The extracted narrow driver API is tested by `make test-extracted-client-driver-slice`.

## Concrete C runtime

The reusable concrete runtime API is:

- `runtime/tls13_client_driver.h`
- `runtime/tls13_client_driver.c`

This C driver is now a thin ABI wrapper around the verified top-level workflow:

- `tls13_client_driver_connect` calls `new_client` and `connect`;
- `tls13_client_driver_send_application_data` calls
  `send`;
- `tls13_client_driver_receive_application_data` calls
  `receive`;
- `tls13_client_driver_close` calls `close`.

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
| Parser/serializer C backend | `src/impl/TLS13.Impl.Parser.fsti`, `src/impl/TLS13.Impl.Serializer.fsti`, `c_stubs/tls13_connection_backend.h` | Interface-only parser/serializer contracts implemented by C macros/static helpers. Live hooks expose `TLS13.Wire.Spec` parse/serialize facts, but the C implementation is trusted. |
| Crypto primitives and entropy | `src/impl/TLS13.Crypto.fsti`, `c_stubs/tls13_crypto_external.c`, `c_stubs/tls13_hacl_stubs.c`, HACL* sources | Trusted to match `TLS13.Crypto.Spec`, including AEAD, hashes, HKDF/HMAC, random bytes, and X25519. |
| X509/signature validation | `src/impl/TLS13.OpenSSL.fsti`, `c_stubs/tls13_openssl_karamel.*`, `c_stubs/tls13_openssl_stubs.c` | Typed OpenSSL auth TCB. The Pulse workflow calls this interface directly; successful returns are trusted to establish `CT.local_input_wf` for certificate validation over the exact returned peer-identity prefix and for CertificateVerify. |
| TCP bridge | `src/impl/TLS13.IO.fsti`, `c_stubs/tls13_io_stubs.c`, `c_stubs/tls13_io_karamel.*` | Trusted connect/read/write/close bridge with ghost-indexed received/sent byte histories. The verified driver exposes those histories in `client_driver_connected` and relates their contents to `st.cs_wire_log`: sent transport bytes equal the protocol raw-sent log, while received transport bytes split into consumed bytes plus retained read-ahead, with the protocol raw-received log content-accounted inside the consumed prefix. `TLS13_IO.krml` is included in the driver bundle so KaRaMeL typechecks the exact IO ABI; the C shim is deliberately small. Read-prefix handling, retained-buffer read-append, and retained-buffer prefix/compaction are verified in Pulse. |
| Extracted runtime infrastructure | F*, Pulse, KaRaMeL, generated C, C compiler/runtime | Trusted extraction/runtime substrate and C platform behavior. |
| Concrete C ABI wrapper | `runtime/tls13_client_driver.c` | Trusted allocation of the small wrapper object, status-to-error translation, and lifetime tracking around the extracted Pulse workflow. |

## What is implemented in C

The C code is kept to glue and TCB responsibilities:

- POSIX socket connect/read/write/close in `tls13_io_stubs.c`;
- the tiny extracted-IO ABI shim in `tls13_io_karamel.c`;
- the typed OpenSSL ABI shim in `tls13_openssl_karamel.c`;
- parser/serializer backend shims in `tls13_connection_backend.h`;
- crypto/X509 bridge code;
- the small `tls13_client_driver.h` ABI wrapper.

Protocol state transitions, key-schedule logic, record-layer logic, client step
theorems, local-action drain, auth copyout/completion boundaries, response
writes, top-level connect/send/receive/close workflows, OpenSSL auth
orchestration, caller receive copyout, and the driver
receive-prefix/buffered-prefix/read-append/compaction paths are in F*/Pulse and
extracted.

## What is not claimed yet

The current theorem does not yet claim:

- cumulative logging of rejected consumed bytes inside `connection_state`;
- full TLS 1.3 feature coverage beyond the supported profile;
- verified parser/serializer C implementations;
- verified crypto/X509 implementations;
- liveness: the top-level Pulse workflows are fuel-bounded and may return
  exhaustion rather than proving global protocol progress;
- full lifecycle support for closing a freshly allocated but never-connected
  `client_driver`; today failed `connect` is terminal and frees driver-owned
  IO/auth/buffer resources, while successful `connect` must be followed by
  `close`;
- transport honesty beyond the trusted `TLS13.IO` bridge contract;
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
5. `src/impl/TLS13.Impl.Client.Driver.fsti` / `.fst` for the narrow top-level
   Pulse driver API, private workflow helpers, and receive-prefix bridge.
6. `src/impl/TLS13.OpenSSL.fsti` and `c_stubs/tls13_openssl_karamel.*` for the
   typed OpenSSL TCB boundary called by the Pulse workflow.
7. `runtime/tls13_client_driver.c` for the small C ABI wrapper around the
   extracted workflow.
8. `src/impl/TLS13.Impl.Parser.fsti`, `src/impl/TLS13.Impl.Serializer.fsti`,
   and `c_stubs/tls13_connection_backend.h` for the parser/serializer TCB.
9. `c_stubs/tls13_io_karamel.*`, `c_stubs/tls13_io_stubs.*`,
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
