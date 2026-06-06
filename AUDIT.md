# TLS 1.3 client audit guide

This repository contains a verified, extraction-oriented TLS 1.3 client core for
the supported client profile, plus C glue for interop. The current proof boundary
is the buffer/event API in `TLS13.Impl.Client`; the concrete socket runtime is
being migrated into verified Pulse through `TLS13.Impl.Client.Driver`.

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

## Verified Pulse driver facade

The migration path from handwritten C orchestration into verified Pulse is:

- `src/impl/TLS13.Impl.Client.Driver.fsti`
- `src/impl/TLS13.Impl.Client.Driver.fst`

The facade owns a `driver` record containing an extracted client and
`TLS13.IO.channel`. It currently verifies and extracts:

- TCP connect through `TLS13.IO.connect_tcp`;
- control-state snapshots;
- certificate leaf DER, CertificateVerify input, and CertificateVerify signature
  copyout;
- externally validated local-event completion;
- one ready internal local action;
- bounded local-action drain;
- exact-buffer network receive and application-receive aliases;
- buffered-prefix network processing and suffix compaction for full-capacity
  retained receive buffers;
- retained-buffer read-append into the free suffix followed by buffered-prefix
  processing and suffix compaction;
- read-prefix network receive via `TLS13.IO.read`;
- application-data send;
- close_notify send;
- channel close.

The read-prefix function is the important receive-buffer bridge. `TLS13.IO.read`
returns ownership of the full-capacity buffer, while `process_network_bytes`
requires a raw array whose logical length is exactly the bytes read. The Pulse
driver uses `Pulse.Lib.Array.sub` / `return_sub` to split the received prefix,
call `process_network_bytes` on that exact prefix, and restore the full buffer.
The processed prefix is carried as an erased proof field, so it does not change
the generated C layout.

The same split/restore pattern is also exposed for retained receive buffers by
`driver_process_buffered_network_bytes_once` and
`driver_process_buffered_network_bytes_compact_once`: the C runtime owns a
capacity-sized buffer and a buffered-byte count, while Pulse splits only the
buffered prefix, routes the protocol step and any response write through the
verified driver facade, and compacts the unconsumed suffix after successful
consumption.

`driver_read_buffered_network_bytes_compact_once` additionally splits the free
suffix of the retained buffer, calls `TLS13.IO.read` on that suffix, rejoins the
full buffer, and then runs the same verified buffered-prefix processing and
compaction path. The concrete runtime now uses this entry point when it needs
more network input; the C code no longer performs a direct socket read into the
retained receive buffer.

The extracted driver facade is tested by `make test-extracted-client-driver-slice`.

## Concrete C runtime

The reusable concrete runtime API is:

- `runtime/tls13_client_driver.h`
- `runtime/tls13_client_driver.c`

This C driver currently performs bounded top-level interop orchestration around
the verified driver facade:

- TCP connect through `driver_connect`;
- handshake/app/close polling around `driver_drain_local_actions`,
  retained-buffer read/process helpers, `driver_send_application_data`,
  `driver_send_close_notify`, and `driver_close`;
- OpenSSL certificate validation and CertificateVerify callbacks, with copyout
  and local-event completion through verified driver wrappers;
- the bounded top-level decision to read more input or process the retained
  buffer again.

This runtime is functional and covered by the OpenSSL echo interop test, but it
still contains trusted C polling/error handling and OpenSSL callback calls. The
main interop path no longer calls raw `Impl.Client` step functions directly;
protocol processing, retained-buffer suffix compaction, local-action drain, auth
copyout and completion, retained-buffer read-append, response writes, and close
all go through extracted Pulse driver entry points.

## Trusted computing base

The active TCB surface is intentionally explicit.

| TCB component | Files | Role |
| --- | --- | --- |
| Parser/serializer C backend | `src/impl/TLS13.Impl.Parser.fsti`, `src/impl/TLS13.Impl.Serializer.fsti`, `c_stubs/tls13_connection_backend.h` | Interface-only parser/serializer contracts implemented by C macros/static helpers. Live hooks expose `TLS13.Wire.Spec` parse/serialize facts, but the C implementation is trusted. |
| Crypto primitives and entropy | `src/impl/TLS13.Crypto.fsti`, `c_stubs/tls13_crypto_external.c`, `c_stubs/tls13_hacl_stubs.c`, HACL* sources | Trusted to match `TLS13.Crypto.Spec`, including AEAD, hashes, HKDF/HMAC, random bytes, and X25519. |
| X509/signature validation | `src/impl/TLS13.X509.fsti`, `c_stubs/tls13_openssl_stubs.c` | Trusted certificate-chain validation and CertificateVerify signature checks. The verified local-step preconditions state exactly what these callbacks must establish. |
| TCP bridge | `src/impl/TLS13.IO.fsti`, `c_stubs/tls13_io_stubs.c`, `c_stubs/tls13_io_karamel.*` | Trusted connect/read/write/close bridge. The KaRaMeL shim is deliberately small; read-prefix handling, retained-buffer read-append, and retained-buffer prefix/compaction are verified in Pulse. |
| Extracted runtime infrastructure | F*, Pulse, KaRaMeL, generated C, C compiler/runtime | Trusted extraction/runtime substrate and C platform behavior. |
| Concrete C driver loop | `runtime/tls13_client_driver.c` | Trusted bounded polling/error handling and OpenSSL callback invocation around verified driver entry points. |

## What is implemented in C

The C code is kept to glue and TCB responsibilities:

- POSIX socket connect/read/write/close in `tls13_io_stubs.c`;
- the tiny extracted-IO ABI shim in `tls13_io_karamel.c`;
- parser/serializer backend shims in `tls13_connection_backend.h`;
- crypto/X509 bridge code;
- the current concrete OpenSSL interop polling loop.

Protocol state transitions, key-schedule logic, record-layer logic, client
step theorems, local-action drain, auth copyout/completion boundaries, response
writes, and the new driver receive-prefix/buffered-prefix/read-append/compaction
paths are in F*/Pulse and extracted.

## What is not claimed yet

The current theorem does not yet claim:

- cumulative logging of rejected consumed bytes inside `connection_state`;
- full TLS 1.3 feature coverage beyond the supported profile;
- verified parser/serializer C implementations;
- verified crypto/X509 implementations;
- a fully verified top-level driver loop with owned receive buffers and auth
  callbacks beyond the current verified facade boundaries;
- transport honesty beyond the trusted `TLS13.IO` bridge contract;
- general multi-record local application-data send correctness beyond the current
  supported one-record send theorem.

## Audit entry points

Start with these files:

1. `src/impl/TLS13.Impl.Client.fsti` for the public API.
2. `src/impl/TLS13.Impl.Client.Types.fst` for the theorem predicates and trace
   theorem surface.
3. `src/spec/TLS13.Spec.ConnectionState.fst` and
   `src/spec/TLS13.ConnectionLog.fst` for the pure model and layered logs.
4. `src/impl/TLS13.Impl.Client.Driver.fsti` / `.fst` for the verified Pulse
   driver facade and receive-prefix bridge.
5. `runtime/tls13_client_driver.c` for the current C polling around the verified
   runtime entry points.
6. `src/impl/TLS13.Impl.Parser.fsti`, `src/impl/TLS13.Impl.Serializer.fsti`,
   and `c_stubs/tls13_connection_backend.h` for the parser/serializer TCB.
7. `c_stubs/tls13_io_karamel.*`, `c_stubs/tls13_io_stubs.*`,
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
linkage for the Pulse driver facade.
