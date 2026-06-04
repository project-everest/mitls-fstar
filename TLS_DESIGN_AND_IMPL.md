# TLS 1.3 client functional-correctness plan

## End goal

Build and prove a fully functional TLS 1.3 client for the supported profile:
TLS 1.3, X25519, `TLS_CHACHA20_POLY1305_SHA256`, no PSK/0-RTT, basic
certificate validation and CertificateVerify through specified external TCBs,
application data, close_notify, tickets, and KeyUpdate behavior supported as
currently implemented.

The verified core is the extraction-oriented buffer/event API in
`TLS13.Impl.Client`. Network I/O belongs in an external driver. The proof target
is a calc_sample-style public theorem showing that each extracted client step
preserves a layered invariant from concrete raw buffers through parsed TLS
records/messages, transcript and key schedule evolution, state-machine events,
and application-log projection.

## Active architecture

| Area | Modules/files | Role |
| --- | --- | --- |
| Public extracted API | `src/impl/TLS13.Impl.Client.fsti`, `src/impl/TLS13.Impl.Client.fst` | Constructor, driver-hint, network-input, local-event, and observation/copyout entry points. |
| Response/event types | `src/impl/TLS13.Impl.Client.Types.fst` | Extraction-facing response types plus legal-response predicates. |
| Concrete state representation | `src/impl/TLS13.Impl.ConnectionState.Repr.fst` | Concrete storage records, allocation helpers, ownership predicates, low-level copy helpers, and `connection_exactly`. |
| State queries | `src/impl/TLS13.Impl.ConnectionState.Queries.fst` | Read-only runtime checks, snapshots, and driver copyout helpers. |
| State model helpers | `src/impl/TLS13.Impl.ConnectionState.{Bounds,Model,Tags}.fst` | Constants, pure transition constructors/evolution lemmas, and proof-only control/tag predicates. |
| State mutations | `src/impl/TLS13.Impl.ConnectionState.{Fail,Network,LocalHandshake,LocalAuth,LocalSend,LocalApp}.fst` | Responsibility-specific stateful mutation functions and protocol-transition proof boundaries. |
| Protocol handlers | `src/impl/TLS13.Impl.Handle.*` | Handshake, local-driver, alert, application data, ChangeCipherSpec, decode-error, and dispatch logic. |
| Low-level message layer | `src/impl/TLS13.Impl.Messages.fst` | Extractable `L` messages and Pulse validity predicates relating them to pure `M` messages. |
| Pure wire/message specs | `src/spec/TLS13.Wire.Spec.*`, `src/spec/TLS13.Messages.fst` | Mathematical parse/serialize model and pure TLS messages. |
| Pure connection spec | `src/spec/TLS13.Spec.ConnectionState.fst` | Rich TLS client state model and legal per-step deltas. |
| Layered log vocabulary | `src/spec/TLS13.ConnectionLog.fst` | Raw I/O logs, records/messages, directed messages, app projection, and stream-shape facts. |
| Record/crypto implementation | `src/impl/TLS13.Record.*`, `src/impl/TLS13.KeySchedule.*` | Extracted record-layer and key-schedule implementation against crypto TCBs. |
| Parser/serializer TCB | `src/impl/TLS13.Impl.Parser.fsti`, `src/impl/TLS13.Impl.Serializer.fsti`, `c_stubs/tls13_connection_backend.h` | Interface-only F*/Pulse contracts implemented by handwritten C macros/static helpers. |
| Runtime tests | `test/unit/test_connection_bindings.c`, `test/unit/test_extracted_client_openssl_echo.c`, `test/openssl_echo_server.c` | Deterministic extracted-client API tests and local OpenSSL TLS 1.3 interop. |

The public client API is buffer/event oriented:

- `new_client_default` and `new_client` allocate a client state;
- `next_local_action` tells the external driver when certificate validation,
  CertificateVerify, Finished, application send, close, or KeyUpdate local work
  is ready;
- `process_network_bytes` is the normal network-input entry point;
- `process_tls_record` and `process_network_event` are lower-level helpers that
  may remain public only if they are useful as testing/theorem sub-surfaces;
- `process_local_event` realizes driver-provided local actions;
- copyout hooks expose auditable driver inputs such as certificate leaf DER and
  CertificateVerify bytes/signature.

## Current status

- The active extracted client path implements meaningful protocol behavior for
  the supported profile: ClientHello, ServerHello, EncryptedExtensions,
  Certificate, CertificateVerify, server Finished verification, application key
  installation, ClientFinished, application data, close_notify,
  NewSessionTicket ignore, received KeyUpdate, and requested-KeyUpdate response.
- Server Finished is checked at runtime against transcript-derived expected
  `verify_data` before the verified state advances. The implementation
  serializes the stored parsed Finished internally for local verification rather
  than exposing a public driver copyout hook.
- The old parser/framing hooks have been removed from the active
  `TLS13.Impl.Parser` TCB surface and C backend. The active network path uses
  `TLS13_Impl_Parser_decode_network_buffer` and
  `TLS13_Impl_Parser_decode_network_record`, both implemented in
  `c_stubs/tls13_connection_backend.h`.
- There are no explicit `admit()` or `assume_` sites under `src/` or
  `calc_sample/`.
- The strongest current proof surface is per-step preservation of
  `TLS13.Impl.Client.connection_exactly` /
  `TLS13.Impl.ConnectionState.Repr.connection_exactly` plus spec-level legal
  response/delta facts. The legal response predicate also states that the API
  `app_out` prefix is exactly
  `CL.concat_bytes (CS.conn_event_app_received_delta ev)`, and local
  send-application-data responses tie their payload to
  `CL.concat_bytes (CS.conn_event_app_sent_delta ev)`. The public
  `TLS13.Impl.Client` postconditions use named theorem-surface predicates:
  `network_event_step_correct`, `tls_record_step_correct`,
  `network_bytes_step_correct`, and `local_event_step_correct`. This is
  substantial progress, but it is not yet the final end-to-end correctness
  theorem.
- `TLS13.Impl.ConnectionState` has been split by responsibility: `Repr` owns the
  concrete representation and exact predicates, `Queries` owns read-only checks
  and copyouts, `Model`/`Bounds`/`Tags` own pure/proof helpers, and the mutation
  surface is split across `Fail`, `Network`, `LocalHandshake`, `LocalAuth`,
  `LocalSend`, and `LocalApp`. The old root `TLS13.Impl.ConnectionState.fst`
  facade has been removed.

## C shim and TCB boundary

`TLS13.Impl.Parser.fsti` and `TLS13.Impl.Serializer.fsti` are interface-only TCB
modules. Their extracted calls are satisfied by macros/static helpers in
`c_stubs/tls13_connection_backend.h`, included into generated C by the KaRaMeL
`-add-include` flags in `make extract-bundle`.

The active network input path is:

1. `process_network_bytes` calls `TLS13_Impl_Parser_decode_network_buffer`;
2. `process_tls_record` calls `TLS13_Impl_Parser_decode_network_record`;
3. those C helpers parse TLS record headers inline and then dispatch through
   `TLS13_Impl_Parser_parse_tls_message`.

No active C shim should forward to old framing modules or undefined generated
symbols. New parser/serializer hooks should be added directly to
`TLS13.Impl.Parser` / `TLS13.Impl.Serializer` with postconditions tied to the
`M`/`L` validity predicates and `TLS13.Wire.Spec`.

Other trusted runtime boundaries remain:

- HACL*/backend crypto wrappers for primitive behavior matching
  `TLS13.Crypto.Spec`;
- entropy and X25519 key generation;
- OpenSSL-backed certificate-chain validation and CertificateVerify signature
  checking, matching `TLS13.X509.Spec` / crypto verification specs;
- Pulse/F*/KaRaMeL/runtime infrastructure, allocation, and C platform behavior;
- the external network driver that connects explicit input/output buffers to TCP
  reads and writes.

## Critical gaps

1. The public theorem is not yet calc_sample-shaped. Callers have strong
   per-step specs, but not one small top-level theorem saying the extracted
   client implements the pure TLS client spec from raw buffers to app
   observations.
2. `ConnectionLog` and `Spec.ConnectionState` still need one stronger layered
   invariant proving that consumed/emitted raw bytes parse, decrypt, and
   interpret as exactly the TLS messages/events that drive the state machine and
   app log.
3. Parser/serializer contracts are uneven. The final TCB audit must cover every
   supported record/message with parse/serialize facts against `TLS13.Wire.Spec`.
4. Certificate and CertificateVerify copyout/local-event proofs must make the
   exact byte correspondence to parsed handshake inputs explicit.
5. The old root `TLS13.Impl.ConnectionState.fst` facade is gone, but future
   changes must preserve the explicit responsibility split rather than recreating
   a catch-all mutation module.
6. Runtime interop is evidence, not proof. OpenSSL tests are essential, but they
   do not replace codec specs, raw-byte invariants, or the public theorem.

## Remaining work

1. Lock `TLS13.Impl.Client.fsti` as the public proof/API boundary.
   Keep it buffer/event oriented and avoid driver-supplied ghost artifacts.
2. State the final `process_network_bytes` theorem in terms of
   `TLS13.Spec.ConnectionState` and a strengthened layered invariant. It should
   prove that consumed network prefixes, emitted network prefixes, and app
   observations are justified by legal spec deltas.
3. State the corresponding local theorem for `next_local_action` and
   `process_local_event`, with explicit assumptions for certificate validation,
   peer signature verification, and local application requests.
4. Strengthen `TLS13.ConnectionLog` / `TLS13.Spec.ConnectionState` so raw bytes,
   record parsing, decryption, transcript updates, traffic secrets, KeyUpdate
   epochs, pending buffers, and app-log projection live in one invariant.
5. Audit `TLS13.Impl.Parser.fsti` and `TLS13.Impl.Serializer.fsti` entry by
   entry. Mark each supported message/record as strong or weak relative to the
   required `M`/`L` + `TLS13.Wire.Spec` postconditions, then strengthen weak
   entries or document them as narrow fixed-builder TCBs.
6. Make the certificate and CertificateVerify boundary auditable by proving that
   driver-visible copyout bytes are exactly the certificate leaf DER,
   CertificateVerify input, and signature bytes from the parsed handshake.
7. Keep the `TLS13.Impl.ConnectionState.*` split explicit and behavior-preserving:
   use `CR`/`ConnectionState.Repr` for storage and `connection_exactly`,
   `CQ`/`ConnectionState.Queries` for read-only checks/copyouts, and
   the specific mutation module (`Fail`, `Network`, `LocalHandshake`,
   `LocalAuth`, `LocalSend`, or `LocalApp`) for state updates. Do not reintroduce
   a broad re-export facade.
8. Keep runtime coverage aligned with the proof target by maintaining the
   deterministic binding test and the OpenSSL interop test through the extracted
   `TLS13.Impl.Client` API.

## Validation workflow

Use the existing repository commands:

```sh
# full F*/Pulse verification
make verify

# C shim syntax checks
make check-c-stubs

# generate extracted C
make extract-bundle

# deterministic extracted-client API test
make test-connection-bindings

# local OpenSSL TLS 1.3 interop
make test-openssl-echo

# admit and diff hygiene gates
make check-admits
git --no-pager diff --check
```

`make test-connection-bindings` is the smallest useful command for confirming
that extracted C compiles and the public client API works. `make test` includes
the binding test but not `test-openssl-echo`; run
`make test-connection-bindings test-openssl-echo` for extracted-client runtime
confidence.

For the calc methodology reference:

```sh
cd calc_sample
make verify
make check-admits
make test-c
```
