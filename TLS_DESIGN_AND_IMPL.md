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
  `c_stubs/tls13_connection_backend.h`. Their success contracts now include
  `TLS13.Wire.Spec.parse_record` facts for the raw outer record bytes; the
  dispatcher fragment relation is now explicit in `CT.network_input_wf`.
  Cleartext records expose the outer fragment. `ApplicationData` records expose
  a `TLS13.Record.Spec.open_record` result under the current read state and
  record-header AAD, followed by TLSInnerPlaintext decoding. The C shim no
  longer accepts synthetic plaintext-in-ApplicationData records, zero-AAD
  protected opens, or decrypted protected records whose opened bytes fail
  TLSInnerPlaintext decoding. The client theorem surface now packages these
  facts as `CT.network_input_message_projection`: a parsed network message is
  tied to the raw outer record parse, the cleartext/protected decoder-fragment
  relation, the legal received raw delta, and protected-record segmentation for
  non-cleartext messages.
- The active serializer TCB surface no longer includes stale unused ClientHello
  record-header/localhost fixed-builder declarations or the unused standalone
  ClientFinished application-data-record declaration. Live fixed helpers now
  expose concrete shape facts: inner plaintext encoding states the copied
  payload slice plus trailing content-type byte, application-data header
  serialization states the public `TLS13.Wire.Spec.parse_record_header` result,
  ClientHello fixed-output serialization exposes the exact public
  `parse_record` result for the emitted cleartext handshake record, and raw
  application-data record serialization plus ClientFinished encrypted-output
  serialization expose public `parse_record` facts for emitted
  application-data records.
- The received Certificate and CertificateVerify state-transition interfaces
  expose the exact driver-copyout facts needed by the external validation TCB:
  certificate leaf DER is the head of the parsed certificate chain, and
  CertificateVerify input is computed from the pre-CV transcript hash.
- The local send state-transition interfaces expose outgoing record parse facts:
  successful ClientHello sends parse as the exact cleartext handshake record, and
  successful ClientFinished, application-data, close_notify, and KeyUpdate sends
  parse as one outer `ApplicationData` record.
- The pure connection spec now has a reusable one-record bridge:
  `lemma_raw_records_exactly_one_parse_record` turns
  `raw_records_exactly raw outer 1` into an exact
  `TLS13.Wire.Spec.parse_record raw == Some (outer, fragment, length raw)` fact.
  The inverse bridge `lemma_parse_record_full_raw_records_exactly` turns a
  full-buffer parser fact back into `raw_records_exactly` and recursive
  segmentation, with `CT.lemma_raw_record_parse_success_raw_records` exposing
  that bridge at the client theorem surface. The raw-log bridge is also
  packaged through protected single-record message/event deltas and through the
  client-side `legal_response_for_event` projection. Multi-record protected
  deltas now expose a first-record parse prefix via
  `lemma_raw_records_exactly_nonempty_parse_record` and the corresponding
  legal-delta/client-response projection lemmas. For protected message raw
  deltas, parser-fuel saturation lifts the head/tail view back to ordinary
  `raw_records_exactly`, and `lemma_raw_records_exactly_segmented` proves full
  recursive record-by-record segmentation through the client response surface.
- The public `process_local_event` input predicate now makes the external
  certificate/signature TCB assumptions explicit: `LocalValidateCertificate`
  assumes `TLS13.X509.Spec.validate_chain` returns the peer identity being
  installed, and `LocalVerifyCertificateSignature` assumes
  `TLS13.Crypto.Spec.verify_signature` succeeds over the stored peer key,
  CertificateVerify input, and parsed signature.
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
  `TLS13.Impl.Client` postconditions use named theorem-surface predicates
  `network_bytes_step_correct` and `local_event_step_correct`; lower-level
  record/event predicates remain internal proof vocabulary. The streaming
  network predicate exposes public `parse_record` success facts for
  non-decode-error consumed raw records, and the `process_network_bytes` theorem
  shape names the exact consumed input prefix instead of hiding it behind an
  existential. The local-step predicate exposes `parse_record` success for
  non-empty local network output. `next_local_action_sound` also proves that
  ready non-external local actions satisfy `local_input_wf` with the empty
  payload; certificate validation and CertificateVerify signature checking
  remain explicit external TCB actions. This is substantial progress, but it is
  not yet the final end-to-end correctness theorem.
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
2. that C helper parses TLS record headers inline and then dispatches through
   `TLS13_Impl_Parser_parse_tls_message`.

`TLS13_Impl_Parser_decode_network_record` remains part of the parser TCB surface
for internal/expert use, but `process_tls_record` and `process_network_event`
are no longer exported by `TLS13.Impl.Client.fsti`; the driver-facing network API
is `process_network_bytes`.

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
   app log. Raw protected deltas can now be segmented record-by-record from the
   existing legal-delta facts, and parser successes now expose a packaged
   decoded-message projection for cleartext/protected records, but transcript,
   key-schedule, and app-projection facts still need to be connected into the
   invariant.
3. Parser/serializer contracts still need a complete entry-by-entry audit. The
   strongest entries already carry `M`/`L` validity and `TLS13.Wire.Spec`
   facts, and stale unused fixed builders have been removed, but every supported
   record/message path must be classified against the final theorem needs.
4. Certificate and CertificateVerify copyout/local-event proofs are much
   clearer: received-message transitions expose exact leaf-DER and
   CertificateVerify-input copyout facts, and the public local-input predicate
   states the X509/signature TCB assumptions. The final theorem still needs to
   package these facts into one auditable end-to-end statement.
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
   observations are justified by legal spec deltas. The current named predicate
   already exposes the consumed prefix as `network_consumed_prefix` and carries
   a public raw-record parse-success fact for non-decode-error consumed input.
3. State the corresponding local theorem for `next_local_action` and
   `process_local_event`, with explicit assumptions for certificate validation,
   peer signature verification, and local application requests. The current
   `next_local_action_sound` predicate already proves empty-input admissibility
   for ready non-external local actions.
4. Strengthen `TLS13.ConnectionLog` / `TLS13.Spec.ConnectionState` so raw bytes,
   record parsing, decryption, transcript updates, traffic secrets, KeyUpdate
   epochs, pending buffers, and app-log projection live in one invariant. The
   spec now has admit-free one-record, non-empty-prefix, head/tail,
   parser-fuel-saturation, and recursive segmentation lemmas, with
   legal-delta/client-response projections, plus a parser-success-to-raw-log
   inverse bridge. The client surface now also exposes
   `network_input_message_projection`, derived from `network_input_wf`, so next
   raw-log work should build on those decoded-message projection facts to connect
   transcript, key schedule, KeyUpdate epochs, pending buffers, and app-log
   projection.
5. Continue auditing `TLS13.Impl.Parser.fsti` and
   `TLS13.Impl.Serializer.fsti` entry by entry. Mark each supported
   message/record as strong or weak relative to the required `M`/`L` +
   `TLS13.Wire.Spec` postconditions, then strengthen weak entries or document
   them as narrow fixed-builder TCBs.
6. Make the certificate and CertificateVerify boundary auditable by proving that
   driver-visible copyout bytes are exactly the certificate leaf DER,
   CertificateVerify input, and signature bytes from the parsed handshake, and
   that successful local events correspond to the X509/signature TCB specs.
   The current public local-input predicate already states these X509/signature
   assumptions; the remaining work is to package them into the final theorem.
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
