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
| Concrete C top-level driver | `runtime/tls13_client_driver.c`, `runtime/tls13_client_driver.h` | Stable C ABI wrapper whose implementation delegates to extracted `TLS13.Impl.Client.Driver` top-level operations for construction, connect including the TLS handshake, application send/receive, and close. |
| Verified Pulse driver | `src/impl/TLS13.Impl.Client.Driver.fsti`, `src/impl/TLS13.Impl.Client.Driver.fst`, `src/impl/TLS13.OpenSSL.fsti`, `c_stubs/tls13_io_karamel.*`, `c_stubs/tls13_openssl_karamel.*` | Narrow top-level Pulse API: `new_client`, `connect`, `send`, `receive`, and `close` over a Pulse-owned `client_driver` containing the extracted client, typed OpenSSL auth context, channel slot, retained receive length, and scratch buffers. Private helpers implement the former lower-level driver/top-driver workflow, auth copyout/completion, local-action drain, buffered-prefix receive+compact, retained-buffer read+compact, and close orchestration. |
| Concrete state representation | `src/impl/TLS13.Impl.ConnectionState.Repr.fst` | Concrete storage records, allocation helpers, ownership predicates, low-level copy helpers, and `connection_exactly`. |
| State queries | `src/impl/TLS13.Impl.ConnectionState.Queries.fst` | Read-only runtime checks, snapshots, and driver copyout helpers. |
| State model helpers | `src/impl/TLS13.Impl.ConnectionState.{Bounds,Model,Tags}.fst` | Constants, pure transition constructors/evolution lemmas, and proof-only control/tag predicates. |
| State mutations | `src/impl/TLS13.Impl.ConnectionState.{Fail,Network,LocalHandshake,LocalAuth,LocalSend,LocalApp}.fst` | Responsibility-specific stateful mutation functions and protocol-transition proof boundaries. |
| Protocol handlers | `src/impl/TLS13.Impl.Handle.*` | Handshake, local-driver, alert, application data, ChangeCipherSpec, decode-error, and dispatch logic. |
| Low-level message layer | `src/impl/TLS13.Impl.Messages.fst` | Extractable `L` messages and Pulse validity predicates relating them to pure `M` messages. |
| Pure wire/message specs | `src/spec/TLS13.Wire.Spec.*`, `src/spec/TLS13.Messages.fst` | Mathematical parse/serialize model and pure TLS messages. |
| Pure connection spec | `src/spec/TLS13.Spec.ConnectionState.fst` | Audit-facing TLS client state model, log invariants, and legal per-step deltas. |
| Connection-state proof support | `src/spec/TLS13.ConnectionState.Lemmas.fst` | Preservation/projection lemmas for the connection-state spec; not part of the primary review surface. |
| Layered log vocabulary | `src/spec/TLS13.ConnectionLog.fst` | Raw I/O logs, records/messages, directed messages, app projection, and stream-shape facts. |
| Lightweight trace automaton | `src/spec/TLS13.StateMachine.fst` | Compact client-only trace/state vocabulary used by `ConnectionLog` and implementation proof projections; it is not the authoritative connection-state model. |
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
  non-cleartext messages. `CT.lemma_legal_network_response_message_projection`
  and `CT.lemma_network_event_step_correct_message_projection` expose the same
  package from the legal network-response / internal network-event theorem
  surface whenever the caller has `network_input_wf` and a parse-success fact.
  For protected inputs, that package now also includes
  `CT.protected_record_decodes_to_message`: the consumed `ApplicationData`
  record opens under the current read state, parses as TLSInnerPlaintext, and
  that plaintext parses as the exact decoded TLS message. Under
  `client_state_correct`, the protected-record projection is packaged as
  `CT.protected_record_decode_correct`, combining that open-to-message fact with
  read-key schedule provenance.
- The active serializer TCB surface no longer includes stale unused ClientHello
  record-header/localhost fixed-builder declarations or the unused standalone
  ClientFinished application-data-record declaration. Live fixed helpers now
  expose concrete shape facts: inner plaintext encoding states the copied
  payload slice plus trailing content-type byte and its no-padding
  `parse_plaintext` result, application-data header
  serialization states the public `TLS13.Wire.Spec.parse_record_header` result,
  ClientHello fixed-output serialization exposes the exact public
  `parse_record` result for the emitted cleartext handshake record, raw
  application-data record serialization exposes both public `parse_record` and
  header-AAD facts, and ClientFinished encrypted-output serialization exposes a
  public `parse_record` fact, exact serialized outer-record/header-AAD facts,
  and the corresponding `Record.Spec.seal` equation.
  Finished handshake serialization also exposes that the generated 36-byte
  handshake buffer parses as `TlsHandshake (Finished ...)`.
- The received Certificate and CertificateVerify state-transition interfaces
  expose the exact driver-copyout facts needed by the external validation TCB:
  certificate leaf DER is the head of the parsed certificate chain, and
  CertificateVerify input is computed from the pre-CV transcript hash.
- The local send state-transition interfaces expose outgoing record parse facts:
  successful ClientHello sends parse as the exact cleartext handshake record, and
  successful ClientFinished, application-data, close_notify, and KeyUpdate sends
  parse as one outer `ApplicationData` record. Protected local sends also prove
  a `CS.sent_event_seal_projection` tying the emitted ciphertext to the current
  write state, emitted record-header AAD, and TLSInnerPlaintext bytes for the
  sent message.
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
  CertificateVerify input, and parsed signature. The local end-to-end theorem
  exposes these assumptions through `CT.local_auth_tcb_projection`, and
  `CT.legal_local_response` now pins the successful validation event to that
  peer and the successful signature event to the parsed CertificateVerify.
- There are no explicit `admit()` or `assume_` sites under `src/` or
  `calc_sample/`.
- The strongest current proof surface is per-step preservation of
  `TLS13.Impl.Client.connection_exactly` /
  `TLS13.Impl.ConnectionState.Repr.connection_exactly` plus spec-level legal
  response/delta facts. The legal response predicate also states that the API
  `app_out` prefix is exactly
  `CL.concat_bytes (CS.conn_event_app_received_delta ev)`, and local
  send-application-data responses tie their payload to
  `CL.concat_bytes (CS.conn_event_app_sent_delta ev)`. The spec also has a
  preserved `connection_state_layered_log_consistent` invariant that packages
  event-log replay from the initial config, transcript projection from serialized
  handshake events, KeyUpdate response-pending state, non-failed record
  epoch/sequence projection, record key/IV consistency with the key schedule,
  pending application-buffer consistency, and app-log projection from
  `cs_event_log`. The public client invariant also includes
  `connection_state_connection_log_view_consistent`, which packages the cumulative
  `ConnectionLog.connection_view` stream shapes, record-prefix parsing, host-trace
  TLS/state-event/app projections, and pending-app source shape. It now also
  includes `connection_state_raw_event_replay_consistent`, proving that the
  cumulative raw sent/received logs replay as per-event raw deltas, each legal at
  the model state where the corresponding event occurs; the client theorem
  surface exposes preservation lemmas for `legal_response_for_event`,
  `some_legal_response`, `network_bytes_step_correct`, and
  `local_event_step_correct`. The public
  `TLS13.Impl.Client` postconditions now use the compact end-to-end predicates
  `network_bytes_end_to_end_correct` and `local_event_end_to_end_correct`; the
  lower-level step, record, and event predicates remain internal proof
  vocabulary. The `new_client_default` and configured `new_client` constructors
  now establish `client_state_correct` plus explicit initial sent/received replay,
  key-provenance replay, and protected raw-segmentation replay facts, so callers
  can chain directly into the end-to-end step predicates. The streaming network
  predicate exposes public `parse_record` success facts for every nonzero
  consumed raw prefix, and the `process_network_bytes` theorem
  shape names the exact consumed input prefix instead of hiding it behind an
  existential. The local-step predicate exposes `parse_record` success for
  non-empty local network output. `next_local_action_sound` also proves that
  ready non-external local actions satisfy `local_input_wf` with the empty
  payload; certificate-validation readiness now also proves the parsed
  Certificate and copied leaf DER are present, while certificate validation and
  CertificateVerify signature checking remain explicit external TCB actions.
  `TLS13.Spec.ConnectionState` now packages
  the layered log invariant, cumulative connection-log view consistency, and
  cumulative raw-event replay as `connection_state_full_log_consistent`.
  `TLS13.Impl.Client.Types` uses that package in compact step theorems:
  `client_state_correct` combines pure reachability with
  `connection_state_full_log_consistent`, cumulative sent-seal replay, and
  cumulative accepted received-decode replay, with historical write/read-key
  schedule provenance folded into those sent/received replay packages, and
  `network_bytes_end_to_end_correct` / `local_event_end_to_end_correct` prove
  that the public API step predicates preserve it while explicitly projecting
  the resulting cumulative connection-log view, raw-event replay, sent-seal
  replay, and historical sent/received key-provenance replay facts. The network
  theorem also exposes `network_consumed_raw_record_projection`: every non-empty
  consumed prefix, including record-level decode-error rejection, is a single
  raw TLS record and has the
  recursive raw-record segmentation fact needed by downstream raw-log proofs.
  `client_end_to_end_invariant` packages `client_state_correct` with
  `connection_state_raw_to_message_replay_consistent`: cumulative raw-event
  replay, protected raw-record segmentation, sent protected-record seal replay
  with write-key provenance, and accepted received protected-record decode replay
  with read-key provenance. The public network/local end-to-end step predicates
  themselves preserve that named invariant; the corresponding helper lemmas keep
  the projection convenient for callers.
  Successful non-decode-error byte steps additionally expose
  `network_bytes_decoded_message_projection`, tying the hidden parser witnesses
  to `network_input_message_projection` for the public consumed prefix. That
  projection now includes `network_input_decoder_payload_projection`: cleartext
  messages expose the cleartext raw law, while protected messages expose the
  `Record.Spec.open_record` / TLSInnerPlaintext decoding relation. The theorem
  also exposes `decoded_message_event_projection`, which says the decoded message
  either drives the received-message event or justifies an unexpected-message
  failure while preserving the received raw-delta fact. The public
  `network_bytes_received_event_projection` strips away parser witnesses and
  exposes that same received raw-delta/event-shape fact directly over the exact
  consumed network prefix. Under `client_state_correct`,
  `network_bytes_protected_record_key_schedule_projection` also connects
  non-cleartext consumed prefixes to a protected `ApplicationData` open under the
  current read state whose key/IV are projected from the installed server
  handshake/application traffic material. The same facts are now also packaged as
  `network_bytes_received_decode_projection`, which strips away parser witnesses
  and gives one public per-network-step predicate tying the consumed prefix to
  the received raw delta, decoded-message event shape, and protected
  open-to-message/read-key projection when the input was encrypted.
  `network_bytes_decode_error_projection` now splits `DecodeError` precisely:
  public buffer-level parser failures consume zero bytes, while record-level
  failures expose the consumed raw prefix as a parsed TLS outer record whose TLS
  message parse fails. Under `client_state_correct`,
  `network_bytes_consumed_input_projection` packages the full consumed-prefix
  classification: zero bytes, decode-error parse failure, or a decoded TLS
  message/event with protected-open facts when encrypted.
  `network_bytes_consumed_input_event_projection` exposes the weaker event-level
  consumed-prefix classification unconditionally, without requiring the
  `client_state_correct` key-schedule facts. Both network and local end-to-end
  predicates expose
  `response_network_out_raw_projection`, so non-empty emitted network prefixes
  are tied to the legal event raw delta and protected-record segmentation facts;
  under `client_state_correct`, `response_network_out_write_key_schedule_projection`
  also exposes the current write-state key/IV projection from installed client
  traffic material for protected sent events. The local theorem exposes
  `CT.response_network_out_seal_projection`, recording the concrete
  `Record.Spec.seal` equation over the emitted header AAD and TLSInnerPlaintext;
  the network theorem exposes `CT.network_bytes_network_out_seal_projection`,
  which now carries the same output-seal surface for every network step,
  including exact `LocalFail tls_decode_error` witnesses for `DecodeError`
  responses. `TLS13.Spec.ConnectionState` also has parallel cumulative replay
  predicates for sent single-record protected seals and accepted received
  protected decodes:
  `connection_state_sent_seal_replay_consistent` and
  `connection_state_received_decode_replay_consistent`; these are now packaged
  with raw replay, protected segmentation, and key-provenance replay as
  `connection_state_raw_to_message_replay_consistent`. The public constructors
  expose that package explicitly, and both public network and local end-to-end
  step predicates directly preserve the named `client_end_to_end_invariant`.
  `TLS13.Impl.Client.Types` also packages those per-step facts into a ghost
  trace theorem, `driver_trace_end_to_end`: a chained list of exported
  network/local client steps preserves `client_end_to_end_invariant`, accumulates
  exactly the accepted-event raw sent/received deltas into the final
  `cs_wire_log`, and derives per-step rejected-input witnesses for
  `DecodeError` and unexpected-message `IllegalTransition` network steps. This
  deliberately keeps `connection_state` as the cumulative accepted-event log;
  rejected consumed input is classified locally at the step that consumed it,
  not added to a second cumulative state log.
  Rejected-but-consumed
  decode-error bytes remain exposed per step instead of being included in the
  cumulative raw received log. The local theorem now exposes
  `CT.local_send_application_data_supported_projection`: every successful
  `LocalSendApplicationData` step is within the current supported profile
  (`max_application_data_fragment_len`) and emits exactly one protected
  application-data record. Multi-record local application-data sends remain
  outside the current implementation profile rather than an unproved hidden
  behavior. Rejected DecodeError/unexpected-message bytes are still exposed by
  per-step theorem projections rather than by the cumulative state log; the
  named decode-error projection now records the zero-consume versus
  parsed-record/parse-failure cases explicitly.
  The local theorem also exposes `CT.local_auth_tcb_projection`, making the
  validation and CertificateVerify external-TCB assumptions directly auditable
  from the public postcondition; the legal local-response event match ties those
  assumptions to the concrete local event being handled. In the top-level Pulse
  workflow, successful certificate validation is completed using an
  `auth_payload` subarray whose length is the exact peer-identity prefix returned
  by the typed OpenSSL TCB, so the installed peer is not a padded scratch buffer.
- `runtime/tls13_client_driver.c` now packages the concrete top-level runtime
  driver as a thin ABI wrapper over extracted `TLS13.Impl.Client.Driver`
  operations. It keeps the public C API but stores only the extracted
  `client_driver`, a connected flag, and the last error string. Construction goes
  through verified `new_client`, `connect` performs TCP connect plus TLS
  handshake, application send goes through verified `send`, receive goes through
  verified `receive` which copies plaintext to the caller buffer, and close goes
  through verified `close`.
  OpenSSL-backed certificate validation and CertificateVerify checks are called
  from Pulse through the typed `TLS13.OpenSSL.fsti` TCB. The OpenSSL echo interop
  test links the driver bundle and exercises this runtime. The workflow treats
  short writes from `TLS13.IO.write` as `DriverWorkflowStepFailed`, so it does not
  report handshake/send/receive/close success after emitting only a prefix of a
  verified TLS record.
- `TLS13.Impl.Client.Driver` now verifies and extracts the intended narrow
  top-level workflow rather than exposing every orchestration slice. The public
  Pulse API is `new_client`, `connect`, `send`, `receive`, and `close`; generated
  C symbols stay module-prefixed to avoid POSIX `connect`/`send`/`close`
  collisions. The private helper layer still contains the client/channel
  `driver`, snapshots, auth copyout and local-event completion, local-action
  steps/drain, retained-buffer prefix processing, retained-buffer read-append via
  `TLS13.IO.read` and `Pulse.Lib.Array.sub`/`return_sub`, suffix compaction,
  application-data send, close_notify, and channel close. Exact-buffer receive,
  standalone read-prefix receive, and helper buffered-loop functions remain
  private implementation slices. External certificate validation and
  CertificateVerify are explicit typed auth TCB actions in `TLS13.OpenSSL.fsti`.
  The extracted C smoke test exercises the narrow generated API surface.
  `make test-extracted-client-driver-slice` extracts this module to C and
  compiles/runs a smoke test through `c_stubs/tls13_io_karamel.*`.
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
for internal/expert use, and `TLS13_Impl_Parser_parse_tls_message` remains the
message decoder used by the network decoders. The old generic parser entry
points are no longer exposed by `TLS13.Impl.Parser.fsti`, and
`process_tls_record` / `process_network_event` are no longer exported by
`TLS13.Impl.Client.fsti`; the driver-facing network API is
`process_network_bytes`.

No active C shim should forward to old framing modules or undefined generated
symbols. New parser/serializer hooks should be added directly to
`TLS13.Impl.Parser` / `TLS13.Impl.Serializer` with postconditions tied to the
`M`/`L` validity predicates and `TLS13.Wire.Spec`. Unused generic parser or
serializer hooks should stay out of the interface rather than expanding the
handwritten TCB surface.

Other trusted runtime boundaries remain:

- HACL*/backend crypto wrappers for primitive behavior matching
  `TLS13.Crypto.Spec`;
- entropy and X25519 key generation;
- OpenSSL-backed certificate-chain validation and CertificateVerify signature
  checking, now isolated behind the typed `TLS13.OpenSSL.fsti` interface and
  implemented by `c_stubs/tls13_openssl_karamel.*` plus
  `c_stubs/tls13_openssl_stubs.c`; certificate validation hands the verified
  local event only the exact returned identity prefix;
- Pulse/F*/KaRaMeL/runtime infrastructure, allocation, and C platform behavior;
- the TCP bridge in `c_stubs/tls13_io_stubs.c` that connects explicit
  input/output buffers to socket reads and writes. The extracted Pulse driver
  facade currently uses the small `c_stubs/tls13_io_karamel.*` ABI shim for
  `TLS13_IO_connect_tcp`, `TLS13_IO_read`, `TLS13_IO_write`, and
  `TLS13_IO_close`; prefix/exact-buffer adaptation after `TLS13.IO.read` and
  buffered-prefix adaptation plus retained-buffer read-append and suffix
  compaction are now verified in Pulse rather than implemented in C.

## Critical gaps

1. The public step theorem is now calc_sample-shaped at the exported API level:
   `process_network_bytes` and `process_local_event` directly return
   `network_bytes_end_to_end_correct` / `local_event_end_to_end_correct`, which
   preserve `client_state_correct` and expose the raw-record, decoded-message,
   received-event, received-decode, decode-error, protected-open/read-key-schedule,
   emitted-network-byte/write-key, and cumulative raw-event replay projections
   currently available. `client_state_correct` now also packages cumulative
   sent-seal replay and accepted received-decode replay with historical
   write/read-key schedule provenance. The exported end-to-end predicates also
   project those key-provenance replay facts explicitly from
   `client_state_correct`. The separate public replay projections remain as
   compatibility/audit facts. The remaining theorem
   gap is
   completeness of the layered invariant itself, not the absence of a compact
   preservation wrapper.
2. `ConnectionLog` and `Spec.ConnectionState` still need one stronger layered
   invariant proving that consumed/emitted raw bytes parse, decrypt, and
   interpret as exactly the TLS messages/events that drive the state machine and
   app log. Raw protected deltas can now be segmented record-by-record from the
   existing legal-delta facts, the raw-event replay has a cumulative protected
   raw-segmentation replay derivation, cumulative `ConnectionLog.connection_view`
   stream and TLS/state-event/app host-trace projections plus cumulative
   raw-event replay are packaged into `client_state_correct`, and parser successes now
   expose a packaged decoded-message projection for cleartext/protected records,
   including a read-key-schedule projection for protected opens. Sent protected
   single-record outputs and accepted received protected inputs now have
   cumulative replay predicates, including historical write/read-key provenance,
   folded into `client_state_correct`;
   successful local application-data sends are publicly constrained to the
   current one-record supported profile. Rejected-but-consumed received decode
   steps now have per-step parse-failure projections and a packaged
   consumed-prefix classification, but still need cumulative treatment if the
   final driver theorem wants total consumed-byte accounting inside the spec
   raw received log.
   Event-log replay,
   transcript projection, KeyUpdate response-pending state, non-failed record
   epoch/sequence projection, record key/IV consistency with the installed key
   schedule, pending application-buffer consistency, and app-log projection are
   now packaged into an explicit preserved spec invariant, but decryption and
   remaining event-projection facts still need to be connected into it.
3. Parser/serializer contracts still need a complete entry-by-entry audit. The
   strongest entries already carry `M`/`L` validity and `TLS13.Wire.Spec`
   facts, and stale unused fixed builders have been removed, but every supported
   record/message path must be classified against the final theorem needs.
4. Certificate and CertificateVerify copyout/local-event proofs are much
   clearer: received-message transitions expose exact leaf-DER and
   CertificateVerify-input copyout facts, and the public local-input predicate
   states the X509/signature TCB assumptions. The final theorem still needs to
   package these facts into one auditable end-to-end statement.
5. The top-level driver polling is now verified Pulse code. The concrete C
   wrapper only tracks the extracted driver handle, connection state, and last
   error; Pulse owns the retained/scratch buffers and copies plaintext into
   caller buffers. The Pulse workflow covers the
   client/channel pair, typed OpenSSL auth context, control snapshots, auth
   copyout and local-event completion, ready internal local steps, retained-buffer
   buffered-prefix network processing with response writes, retained-buffer
   read-append, suffix compaction, fueled connect/receive/close workflows,
   application send, close_notify send, optional peer-close wait, channel close,
   and auth context free. The receive side has verified retained-buffer prefix/read-append
   bridges: the full buffer is split, only the active prefix is passed to
   `process_network_bytes`, the free suffix is split before `TLS13.IO.read`, and
   the full buffer is restored. The remaining proof-polish step is to prove
   liveness beyond the current fueled status API, if that becomes part of the
   theorem.
6. The old root `TLS13.Impl.ConnectionState.fst` facade is gone, but future
   changes must preserve the explicit responsibility split rather than recreating
   a catch-all mutation module.
7. Runtime interop is evidence, not proof. OpenSSL tests are essential, but they
   do not replace codec specs, raw-byte invariants, or the public theorem.

## Remaining work

1. Lock `TLS13.Impl.Client.fsti` as the public proof/API boundary.
   Keep it buffer/event oriented and avoid driver-supplied ghost artifacts.
2. State the final `process_network_bytes` theorem in terms of
   `TLS13.Spec.ConnectionState` and a strengthened layered invariant. It should
   prove that consumed network prefixes, emitted network prefixes, and app
   observations are justified by legal spec deltas. The current named predicate
   already exposes the consumed prefix as `network_consumed_prefix` and carries
   a public raw-record parse-success fact for every nonzero consumed input.
3. State the corresponding local theorem for `next_local_action` and
   `process_local_event`, with explicit assumptions for certificate validation,
   peer signature verification, and local application requests. The current
   `next_local_action_sound` predicate already proves empty-input admissibility
   for ready non-external local actions, and certificate-validation readiness
   exposes the stored Certificate plus copied leaf DER that the external driver
   must validate.
4. Strengthen `TLS13.ConnectionLog` / `TLS13.Spec.ConnectionState` so raw bytes,
   record parsing, decryption, transcript updates, traffic secrets, KeyUpdate
   epochs, pending buffers, and app-log projection live in one invariant. The
   spec now has admit-free one-record, non-empty-prefix, head/tail,
   parser-fuel-saturation, recursive segmentation, event-log replay,
   transcript-projection, KeyUpdate response-pending, non-failed record
   epoch/sequence projection, record key/IV-to-key-schedule consistency,
   pending application-buffer consistency, app-log-consistency preservation, and
   cumulative connection-log view consistency and cumulative raw-event replay
   lemmas, with legal-delta/client-response/public-step projections, plus a
   parser-success-to-raw-log inverse bridge, an on-demand cumulative protected
   raw-segmentation replay derivation, and cumulative sent-seal plus accepted
   received-decode replay inside `client_state_correct`.
   The client surface now also
   exposes `network_input_message_projection`, derived from `network_input_wf`,
   `network_bytes_received_decode_projection` over the public consumed prefix,
   `network_bytes_decode_error_projection` for zero-consume parser failures and
   consumed record-level parse failures,
   `network_bytes_consumed_input_projection` as the one-step classifier for the
   whole consumed prefix under `client_state_correct`,
   `network_bytes_consumed_input_event_projection` as the unconditional
   zero/decode-error/decoded-event classifier,
   `local_send_application_data_supported_projection` for successful local app
   sends in the current one-record supported profile, and exact decode-error
   local-fail witnesses, so next raw-log work should build
   on those decoded-message projection facts to connect key schedule, KeyUpdate
   epochs, pending buffers, rejected consumed-byte decryption facts, supported
   one-record sent seals, and remaining event-log projections.
5. Continue auditing `TLS13.Impl.Parser.fsti` and
   `TLS13.Impl.Serializer.fsti` entry by entry. Mark each supported
   message/record as strong or weak relative to the required `M`/`L` +
   `TLS13.Wire.Spec` postconditions, strengthen weak live entries, and keep
   unused generic parser/serializer hooks out of the TCB surface.
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
