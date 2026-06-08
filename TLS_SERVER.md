# Verified TLS 1.3 server plan

This document plans a verified TLS 1.3 server implemented in the same style as
the current verified client: a buffer/event-oriented Pulse core, a narrow
verified top-level driver, explicit typed TCB interfaces, extracted C, and a
small runtime wrapper.

The goal is not a second independent TLS stack. The server should reuse the
current message, wire, record, key-schedule, logging, parser/serializer, driver,
and proof infrastructure wherever that infrastructure is genuinely
role-neutral. Where the current code is client-shaped, the work starts by making the
specification and theorem layers explicitly endpoint/role-parametric. We should
not create a large duplicated server proof stack that later has to be cleaned
up.

## Review decisions

The first implementation will use these decisions:

- Use role-parametric specs and invariants as a hard requirement.
- Use the single-connection server driver API first:
  `new_server`, `accept`, `send`, `receive`, `close`.
- `accept` creates/listens/accepts one TCP channel internally, runs the TLS
  handshake to completion, closes the listener, and returns a connected
  per-connection server handle.
- Omit sending compatibility ChangeCipherSpec in the first version; tolerate
  receiving it only if that remains straightforward in the shared handlers.
- Emit empty `EncryptedExtensions`.
- Use in-memory PEM/DER credential buffers at the typed API boundary, matching
  the current client style of passing trust anchors as bytes rather than making
  protocol code own file I/O.
- Support exactly the credential scheme needed for interop with the verified
  client first: `RsaPssRsaeSha256` (`0x0804`) with an RSA credential compatible
  with RSA-PSS/SHA-256. Other schemes can be added later by extending the typed
  credential TCB and negotiation proof.
- Keep initial failure alerts simple and auditable, with room to refine to
  precise RFC alert mapping after the basic theorem is in place.
- Defer KeyUpdate support if it threatens the basic handshake/app/close
  milestone; otherwise align it with the current client profile.

## Supported server profile

First server version:

- TLS 1.3 server endpoint.
- `TLS_CHACHA20_POLY1305_SHA256`.
- X25519 key exchange.
- Certificate-based server authentication.
- First credential scheme: `RsaPssRsaeSha256` (`0x0804`), because the current
  verified client advertises `[RsaPssRsaeSha256]`.
- No PSK, no 0-RTT, no HelloRetryRequest, no client authentication, no
  resumption, and no early application data.
- Empty `EncryptedExtensions` unless a later interop requirement explicitly
  needs ALPN.
- One TLS record per emitted handshake message in the first implementation:
  cleartext `ServerHello`, then encrypted `EncryptedExtensions`,
  `Certificate`, `CertificateVerify`, and server `Finished`.
- Application data, close_notify, received NewSessionTicket ignore, and
  KeyUpdate handling aligned with the supported client profile.
- Compatibility ChangeCipherSpec is not sent in the first version. Receiving a
  non-transcript CCS may be tolerated if it remains a small reuse of existing
  client-side CCS handling.

The server must reject unsupported or malformed handshakes with explicit failure
transitions. With HelloRetryRequest out of scope, a `ClientHello` that lacks an
X25519 key share, lacks `TLS_CHACHA20_POLY1305_SHA256`, lacks a compatible
signature scheme, or violates the supported profile must fail rather than
silently proceeding.

## Current client baseline to preserve

The current committed client path is the regression baseline:

- `TLS13.Impl.Client.fsti` exposes the verified buffer/event API.
- `TLS13.Impl.Client.Types.fst` defines the client response types, local event
  vocabulary, well-formedness predicates, and end-to-end theorem surface.
- `TLS13.Impl.Client.Driver.fsti` exposes the narrow Pulse top-level API:
  `new_client`, `connect`, `send`, `receive`, and `close`.
- `runtime/tls13_client_driver.c` is a small C wrapper over the extracted
  verified driver.
- `TLS13.IO.fsti` and `TLS13.OpenSSL.fsti` are explicit typed TCB boundaries for
  TCP and client-side OpenSSL authentication.
- `TLS13.Record`, `TLS13.KeySchedule`, `TLS13.Messages`,
  `TLS13.Impl.Messages`, `TLS13.Wire.Spec`, `TLS13.ConnectionLog`, and the
  Pulse array/vector split/restore patterns are intended to be shared.

Every server milestone must keep the current client gates green. The client
proofs are the guardrail against accidentally weakening shared specs.

## Reuse and refactor map

| Layer | Reuse as-is | Refactor or add |
| --- | --- | --- |
| Pure messages | `TLS13.Messages`, most `TLS13.Wire.Spec` parse/serialize functions | Add/strengthen server-specific serialize lemmas and ClientHello acceptability predicates. |
| Low-level messages | `TLS13.Impl.Messages` has L types for client/server handshake messages | Add server-side construction/copy helpers only where missing. |
| Record layer | `TLS13.Record` and `TLS13.Record.Spec` are direction-state based | Reuse; prove server read/write projection lemmas against endpoint role. |
| Key schedule | HKDF labels for client/server traffic secrets are already present | Make endpoint role choose which traffic secret is read/write; avoid client-only assumptions. |
| Logs | `TLS13.ConnectionLog` sent/received raw streams are role-neutral | Reuse; add server trace projections. |
| Parser | Wire parser decodes all handshake message variants | Move parser contracts away from `TLS13.Impl.Client.Types` into shared endpoint predicates. |
| Serializer | Application-data and Finished helpers are partially reusable | Add ServerHello, EncryptedExtensions, Certificate, CertificateVerify, and server Finished builders with parse-back/seal facts. |
| Pure connection model | Currently client-only (`ClientEndpoint`, client phases, client key projections) | Make endpoint-role-parametric; avoid a duplicated server model/proof stack. |
| Pulse connection state | Storage contains many client-specific names but enough general fields | Prefer shared storage where fields are genuinely bidirectional; add server-specific fields for credentials, selected parameters, and signing. |
| Handlers | Current `Handle.*` modules are client-oriented | Use shared helpers and thin client/server dispatchers; server-specific handler modules are acceptable only for genuinely endpoint-specific control flow. |
| Top-level driver | Retained-buffer, read-append, compaction, total-write IO, and ghost transport-history patterns | Reuse the pattern in `TLS13.Impl.Server.Driver`; handshake loop is read-first and signs instead of validates. |
| TCBs | Crypto, record AEAD, TCP read/write/close | Add typed listen/accept IO and typed server credential/signing TCB. |

## Critical TLS server checkpoints

These checkpoints should be written into the pure model before implementing the
Pulse server. They are common sources of off-by-one transcript and wrong-secret
bugs.

1. Receive and validate `ClientHello`:
   - selected cipher suite is offered and equals
     `TLS_CHACHA20_POLY1305_SHA256`;
   - selected group is X25519 and an X25519 key share is present;
   - selected signature scheme is `RsaPssRsaeSha256`, offered by the client, and
     compatible with the configured RSA-PSS/SHA-256 server credential;
   - unsupported profile inputs transition to failure.
2. Send `ServerHello`:
   - generated server random and X25519 ephemeral public key are fresh TCB
     outputs;
   - transcript after this step is `ClientHello || ServerHello`;
   - handshake secret and both handshake traffic secrets are derived from the
     X25519 shared secret and transcript through `ServerHello`.
3. Install handshake traffic keys:
   - server write uses `server_handshake_traffic_secret`;
   - server read uses `client_handshake_traffic_secret`;
   - this is not a mechanical rename of the client invariant.
4. Send encrypted server flight:
   - `EncryptedExtensions`, `Certificate`, `CertificateVerify`, and server
     `Finished` are serialized in order;
   - each message updates the transcript before the next message's proof step;
   - `CertificateVerify` signs
     `TLS13.Handshake.Spec.certificate_verify_input(hash(transcript_before_cv))`;
   - server `Finished` MAC is computed over the transcript through
     `CertificateVerify`.
5. Derive application traffic secrets:
   - application traffic secrets are based on the transcript through server
     `Finished`;
   - the server may store application secrets after sending server Finished, but
     the first supported API must not expose application `send`/`receive` until
     client Finished is verified.
6. Receive client `Finished`:
   - record is opened with the client handshake read key;
   - Finished MAC is verified with the client handshake traffic secret over the
     transcript through server Finished;
   - only after this verification does the connection enter application data and
     install the client application read key.
7. Application and shutdown:
   - server application sends use server application write keys;
   - server application receives use client application read keys;
   - close_notify and KeyUpdate follow the same supported-profile policy as the
     client, with role-correct traffic-secret updates.

## Phase 0: baseline and naming

1. Add server plan artifacts and keep branch hygiene simple:
   - no server implementation code until this plan is reviewed;
   - leave unrelated untracked artifacts untouched.
2. Establish validation commands for the server branch:
   - `make verify`;
   - `make check-admits`;
   - `make extract-driver-bundle`;
   - `make test-extracted-client-driver-slice`;
   - `make test-openssl-echo`.
3. Pick module naming before coding. Recommended names:
   - shared endpoint proof vocabulary: `TLS13.Impl.Endpoint.Types`;
   - pure role-parametric state, if split out:
     `TLS13.Spec.EndpointState`;
   - server public API: `TLS13.Impl.Server.fsti` / `.fst`;
   - server theorem/response vocabulary:
     `TLS13.Impl.Server.Types.fst`;
   - server top-level driver:
     `TLS13.Impl.Server.Driver.fsti` / `.fst`;
   - server credential TCB:
     `TLS13.ServerCredentials.fsti` or `TLS13.OpenSSL.Server.fsti`;
   - runtime wrapper:
     `runtime/tls13_server_driver.h` / `.c`.

## Phase 1: decouple shared endpoint/codec predicates

The parser and much of the handler stack currently import
`TLS13.Impl.Client.Types`, so server reuse requires an explicit decoupling
step.

1. Extract role-neutral definitions from `TLS13.Impl.Client.Types` into a shared
   endpoint module:
   - endpoint step status and response records;
   - response well-formedness over `network_out` and `app_out`;
   - wire parse success predicates;
   - raw consumed-prefix predicates that do not mention client state;
   - record/message parse-back helpers;
   - generic output slice helpers.
2. Keep `TLS13.Impl.Client.Types` as a client theorem module:
   - re-export or alias shared response/status types where possible;
   - keep client-specific local events, `local_input_wf`, `network_input_wf`,
     `client_state_correct`, and `client_end_to_end_invariant`.
3. Change `TLS13.Impl.Parser.fsti` and shared serializer contracts to depend on
   the shared endpoint predicates rather than directly on client theorem
   predicates.
4. Preserve the public client API shape. This phase should be a refactor with no
   behavior change.

Validation gate: client verification, extraction, and interop remain unchanged.

## Phase 2: role-parametric pure state and invariants

The pure model is currently client-only. Server proof work must make this layer
role-parametric rather than duplicating it. Endpoint-specific implementation
modules may exist later, but the theorem vocabulary and invariants should be
shared by construction.

1. Extend endpoint roles:
   - `ClientEndpoint`;
   - `ServerEndpoint`.
2. Split role-specific configuration:
   - client config retains server name, trust anchors, validation time, offered
     cipher suites, and offered signature schemes;
   - server config adds certificate chain, credential identity, allowed signature
     schemes, optional accepted SNI policy, supported cipher suites, supported
     groups, and the RSA-PSS/SHA-256 credential identity for the first version.
3. Replace client-only handshake start with role-aware handshake/session data:
   - client start keeps the current client random/key share/offered lists;
   - server selected parameters record client hello, selected cipher suite,
     selected group, selected signature scheme, server random, server key share,
     and server credential identity.
4. Add server handshake stages. The exact names can change, but the states must
   distinguish at least:
   - awaiting ClientHello;
   - ClientHello accepted;
   - ServerHello sent and handshake keys available;
   - server encrypted flight in progress or sent;
   - server Finished sent and application secrets derived;
   - client Finished received;
   - client Finished verified/application data.
5. Generalize legal events:
   - network received `ClientHello`;
   - network sent `ServerHello`, `EncryptedExtensions`, `Certificate`,
     `CertificateVerify`, server `Finished`;
   - local parameter selection/random generation;
   - local X25519 shared-secret derivation;
   - local traffic-key installation;
   - local CertificateVerify signing;
   - local client Finished verification;
   - application, close_notify, KeyUpdate, and failure events.
6. Generalize read/write key schedule projections:
   - define the expected traffic secret as a function of endpoint role, record
     direction, epoch, and control phase;
   - prove that the client instance reduces to the existing client projection;
   - prove the server instance:
     - write/handshake = server handshake traffic;
     - read/handshake = client handshake traffic;
     - write/application = server application traffic;
     - read/application = client application traffic;
     - handshaking exceptions are re-derived for the server, not copied from the
       client write-side exception.
7. Extend trace and layered-log definitions so both endpoints can prove:
   - raw sent/received replay;
   - message/event projection;
   - transcript consistency;
   - record epoch/sequence consistency;
   - sent seal and accepted received decode replay with role-correct keys;
   - application-log projection.

Validation gate: existing client theorem modules still verify.

## Phase 3: server credential and signing TCB

Client auth currently validates a peer certificate. A server needs a different
typed assumption: it owns a certificate chain and can sign the
CertificateVerify input.

1. Add a pure credential spec, likely in `TLS13.X509.Spec` or a new
   `TLS13.ServerCredentials.Spec`:
   - `server_credential_identity`;
   - certificate chain bytes;
   - leaf public key;
   - supported/compatible signature schemes, initially exactly
     `RsaPssRsaeSha256`;
   - a predicate relating signatures to a credential without exposing private
     key bytes.
2. Add a Pulse TCB interface:
   - allocate/free credential context from in-memory certificate-chain and
     private-key PEM/DER buffers;
   - expose the certificate chain bytes to the server local event;
   - choose or validate `RsaPssRsaeSha256` from the ClientHello offered list;
   - sign the server CertificateVerify input;
   - on success, establish the server `local_input_wf` needed by
     `process_local_event`.
3. Keep server Finished verification out of this TCB. It is HMAC over the
   transcript using existing key-schedule/crypto assumptions.
4. Implement C stubs with OpenSSL only behind the typed interface. The C code is
   trusted for:
   - loading/parsing the certificate and private key from byte buffers;
   - checking RSA-PSS/SHA-256 key compatibility;
   - producing the CertificateVerify signature.

## Phase 4: server codec and serializer support

Server serialization must be precise enough for both interop and proof. The
first version should avoid coalesced handshake records.

1. Add or expose pure wire lemmas for:
   - supported ClientHello acceptability;
   - serialized ServerHello length and parse-back;
   - empty EncryptedExtensions parse-back;
   - Certificate message parse-back over the configured chain;
   - CertificateVerify parse-back over the selected scheme/signature;
   - server Finished parse-back.
2. Extend `TLS13.Impl.Serializer.fsti` with fixed server builders:
   - `serialize_server_hello_from_selection`;
   - `serialize_empty_encrypted_extensions`;
   - `serialize_certificate_from_credential`;
   - `build_server_certificate_verify_input` can reuse the existing server
     context function;
   - `serialize_certificate_verify_from_signature`;
   - `serialize_server_finished_outputs`.
3. Each serializer contract must expose:
   - exact bytes written and length bounds;
   - `TLS13.Wire.Spec.parse_record` or `parse_tls_message` parse-back;
   - header-AAD facts for protected records;
   - `TLS13.Record.Spec.seal` facts for encrypted records;
   - transcript-message equality for the handshake fragment.
4. Extend the C serializer backend in `c_stubs/tls13_connection_backend.h` only
   for these typed hooks. Do not add broad generic serializers unless the proof
   requires them.
5. Keep parser changes minimal: ClientHello parsing already exists, but its
   postconditions must use shared endpoint predicates from Phase 1.

## Phase 5: server core API and theorem surface

Add `TLS13.Impl.Server.Types` and `TLS13.Impl.Server` in the same style as the
client, but do not expose the top-level socket driver here.

Recommended `TLS13.Impl.Server.fsti` shape:

```text
type server = TLS13.Impl.ConnectionState.Repr.connection_state

connection_exactly : server -> server_connection_state -> slprop

new_server :
  certificate/config/credential public bytes ->
  server

next_local_action :
  server -> server_next_local_action

process_network_bytes :
  server ->
  raw input buffer ->
  network output buffer ->
  application output buffer ->
  server_buffer_response

process_local_event :
  server ->
  server_local_event_kind ->
  payload buffer ->
  network output buffer ->
  application output buffer ->
  server_response
```

The public postconditions should mirror the client:

- constructor establishes `server_state_correct` and
  `server_end_to_end_invariant`;
- `process_network_bytes` returns
  `server_network_bytes_end_to_end_correct`;
- `process_local_event` returns
  `server_local_event_end_to_end_correct`;
- both step predicates preserve the server end-to-end invariant;
- emitted bytes expose raw-delta, parse-back, seal, and write-key provenance;
- consumed bytes expose exact prefix, parse/decode classification, open facts,
  and read-key provenance;
- accepted events accumulate into raw sent/received replay and connection-log
  views.

Server local event kinds should be server-specific, for example:

- select parameters / start server handshake after ClientHello;
- derive shared secret;
- install client/server handshake traffic keys;
- send ServerHello;
- send EncryptedExtensions;
- send Certificate;
- sign and send CertificateVerify;
- verify client Finished;
- install client/server application traffic keys;
- deliver application data;
- send application data;
- send KeyUpdate;
- send close_notify;
- fail.

## Phase 6: server state mutations and handlers

Implement server state changes behind small `.fsti` boundaries, following the
client split by responsibility.

1. Prefer shared state/proof helpers and thin endpoint dispatchers. Parallel
   server implementation modules are acceptable for endpoint-specific protocol
   control, but they should depend on the role-parametric pure model rather than
   duplicate it:
   - `TLS13.Impl.Server.ConnectionState.Model`;
   - `TLS13.Impl.Server.ConnectionState.Network`;
   - `TLS13.Impl.Server.ConnectionState.LocalHandshake`;
   - `TLS13.Impl.Server.ConnectionState.LocalSend`;
   - `TLS13.Impl.Server.ConnectionState.LocalApp`;
   - `TLS13.Impl.Server.ConnectionState.Fail`.
2. Extract shared lemmas/helpers early when they express endpoint-independent
   facts. Avoid both extremes: no massive duplicated server proof stack, and no
   single catch-all mixed client/server mutation module.
3. Implement network handlers:
   - parse and accept/reject ClientHello;
   - receive/ignore compatibility CCS if supported;
   - receive client Finished under client handshake read keys;
   - receive application data, alerts, KeyUpdate, tickets, and decode errors.
4. Implement local handlers:
   - generate server random and X25519 key share;
   - select cipher suite/group/signature scheme;
   - derive shared secret and traffic secrets;
   - install server/client handshake keys in role-correct read/write slots;
   - emit each server flight message with transcript updates;
   - verify client Finished;
   - install application traffic keys;
   - send application data, KeyUpdate response, and close_notify.
5. Add negative/failure transitions:
   - unsupported cipher suite;
   - unsupported group or missing X25519 key share;
   - unsupported/credential-incompatible signature scheme;
   - malformed ClientHello;
   - bad client Finished;
   - application data before client Finished;
   - short output buffer;
   - decode/decrypt errors.

## Phase 7: verified top-level server driver

The public server driver should be as narrow as the client driver. The clean
review target is:

```text
new_server
accept
send
receive
close
```

A server has listener state, unlike a client. The first implementation uses the
single-connection API because it is isomorphic to the client driver and easier
to verify:

- `new_server` allocates credential context and Pulse-owned buffers;
- `accept` takes bind host/port, creates a listener internally, accepts one TCP
  channel, runs the TLS handshake to completion, closes the listener, and
  returns a connected server driver;
- `send`, `receive`, and `close` operate on that one connection.

The plan should leave a clear path to split listener and connection state later
without changing the verified per-connection protocol workflow.

Driver internals should reuse the client driver patterns:

- Pulse-owned retained receive buffer;
- Pulse-owned network output, application output, auth/signing scratch buffers;
- `Pulse.Lib.Array.sub` / `return_sub` for exact-prefix processing;
- retained-buffer read-append into the free suffix;
- suffix compaction after consumed prefixes;
- total-write `TLS13.IO.write` postconditions on every response write;
- fueled loops for handshake/receive/close;
- C wrapper owns only a handle, connection/listening flags, and last error.

The server handshake loop differs from the client:

- it is read-first;
- the first successful network event is ClientHello;
- local actions may emit multiple consecutive handshake records;
- signing orchestration replaces certificate-validation orchestration;
- application `send` is disabled until the driver is connected after client
  Finished verification.

## Phase 8: IO, runtime, extraction, and C TCB surface

1. Extend `TLS13.IO.fsti` with server-side typed operations:
   - `listen_tcp`;
   - `accept_tcp`;
   - listener close/free if the API has persistent listeners.
2. Add C implementations in `c_stubs/tls13_io_karamel.c` /
   `tls13_io_stubs.c`, keeping the generated ABI authoritative as with the
   client.
3. Add server credential/signing C shim files, for example:
   - `c_stubs/tls13_server_credentials_karamel.c`;
   - `c_stubs/tls13_server_credentials_karamel.h`;
   - OpenSSL helper code for in-memory certificate/private-key loading and
     RSA-PSS/SHA-256 signing.
4. Add Makefile targets:
   - `extract-server-krml`;
   - `extract-server-bundle`;
   - `extract-server-driver-bundle`;
   - `test-extracted-server-driver-slice`;
   - `test-openssl-sclient`;
   - `test-verified-client-server`.
5. Ensure generated server C symbols remain prefixed, avoiding POSIX name
   collisions with `accept`, `listen`, `send`, and `close`.
6. Keep the C runtime wrapper audit surface small:
   - allocation/free of the wrapper;
   - status-to-error translation;
   - lifetime/connection state tracking;
   - no TLS scratch buffers owned in C;
   - no TLS handshake polling in C.

## Phase 9: validation and tests

Add tests in increasing strength:

1. Pure and extracted smoke tests:
   - server object allocation;
   - server credential context creation/free;
   - server serializer parse-back tests for each emitted handshake message.
2. Protocol unit tests:
   - supported ClientHello accepted;
   - unsupported cipher suite rejected;
   - missing/unsupported X25519 key share rejected;
   - unsupported signature scheme rejected;
   - bad client Finished rejected;
   - application data before client Finished rejected.
3. Runtime interop:
   - OpenSSL `s_client` connects to the extracted verified server and echoes
     application data;
   - verify close_notify behavior;
   - verify KeyUpdate behavior if included in the first server profile.
4. End-to-end in-repo interop:
   - current verified client connects to verified server;
   - application echo round trip;
   - close_notify both directions.
5. Regression:
   - existing OpenSSL echo client test still passes;
   - existing client driver slice test still passes;
   - `make check-admits` stays at zero.

## Proof hardening checklist

For each phase:

- verify `.fsti` before `.fst`;
- keep public postconditions strong enough for downstream callers;
- no `admit()` or `assume_`;
- no broad C fallback that returns success without establishing a typed TCB
  postcondition;
- no hidden weakening of parser/serializer contracts;
- no role-ambiguous key projection lemmas;
- record transcript checkpoints as named lemmas rather than relying on SMT
  unfolding large state updates;
- preserve low rlimits by factoring role-parametric lemmas into small modules.

## Audit/TLS expert checklist

Before calling the server audit-ready, `TLS_SERVER.md`, `AUDIT.md`, and
`STATUS.md` should make these points explicit:

- exact supported profile and rejected features;
- public server APIs and intended usage;
- server handshake transcript sequence;
- key-schedule direction mapping for server read/write states;
- server credential/signing TCB and what it proves;
- parser/serializer C backend TCB additions;
- IO listen/accept TCB additions;
- proof theorem names and how they correspond to the client theorem surface;
- runtime C owned code and why it is not protocol logic;
- validation commands and interop evidence.

## Suggested implementation order

1. Shared endpoint predicate refactor, with client proof unchanged.
2. Role-parametric pure model and key-projection lemmas, with client instance
   unchanged.
3. Server credential/signing spec and typed C/Pulse interface.
4. Server serializer contracts and C backend hooks.
5. Server pure theorem vocabulary and public `TLS13.Impl.Server.fsti`.
6. Server state mutation modules and handlers.
7. Server buffer/event API implementation.
8. Server top-level Pulse driver.
9. Runtime C wrapper and extraction targets.
10. OpenSSL `s_client` interop.
11. Verified client-to-server interop.
12. Audit documentation updates.
