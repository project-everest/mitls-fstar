# TLS 1.3 client proof status

## End goal

Prove a calc_sample-style end-to-end functional correctness theorem for the extracted, buffer/event-oriented TLS 1.3 client API in `TLS13.Impl.Client`.

The theorem should say that constructors establish a layered invariant, and every exported client step preserves it while tying concrete buffers to the specification:

```text
raw network bytes
  -> TLS outer records
  -> TLS messages / protected record open-seal facts
  -> transcript and key-schedule evolution
  -> connection state-machine events
  -> application log projection
```

The target profile is the implemented TLS 1.3 client profile: X25519, `TLS_CHACHA20_POLY1305_SHA256`, no PSK/0-RTT, certificate validation and CertificateVerify through explicit external TCBs, application data, close_notify, NewSessionTicket ignore, and KeyUpdate handling.

## Current status

We now have a coherent supported-profile trace-level end-to-end theorem, with a deliberately weaker rejected-input story.

The current committed proof surface is centered on `TLS13.Impl.Client`, not the legacy socket/core path:

- `new_client_default` and `new_client` establish `CT.client_state_correct` and `CT.client_end_to_end_invariant`.
- `process_network_bytes` returns `CT.network_bytes_end_to_end_correct`.
- `process_local_event` returns `CT.local_event_end_to_end_correct`.
- Both public step predicates directly preserve `CT.client_end_to_end_invariant`.
- `CT.client_end_to_end_invariant` packages `CT.client_state_correct` with `CS.connection_state_raw_to_message_replay_consistent`.
- `CT.driver_trace_end_to_end` folds those public step predicates over a ghost driver trace.
- `runtime/tls13_client_driver.c` and `runtime/tls13_server_driver.c` are stable C ABI wrappers over the extracted endpoint/canonical protocol surface. They use `Common.TCP` channels, endpoint scheduling, local/API events, residual input buffering before fresh reads, and generated canonical network/local handlers.
- `Common.ProtocolImplementation` is the core refinement contract; `Common.ProtocolEndpoint` adds endpoint frames, concrete buffer preparation, first-order scheduling actions, and TCP I/O resources; `Common.ProtocolDriver` provides the verified fuel-bounded endpoint loop used by the calc socket sample and as the proof contract for TLS monomorphic runtime wrappers.
- TLS endpoint-local callback outcomes are represented as local/API events, not external actions. Certificate validation/signature verification, server parameter selection, shared-secret derivation, signing, application send, and close_notify all go through the canonical local handler path.
- The shared TCP bridge is `Common.TCP` plus `c_stubs/common_tcp_karamel.*`/`common_tcp_stubs.*`. The C shim accepts both generated erased-argument shapes for bundles that erase ghost histories differently.

The invariant now includes:

- pure state reachability;
- layered log consistency;
- cumulative `ConnectionLog.connection_view` consistency;
- cumulative raw-event replay for accepted spec events;
- cumulative sent protected-record seal replay plus write-key provenance;
- cumulative accepted received protected-record decode replay plus read-key provenance;
- transcript, record epoch/sequence, record key/IV, pending app-buffer, KeyUpdate-pending, and app-log projections.

The network theorem currently exposes:

- the exact consumed input prefix via `CT.network_consumed_prefix`;
- every nonzero consumed prefix parses as one TLS outer record and has recursive raw-record segmentation;
- successful non-decode-error consumed prefixes project to decoded TLS messages/events;
- cleartext/protected decoder payload origin;
- protected `ApplicationData` open-to-message facts with read-key schedule provenance;
- accepted received-decode replay preservation;
- `DecodeError` split into zero-consume buffer parser failure versus consumed parsed-record/TLS-message parse failure;
- unconditional consumed-input classification as zero, decode-error parse failure, or decoded TLS message/event;
- emitted network bytes tied to legal raw deltas, write-key provenance, and seal facts.

The local theorem currently exposes:

- readiness through `next_local_action_sound`;
- explicit certificate-validation and CertificateVerify-signature TCB assumptions;
- local app-send supported-profile projection: successful local app sends are bounded to one protected record;
- outgoing record parse facts and protected seal/write-key projections for ClientFinished, app data, close_notify, and KeyUpdate.

The trace theorem now adds:

- state chaining over exported network/local client steps;
- preservation of `CT.client_end_to_end_invariant` from the first state to the final state;
- exact accumulation of accepted-event raw sent/received deltas into the final `cs_wire_log`;
- derived per-step rejected-input witnesses for `DecodeError` and unexpected-message/`IllegalTransition` network steps.

The concrete runtime driver in `runtime/tls13_client_driver.c` now adds only the
stable C ABI around the extracted workflow:

- allocation of the small C wrapper object;
- a connected flag and status-to-error translation;
- calls into `TLS13_Impl_Client_Driver_new_client`, `connect`, `send`,
  `receive`, and `close` (with generated names prefixed in C to avoid POSIX
  symbol collisions).

The Parser/Serializer TCB surface has been narrowed and strengthened:

- unused generic parser/serializer hooks were removed from the active interfaces;
- active parser hooks expose `TLS13.Wire.Spec` parse success/failure facts and raw-record facts;
- live serializer hooks expose exact byte/parse-back/header-AAD/seal facts;
- the C parser shim was tightened to reject trailing Alert/Handshake bytes inconsistent with the wire spec.

Recent committed increments:

- `2d65ec2` preserves `client_end_to_end_invariant` directly in public step predicates.
- `54bb923` strengthens live serializer contracts.
- `612d299` requires raw-record parse facts for every nonzero consumed network prefix.
- `b39efa6` adds the first extracted Pulse driver facade and concrete runtime driver.
- current increment: the OpenSSL interop runtime now goes through the top-level verified Pulse workflow, with auth assumptions isolated in `TLS13.OpenSSL.fsti` and implemented by `c_stubs/tls13_openssl_karamel.*`.

## What remains to prove

### 1. Strengthen the rejected-input story only if we want a stronger theorem

The design choice has been made and implemented for the current theorem.

Accepted received bytes are in the cumulative `cs_wire_log.raw_received` replay. Rejected-but-consumed bytes are currently exposed per step, not cumulatively logged. This includes record-level decode failures and unexpected-message failures after a TLS message has been decoded.

The current theorem uses this design:

- keep the connection-state cumulative log as an accepted-event log;
- derive per-step witnesses for rejected consumed input from `CT.network_bytes_end_to_end_correct`;
- do not claim that all consumed rejected bytes are cumulatively present in `connection_state`.

The stronger "all bytes ever consumed are cumulatively classified" theorem would still require adding a rejected-input log or revising legal-delta semantics.

### 2. Keep shrinking the remaining C runtime shell

The top-level connect (including handshake), receive, send, and close workflow is now in
verified Pulse. The concrete driver no longer calls raw `next_local_action`,
`process_local_event`, `process_network_bytes`, `control_snapshot`, auth copyout
wrappers, or read/process/compact helpers directly. Instead, the runtime's public
C API calls the narrow extracted driver operations: `new_client`, `connect`,
`send`, `receive`, and `close`.

The verified Pulse driver now owns its retained receive/output/auth scratch
buffers. It verifies retained-buffer prefix processing, retained-buffer
read-append into the free suffix, suffix compaction, response writes, internal
local-action processing, typed OpenSSL auth orchestration, fueled top-level
connect/receive/close loops, and `receive` copyout to a caller buffer. The
exact-buffer, standalone read-prefix, and helper recursive buffered-record
functions remain private implementation slices.

Remaining work:

- add a public free/close path for an allocated-but-never-connected driver if that lifecycle becomes part of the public API; today failed connect is terminal, and successful connect must be followed by close;
- decide whether to prove liveness/progress beyond the current fueled workflow status API;
- keep the typed OpenSSL interface (`TLS13.OpenSSL.fsti`) as the explicit auth TCB, or replace it with verified validation/signature code later;
- keep TCP connect/read/write in the unverified `Common.TCP` bridge, with stronger raw byte-log specs when we want transport-honesty proofs;
- preserve the concrete C driver API as the runtime contract while reducing the C wrapper further when practical.

### 3. Make the supported-profile boundary explicit in the final theorem

The current implementation/proof supports one-record local app-data sends and single-record protected replay surfaces. For the final theorem we should either:

- explicitly state the supported-profile theorem with these bounds; or
- implement and prove real multi-record application-data send/receive behavior.

For the near-term end-to-end theorem, the first option is the right path.

### 4. Finish the TCB audit at the theorem boundary

The active Parser/Serializer hooks are verified F*/Pulse code now, so the final theorem should include a concise audited list of the remaining trusted assumptions:

- HACL/crypto wrappers and entropy/X25519;
- X509 chain validation and signature verification;
- Pulse runtime/extraction/runtime shims;
- the TCP bridge used by the concrete driver for connect/read/write.

Replacing these TCBs with verified code is outside the near-term proof unless the goal changes.

### 5. Polish theorem names and documentation

The theorem surface is now packaged, but still large. Before a final audit, document the exact theorem boundary and cross-reference `CT.driver_trace_end_to_end`, `CT.lemma_driver_trace_end_to_end`, and `CT.lemma_driver_trace_from_initial_end_to_end`.

## Estimate

For the supported-profile end-to-end theorem with current TCBs retained:

```text
About 3-6 focused days for audit-ready polish of the current theorem.
```

Breakdown:

- rejected-input design decision and theorem packaging: done for the per-step-witness design;
- trace fold over public steps: done for the ghost exported-step trace theorem;
- supported-profile theorem statement and cleanup: 1-2 days;
- final TCB audit text and proof-surface cleanup: 1-2 days;
- full proof/extraction/runtime gates and fixes: 1-2 days.

If the required theorem must cumulatively account for rejected consumed bytes inside `connection_state`, estimate closer to 2-3 weeks total from here because that is a spec/model change, not a lemma-only strengthening.

If the required theorem also removes Crypto/X509 TCBs or adds full multi-record app-data support, that is substantially larger work, likely several additional weeks to months depending on scope.

## What to audit now

Start with these files:

- `src/impl/TLS13.Impl.Client.fsti`: public API and theorem-returning postconditions.
- `src/impl/TLS13.Impl.Client.Types.fst`: definitions of `client_state_correct`, `client_end_to_end_invariant`, `network_bytes_end_to_end_correct`, `local_event_end_to_end_correct`, and the `driver_trace_end_to_end` theorem surface.
- `runtime/tls13_client_driver.c`, `runtime/tls13_server_driver.c`, and their headers: stable concrete C APIs over the extracted endpoint/canonical protocol runtime path.
- `common/Common.ProtocolImplementation.fst`, `common/Common.ProtocolEndpoint.fst`, `common/Common.ProtocolDriver.fst`, and `common/Common.TCP.fsti`: shared protocol refinement, endpoint scheduling, generic fuel-bounded driver, and TCP-history interface.
- `src/impl/TLS13.OpenSSL.fsti` and `c_stubs/tls13_openssl_karamel.*`: typed OpenSSL auth TCB used by the verified workflow.
- `c_stubs/common_tcp_karamel.*`, `c_stubs/common_tcp_stubs.*`, and the OpenSSL interop tests in `test/unit/`: C ABI bridge and smoke tests for the endpoint-driven runtime path.
- `src/spec/core/TLS13.Spec.StateMachine.fst`: audit-facing core connection-state model and legal deltas. Client/server endpoint machines and exact wire semantics are in `src/spec/core/TLS13.Spec.Endpoint.*` and `TLS13.Spec.StateMachine.Canonical`; replay and preservation properties are isolated under `src/spec/properties`.
- `src/impl/TLS13.Impl.Parser.*` and `src/impl/TLS13.Impl.Serializer.*`: verified parser/serializer facades and their `TLS13.Wire.Spec` postconditions.
- `TLS_DESIGN_AND_IMPL.md`: high-level description of the current proof architecture and remaining gaps.
- `AUDIT.md`: audit-oriented summary of the theorem guarantees, supported profile, verified/C split, and TCB surface.

## Bottom line

The coherent end-to-end theorem now exists for the supported profile: accepted events are cumulative and exact in the connection-state log, while rejected consumed network input is classified by per-step witnesses. The main remaining work is audit/polish and any optional strengthening beyond that theorem boundary.
