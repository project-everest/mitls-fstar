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
- `runtime/tls13_client_driver.c` is now a thin C ABI wrapper over the extracted `TLS13.Impl.Client.Driver` top-level workflow: connect calls `driver_open`, handshake calls `driver_handshake`, send calls `top_driver_send_application_data`, receive calls `driver_receive_application_data`, and close calls `driver_close_workflow`.
- `TLS13.Impl.Client.Driver` now contains a curated C-facing Pulse driver facade and a `top_driver` workflow. The lower-level facade still exposes connect, snapshots, auth copyout/completion, local-action steps/drain, retained-buffer prefix processing, retained-buffer read-append, suffix compaction, application send, close_notify, and channel close. The top-level workflow adds typed OpenSSL auth orchestration through `TLS13.OpenSSL.fsti`, fueled handshake/receive loops, and close orchestration; certificate validation splits the auth payload to the exact validated peer-identity prefix before completing `LocalValidateCertificate`. Exact-buffer receive, standalone read-prefix receive, and helper buffered-record loops remain implementation-private.
- The top-level workflow checks response write counts: if a local or network `StepOk` emits network bytes but `TLS13.IO.write` writes a short prefix, the workflow returns `DriverWorkflowStepFailed` instead of advancing to apparent success.
- The Pulse driver facade has a separate extraction path, `make test-extracted-client-driver-slice`, with small C ABI bridges for extracted IO (`c_stubs/tls13_io_karamel.*`) and the typed OpenSSL TCB (`c_stubs/tls13_openssl_karamel.*`).

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

- fixed runtime buffers for retained network input, network output, app output,
  and auth scratch space;
- status-to-error translation and caller plaintext copyout;
- calls into `driver_open`, `driver_handshake`, `top_driver_send_application_data`,
  `driver_receive_application_data`, and `driver_close_workflow`.

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

The top-level handshake, receive, send, and close workflow is now in verified
Pulse. The concrete driver no longer calls raw `next_local_action`,
`process_local_event`, `process_network_bytes`, `control_snapshot`, auth copyout
wrappers, or read/process/compact helpers directly. Instead, the runtime's public
C API calls `driver_open`, `driver_handshake`, `top_driver_send_application_data`,
`driver_receive_application_data`, and `driver_close_workflow`.

The verified Pulse facade remains caller-buffer-supplied rather than fully
heap-owning. It verifies retained-buffer prefix processing, retained-buffer
read-append into the free suffix, suffix compaction, response writes, internal
local-action processing, typed OpenSSL auth orchestration, and fueled top-level
handshake/receive/close loops. The exact-buffer, standalone read-prefix, and
helper recursive buffered-record functions remain private implementation slices.

Remaining work:

- design a Pulse-owned heap driver state with receive/output/auth buffers if we want to remove the remaining C buffer ownership and wrapper allocation code;
- decide whether to prove liveness/progress beyond the current fueled workflow status API;
- keep the typed OpenSSL interface (`TLS13.OpenSSL.fsti`) as the explicit auth TCB, or replace it with verified validation/signature code later;
- keep TCP connect/read/write in the unverified C bridge, with stronger `TLS13.IO` specs over raw byte logs when we want transport-honesty proofs;
- preserve the concrete C driver API as the runtime contract while reducing the C wrapper further when practical.

### 3. Make the supported-profile boundary explicit in the final theorem

The current implementation/proof supports one-record local app-data sends and single-record protected replay surfaces. For the final theorem we should either:

- explicitly state the supported-profile theorem with these bounds; or
- implement and prove real multi-record application-data send/receive behavior.

For the near-term end-to-end theorem, the first option is the right path.

### 4. Finish the TCB audit at the theorem boundary

The active Parser/Serializer hooks are much stronger now, but the final theorem should include a concise audited list of trusted assumptions:

- parser and serializer C shims;
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

If the required theorem also removes Parser/Serializer/Crypto/X509 TCBs or adds full multi-record app-data support, that is substantially larger work, likely several additional weeks to months depending on scope.

## What to audit now

Start with these files:

- `src/impl/TLS13.Impl.Client.fsti`: public API and theorem-returning postconditions.
- `src/impl/TLS13.Impl.Client.Types.fst`: definitions of `client_state_correct`, `client_end_to_end_invariant`, `network_bytes_end_to_end_correct`, `local_event_end_to_end_correct`, and the `driver_trace_end_to_end` theorem surface.
- `runtime/tls13_client_driver.c` and `.h`: stable concrete C API and thin wrapper around the extracted top-level Pulse workflow.
- `src/impl/TLS13.Impl.Client.Driver.fsti` and `.fst`: curated verified/extracted Pulse driver facade, top-level workflow, private helper slices, and the current transport/auth TCB boundary.
- `src/impl/TLS13.OpenSSL.fsti` and `c_stubs/tls13_openssl_karamel.*`: typed OpenSSL auth TCB used by the verified workflow.
- `c_stubs/tls13_io_karamel.*` and `test/unit/test_extracted_client_driver_slice.c`: C ABI bridge and smoke test for the extracted Pulse driver facade.
- `src/spec/TLS13.Spec.ConnectionState.fst`: `connection_state_raw_to_message_replay_consistent`, legal deltas, cumulative replay predicates, and the accepted-versus-rejected raw-byte distinction.
- `src/impl/TLS13.Impl.Parser.fsti` and `src/impl/TLS13.Impl.Serializer.fsti`: active TCB contracts.
- `c_stubs/tls13_connection_backend.h`: handwritten C implementation of parser/serializer assumptions.
- `TLS_DESIGN_AND_IMPL.md`: high-level description of the current proof architecture and remaining gaps.
- `AUDIT.md`: audit-oriented summary of the theorem guarantees, supported profile, verified/C split, and TCB surface.

## Bottom line

The coherent end-to-end theorem now exists for the supported profile: accepted events are cumulative and exact in the connection-state log, while rejected consumed network input is classified by per-step witnesses. The main remaining work is audit/polish and any optional strengthening beyond that theorem boundary.
