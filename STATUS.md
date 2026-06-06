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
- `runtime/tls13_client_driver.c` now gives a concrete top-level C driver over extracted `Impl.Client`: TCP connect through the I/O bridge, handshake loop, local auth callbacks, app send/receive, and close.
- `TLS13.Impl.Client.Driver` now contains verified Pulse driver slices plus a driver-record facade: one local event is processed through `process_local_event`, successful network output is handed to `TLS13.IO.write`, ready non-external `next_local_action` steps can be driven with an empty payload, bounded local actions can be drained until blocked or fuel is exhausted, certificate/CV data can be copied out for external auth, externally validated local events can be completed through `driver_process_local_event`, exact raw network buffers can be processed and flushed, `TLS13.IO.read` buffers can be split with `Pulse.Lib.Array.sub` so only the received prefix is passed to `process_network_bytes`, application data and close_notify can be sent, and the TCP channel can be closed. The postconditions preserve the public `CT.local_event_end_to_end_correct` / `CT.network_bytes_end_to_end_correct` theorem surfaces for processed steps and record concrete read/write results.
- The Pulse driver facade now has a separate extraction path, `make test-extracted-client-driver-slice`, with a minimal `TLS13.IO` C ABI bridge for extracted connect/read/write/close in `c_stubs/tls13_io_karamel.*`.

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

The concrete runtime driver in `runtime/tls13_client_driver.c` adds:

- reusable C orchestration around `next_local_action`, `process_local_event`, and `process_network_bytes`;
- OpenSSL-backed certificate validation and CertificateVerify handling at the existing explicit TCB boundary;
- application send/receive APIs where received plaintext comes from `process_network_bytes` `app_out`;
- close_notify sending with an optional wait for peer close_notify.

The Parser/Serializer TCB surface has been narrowed and strengthened:

- unused generic parser/serializer hooks were removed from the active interfaces;
- active parser hooks expose `TLS13.Wire.Spec` parse success/failure facts and raw-record facts;
- live serializer hooks expose exact byte/parse-back/header-AAD/seal facts;
- the C parser shim was tightened to reject trailing Alert/Handshake bytes inconsistent with the wire spec.

Recent committed increments:

- `2d65ec2` preserves `client_end_to_end_invariant` directly in public step predicates.
- `54bb923` strengthens live serializer contracts.
- `612d299` requires raw-record parse facts for every nonzero consumed network prefix.
- uncommitted: `CT.driver_trace_end_to_end` packages the accepted-log/per-step-rejection trace theorem, and `runtime/tls13_client_driver.c` factors the concrete OpenSSL interop driver out of the test harness.

## What remains to prove

### 1. Strengthen the rejected-input story only if we want a stronger theorem

The design choice has been made and implemented for the current theorem.

Accepted received bytes are in the cumulative `cs_wire_log.raw_received` replay. Rejected-but-consumed bytes are currently exposed per step, not cumulatively logged. This includes record-level decode failures and unexpected-message failures after a TLS message has been decoded.

The current theorem uses this design:

- keep the connection-state cumulative log as an accepted-event log;
- derive per-step witnesses for rejected consumed input from `CT.network_bytes_end_to_end_correct`;
- do not claim that all consumed rejected bytes are cumulatively present in `connection_state`.

The stronger "all bytes ever consumed are cumulatively classified" theorem would still require adding a rejected-input log or revising legal-delta semantics.

### 2. Move the concrete driver loop into verified Pulse

The concrete driver is now C. The verified Pulse facade in `src/impl/TLS13.Impl.Client.Driver.*` has the same core shape, but remains caller-buffer-supplied rather than fully heap-owning: `driver_connect` creates a client/channel pair, `driver_control_snapshot` observes control state, certificate/CV copyout wrappers expose the bytes needed by external auth, `driver_process_local_event` lets the external-auth TCB complete validation/signature local events, `driver_handshake_step` drives one ready internal local action or exposes the external/need-network blocker, `driver_drain_local_actions` repeats those internal local steps up to a caller-supplied fuel bound, `receive_network_bytes_once` / `driver_receive_application_data_once` processes one exact raw input buffer and writes any response bytes, `driver_read_network_bytes_once` / `driver_read_application_data_once` call `TLS13.IO.read`, use `Pulse.Lib.Array.sub`/`return_sub` to process exactly the received prefix, and restore the full receive buffer, `driver_send_application_data` and `driver_send_close_notify` send local data, and `driver_close` closes the channel. The C smoke test composes `driver_handshake_step` twice, exercises `driver_drain_local_actions`, and calls the read-prefix receive path.

Remaining work:

- design a Pulse-owned driver state with receive buffering and output buffers;
- lift the verified single-read prefix bridge into loops that retain unconsumed record suffixes across reads;
- verify loops that alternate local actions and network records through handshake, app receive, KeyUpdate response, and close;
- keep TCP connect/read/write in the unverified C bridge, with stronger `TLS13.IO` specs over raw byte logs when we want transport-honesty proofs;
- wire the copyout/local-event auth facade into a concrete callback loop;
- preserve the concrete C driver API as the runtime contract while swapping its implementation to extracted Pulse.

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
- `runtime/tls13_client_driver.c` and `.h`: concrete top-level driver API and current C implementation to migrate into Pulse.
- `src/impl/TLS13.Impl.Client.Driver.fsti` and `.fst`: verified/extracted Pulse driver facade and one-step slices plus the current transport-TCB boundary.
- `c_stubs/tls13_io_karamel.*` and `test/unit/test_extracted_client_driver_slice.c`: C ABI bridge and smoke test for the extracted Pulse driver facade.
- `src/spec/TLS13.Spec.ConnectionState.fst`: `connection_state_raw_to_message_replay_consistent`, legal deltas, cumulative replay predicates, and the accepted-versus-rejected raw-byte distinction.
- `src/impl/TLS13.Impl.Parser.fsti` and `src/impl/TLS13.Impl.Serializer.fsti`: active TCB contracts.
- `c_stubs/tls13_connection_backend.h`: handwritten C implementation of parser/serializer assumptions.
- `TLS_DESIGN_AND_IMPL.md`: high-level description of the current proof architecture and remaining gaps.
- `AUDIT.md`: audit-oriented summary of the theorem guarantees, supported profile, verified/C split, and TCB surface.

## Bottom line

The coherent end-to-end theorem now exists for the supported profile: accepted events are cumulative and exact in the connection-state log, while rejected consumed network input is classified by per-step witnesses. The main remaining work is audit/polish and any optional strengthening beyond that theorem boundary.
