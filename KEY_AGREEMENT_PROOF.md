# Counting-free key agreement proof

Summary of the `agentic_ltl` branch relative to `agentic` (merge-base `37fbc7db9`).

**40 commits, +17,623 / −4,331 lines excluding attic renames. `make check-admits` reports 0** —
no `admit`, `assume`, or `magic` anywhere in `src/` or `calc_sample/`.

Most of the raw diffstat is noise: roughly 60 files under `attic/clean16/` are pure renames with
**zero changed lines**. The substantive change is much smaller than the line count suggests.

---

## 1. TLS spec changes

Only four spec files changed.

### `src/spec/core/TLS13.Spec.StateMachine.fst` (+83 / −20)

The one real model change, referred to throughout the tree as **Model-Fix-1**.

**Atomic Finished delivery.** Both `CL.Received, M.Finished` arms previously did nothing but
`R.next_seq` — bump the read sequence number. They now, in a *single* step:

1. append the Finished to the transcript,
2. derive the peer application traffic secret from the transcript **through** the Finished,
3. `R.install_keys … R.Application` on the record read direction.

The client arm (`ControlHandshaking HsCertificateVerifyVerified`) lands at
`HsServerFinishedVerified` and sets `hs_server_finished_verified`. The server arm
(`ControlHandshaking HsServerFinishedSent`) additionally advances straight to
`ControlApplicationData`.

*Why this was necessary.* The old two-step formulation left a window in which one endpoint could
legally send a record under application keys that the peer had not yet installed and therefore
could not decrypt. That window is precisely what breaks key agreement, so closing it was a
prerequisite for the flagship theorem rather than an optimisation.

Note the deliberate ordering asymmetry between the two arms: the client derives its secret *after*
appending the server Finished, whereas the server derives *before* appending the client Finished.
In both cases the secret is keyed on the transcript through the **server** Finished.

**A failed connection sends nothing.** A new arm `M.TlsAlert alert, ControlFailed _` makes
`CL.Sent` yield `None`, while `CL.Received` re-fails idempotently. Previously a connection that had
already failed could still emit an alert, which is not a real transition.

**Strengthened legality side conditions.**

- `W.certificate_representable` on the `Certificate` arm of `legal_handshake_message`.
- `W.certificateVerify_representable` on the `CertificateVerify` arm of `legal_handshake_message`
  and on the `LocalSignCertificateVerify` arm of `legal_local_event`.
- `Some? hs.hs_keys.ks_master_secret` on both `Received Finished` arms — the atomic step cannot
  derive a traffic secret without it.

### `src/spec/properties/TLS13.Spec.StateMachine.Log.fst` (+9 / −1)

The projection is kept in step with the model:

- `conn_event_transcript_delta` now emits `W.serialize_handshake (M.Finished fin)` on
  `CL.Received`, not just on `CL.Sent`.
- `projected_record_layer_step_for_role` maps `CL.Received, M.TlsHandshake (M.Finished _)` to
  `projected_install_keys R.Application` (seq reset to 0) instead of `projected_next_seq`.

### `src/spec/properties/TLS13.Spec.StateMachine.KeyMaterial.fst` (+17 / −8)

The `Application` / `TrafficWrite` / `ControlHandshaking` escape hatch (which simply returned
`True`) is narrowed from all roles to `ClientEndpoint` only. The in-file comment records that even
the client clause is never actually exercised — during the client's send-Finished window the record
write direction is still at the Handshake epoch — so the clause only avoids an obligation that has
no honest witness.

### Not spec: the new proof modules

Everything else added under `src/spec/properties/` is **new proof material, not specification**:
roughly 20 modules including the Canonical shape family, the NoCcs family, and the two large
`ProtectedWire*Inversion` bridges (4,126 and 3,379 lines). These add lemmas; they do not change
what the protocol means.

---

## 2. Pulse implementation changes

Six files, but only **two real Pulse functions**.

### `src/impl/TLS13.Impl.ConnectionState.Network.fst` (+602 / −116)

`mark_received_server_finished` and `mark_received_client_finished`. This is where the model change
is paid for at runtime. Each now:

1. serialises the Finished (36 bytes) via `Ser.serialize_finished_handshake`,
2. copies it into the transcript buffer and bumps `transcript.len`,
3. hashes the transcript with `Crypto.sha256_prefix`,
4. derives the application traffic secret and key material,
5. installs the record read keys.

Previously these functions only incremented a counter. There are **no new top-level definitions** —
the entire change lives inside the two existing `fn` bodies.

### Precondition strengthening (+200 total)

`Queries.fst` / `Queries.fsti` (`can_receive_server_finished`, `can_receive_client_finished`),
`Model.fsti` / `Model.fst` (`received_server_finished_state`, `received_client_finished_state`,
`lemma_received_server_finished_state_evolves`), and `Network.fsti` all gain the same two
conjuncts:

- `Some? … hs_keys.ks_master_secret`
- `B.length … hs_transcript + 36 <= max_transcript_len` — the new buffer-space obligation

`received_server_finished_state` also changed from `Tot` to `GTot`, since it now hashes.

### Proof glue

`src/impl/TLS13.Impl.Server.fst` (+10) and `src/impl/TLS13.Impl.Server.Auth.fst` (+8) invoke
`W.lemma_certificate_representable` / `W.lemma_certificateVerify_representable` (plus the
`lemma_cert_chain_total_bytes_*` helpers) to discharge the newly strengthened `legal_*` arms. No
behavioural change.

**Worth stressing:** the Pulse-side blast radius of a semantic model change is two functions plus
two lemma invocations. The refinement proof absorbed the rest.

---

## 3. The invariant

`tls_system_inv` (`src/impl/TLS13.System.fst:424`) is 21 conjuncts over the system state
`{client; server; channel}`. Grouped by role:

**Well-formedness.** `SMR.connection_state_consistent` on each endpoint; role pinning
(`config_role == ClientEndpoint` / `ServerEndpoint`); `WFL.supported_client_config_wire_profile`;
`WStep.hellos_shape` on both; `client_start_ok`; the two stage predicates.

**Cross-endpoint hello facts.**

- `hello_coupling` — the two monotone clauses: a stored ServerHello on the client implies the
  server stored (sent) one, and likewise for the ClientHello in the other direction.
- `ch_wire_equiv` / `sh_wire_equiv` (**FACT 1 / FACT 2**) — sender and receiver hold hellos that
  came from *the same raw bytes*.
- `hello_key_shares_ok` (**FACT 3**) — once all four hellos are present, the key shares are paired.

**Byte layer.**

- `client_byte_reachable` / `server_byte_reachable` — each endpoint is reachable from
  `CS.initial cfg` under the *official* canonical step relation.
- `byte_pairing` (**FACT 5**) — channel-aware: `client.sent == server.received ++ in_flight` and
  symmetrically, collapsing to exact `paired_wire_logs` at `TlsQuiet`.

**Channel.** `channel_consistent` is keyed on the **raw bytes alone**: a raw that parses as a
cleartext hello pins the sender's stored hello. A protected record parses as an ApplicationData
record, so the hello antecedent is false and the clause is vacuously true — no cross-endpoint
control-state coupling is required. At a delivery, the receiver's own parse of the raw supplies the
antecedent, which then yields the sender-side hello needed for FACT 1 / FACT 2.

**Payload.** `client_ksp` / `server_ksp` (key-schedule prefix), `client_e2e` / `server_e2e`,
`client_clean`, and `protected_witnesses_ok` (**FACT 4**, the protected-flight projection
witnesses). FACT 4 is marked `opaque_to_smt` so that unfolding the invariant does not drag its
inner existential into every VC that merely carries the invariant as a hypothesis.

---

## 4. How the invariant implies key agreement

```
lemma_reachable_inv             induction over the 6 move families
   ⇒ tls_system_inv s'
lemma_inv_implies_agreement     ⇒ lemma_ready_quiescent_agrees
   ⇒ T.ag tls_sys_step record_material_agrees_when_ready_scoped (initial_tls_system cfg_c cfg_s)
```

The flagship theorem is `lemma_flagship_record_material_agreement`
(`src/impl/TLS13.System.Temporal.fst:82`). In words: **on every run of the system from the initial
state, it is always the case that** if the system is quiescent, has not rekeyed, and both endpoints
have completed the handshake, **then** `SMKM.peer_record_material_agrees` holds for both the
`ClientTraffic` and `ServerTraffic` application traffic identifiers.

The final step is `lemma_ready_quiescent_agrees` (`src/impl/TLS13.System.fst:2999`):

1. `tls_application_ready` pins both control states to `ControlApplicationData`, which via the stage
   predicates forces all four hellos present on both sides.
2. FACT 4 is read directly off the invariant (`reveal_opaque` on `protected_witnesses_ok`) — it was
   discharged once, at the server-verify instant, and is preserved thereafter.
3. FACT 1 / FACT 2 supply the two shared raw byte strings `raw1`, `raw2` by elimination.
4. FACT 3 supplies the paired key shares.
5. These feed
   `P.lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_protected_event_projection_witnesses`,
   whose conclusion `SMKM.supported_profile_application_record_material_agrees` is
   *definitionally* the two agreement conjuncts.

### Two structural points about the shape of the argument

**`tls_sys_step` is the literal canonical product.** Each of the six move families is a channel
precondition, a **verbatim** `EC.client_step` / `ES.server_step`, a wire-output shape, and a
log/channel update — with no additional TLS-specific side conditions. The former strict-progress
`*_advances` guards have been removed along with the entire progress-counting apparatus that
supported them, and `tls_sys_step` is now exactly `SP.product_step tls_iface` over the generic
combinator in `common/Common.SystemProduct.fst`, shared with `Calc.System.sys_step`.

Because removing guards makes the step relation strictly *larger*, the flagship now holds over
*more* behaviours and is proved from a *weaker* invariant. That is strictly stronger, and it removes
the main vacuity concern.

**No-rekeying moved into the antecedent** of the state predicate rather than being pinned inside the
step relation. The honest run never rekeys, so the property still fires along every real run, while
the step relation stays free of TLS-specific gating.

Nonvacuity ultimately rests on the Pulse implementation refining this state machine — which is why
the atomic-Finished change had to be made in *both* the spec and `Network.fst`, and why keeping
`tls_sys_step` matched to the canonical relation matters.

---

## 5. Key file reference

| File | Role |
| --- | --- |
| `src/spec/core/TLS13.Spec.StateMachine.fst` | The canonical model; Model-Fix-1 lives here |
| `src/impl/TLS13.System.fst` | `tls_system_inv`, the six move families, `tls_iface`, `tls_sys_step`, `lemma_pw_establish`, `lemma_ready_quiescent_agrees` |
| `src/impl/TLS13.System.Temporal.fst` | The flagship `T.ag` theorem |
| `common/Common.SystemProduct.fst` | Generic single-slot directed-channel product, shared with Calc |
| `src/impl/TLS13.Impl.ConnectionState.Network.fst` | The two Pulse functions implementing atomic Finished delivery |
| `src/spec/properties/TLS13.ConnectionState.ProtectedWireServerFlightInversion.*` | Field-pinned bridge (server flight) |
| `src/spec/properties/TLS13.ConnectionState.ProtectedWireClientFinishedInversion.*` | Field-pinned bridge (client Finished) |
