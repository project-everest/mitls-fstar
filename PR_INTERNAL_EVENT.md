# Remove the client receive-path semantic fork: internal events

Draft PR description for `chromium` → `agentic`. Not yet opened.

---

## Summary

A protected TLS record can carry several coalesced handshake messages. Before
this work the client described that situation **two different ways** depending
on how many messages the record happened to contain:

- a record with **several** messages → a chain of `ConnProtectedHandshake` events
  (a *head* step plus *tail* steps);
- a record with **exactly one** message → a single `ConnNetworkEvent`.

Two spec shapes for one physical event. That fork propagated everywhere: two
receive functions in the implementation, and a case split in every proof
downstream of receive.

This PR removes the fork. Every client-received protected handshake record now
takes the same route: the record transition installs a pending plaintext, and a
finite sequence of **internal events** consumes it one message at a time. An
internal event is an ordinary `LocalEvent` distinguished only by a syntactic
classifier — no new event constructor, no new product move family.

The design contract is `INTERNAL_EVENT_PLAN.md`, which is included in the diff
and records the decisions, every phase "as built", and the two items left open.

## The one-line change at the centre of it

The entire fork was created by a single conjunct in
`legal_protected_handshake_step` (`src/spec/core/TLS13.Spec.StateMachine.fst`):

```diff
-     consumed < B.length fragment /\
```

That strict inequality said "a head step must leave a tail behind", which forced
a single-message record out of the coalescing shape and into `ConnNetworkEvent`.
Dropping it lets the head step saturate its fragment, so a single-message record
is just the degenerate case of the general one — with the pending buffer left
empty by `set_pending_protected_handshake` and no tail steps following.

Everything else in this PR is the consequence: making the implementation emit
that shape, re-proving the byte-level pairing over it, and deleting the second
path.

## Scope

`c7bec267b..87bbd2670`, 30 commits.

```
 64 files changed, 8530 insertions(+), 700 deletions(-)
```

| Area | Files | +/- |
|---|---|---|
| `src/spec` | 22 | +2266 / −275 |
| `src/impl` | 23 | +3264 / −406 |
| `docs` (incl. the plan) | 5 | +2238 / −2 |
| `common` | 2 | +586 / −2 |
| samples | 10 | +104 / −10 |
| `Makefile` | 1 | +71 / −5 |
| **`runtime/` + `c_stubs/` (C)** | **0** | **0 / 0** |

### The C is untouched — literally

```
$ git diff --name-only c7bec267b HEAD -- runtime c_stubs | wc -l
0
```

Total hand-written C (`runtime/*.c` + `c_stubs/*.c`) is **2718 lines at both
ends of the range**. This was the hardest constraint on the work and the one I
would most want a reviewer to check, because it is what makes the result
meaningful: the receive path was restructured end to end without moving any
responsibility into unverified code.

The responsibility gate holds too, not just the line count:

```
$ grep -rniE 'handshake|record_|0x16|content_type' runtime/*.c c_stubs/*.c
(no output)
```

No C-side record parsing, no C-side handshake sequencing, no C-side scheduling
decision. `runtime/tls13_client_engine.c` is 443 lines and only marshals into
`TLS13_Impl_Client_Engine_poll` / `_feed_network`.

## What a reviewer should look at, in order

### 1. The generic mechanism — `common/Common.ProtocolImplementation.fst`

Five new class fields: `pi_internal`, `pi_internal_pending`,
`pi_internal_frame_pre`, `pi_internal_frame_post`, `pi_process_internal`.

The key design decision (S1 in the plan) is that an internal event is **an
ordinary local event**, not a new kind of event. The payoff shows up in
`internal_process_correct`, which does not restate the step relation — it
*reuses* `local_process_correct`:

```fstar
| InternalProgress ->
  result.internal_process.process_status == StepOk /\
  (exists (ev:local_event).
    is_internal ev /\
    local_process_correct system ev old_out out_bytes out_len
      received0 sent0 st0 result.internal_process
      received1 sent1 st1 wire_outputs local_outputs)
```

So every existing caller that reasons about local steps needs nothing new
(`lemma_internal_process_is_local_process`), and — see §4 below — the system
layer needed no new inductive argument at all.

`pi_process_local` gained `~(pi_internal ev)` in its precondition. That is the
type system enforcing the split rather than a comment asking for it.

### 2. The spec — `src/spec/`

- `TLS13.Spec.StateMachine.fst` — the deleted conjunct above, and the head/tail
  legality relation around it.
- `TLS13.Spec.StateMachine.Replay.fst` (+405) —
  `lemma_single_message_head_step_replay_normalizes`: a single-message head step
  and the old `ConnNetworkEvent` describe the same replay. This is the transport
  lemma that let the fork be removed without weakening the byte-level pairing.
- `TLS13.ConnectionState.ProtectedWireNormalize.fst` (new, +396) — normalising
  raw protected server flights under the new shape.
- `TLS13.Spec.Client.CleartextNoTail.fst` (new, +195) — see §5.
- `TLS13.Spec.InternalEvent.Baseline.fst/.fsti` (new) — Phase 0 characterisation:
  what the old semantics actually said, written down before changing it.

### 3. The implementation — `src/impl/`

- `TLS13.Impl.Client.Drain.fst` (new, +660) — the drain theory. `drain_step`,
  `drain_chain`, `drained`, and `lemma_drained_facts`, which shows a drain chain
  ending in `drained` establishes exactly the end-to-end postcondition a caller
  of the receive primitive expects. Termination is a decreasing measure on the
  pending plaintext (`B.length fragment - parsed`), so **no fuel parameter**.
- `TLS13.Impl.Client.DrainProgress.fst` (new) — deliberately split out so
  `Drain.fst` keeps a fast rebuild; holds everything needing `CanonicalProtocol`.
- `TLS13.Impl.Client.DrainLoop.fst` (new) — the executable Pulse loop.
- `TLS13.Impl.Client.CanonicalProtocol.fst` (+1153/−33) — the single
  `protocol_implementation` instance, now with a real `client_process_internal`.
- `TLS13.Impl.Client.fst/.fsti` (+188/−159) — the fork removal proper; see §6.

### 4. The system layer — `src/impl/TLS13.System.Internal.fst` (new, +318)

This is the part I expected to be hard and wasn't, for a reason worth stating.

Because S1 made the internal event an ordinary local event, an internal step
already travels on an existing product move family: `MP.mp_client_local`, which
asks for a `LocalEvent` step with `so_wire_outputs == []`. So
**`Common.MachineProduct` and `Common.SystemProduct` are untouched**, and "no new
move families" is a proved lemma (`lemma_drain_step_is_client_local`) rather than
a claim in a design doc.

Likewise `combined_inv` was already inductive for `tls_sys_step`
(`lemma_combined_inv_preserved`), so a drain chain transports it via
`RTC.stable_on_closure` with no new inductive proof.

New flagship: `lemma_flagship_settled_record_material_agreement`. It states the
existing agreement theorem at a **settled** state — quiescent *and* nothing
pending internally. `lemma_drain_to_settled` shows every reachable state reaches
a settled one by a finite chain of internal steps, so this is a scheduling side
condition, not a weakening. The original
`lemma_flagship_record_material_agreement` is retained **verbatim** alongside it
(adding a hypothesis weakens a lemma, so keeping both costs nothing and preserves
every caller).

### 5. The cleartext exception is a theorem, not a carve-out

Cleartext handshake records (`ServerHello`, `HelloRetryRequest`) keep the direct
`ConnNetworkEvent` shape. I want to be explicit that this is **not** a residual
fork left for convenience.

`TLS13.Spec.Client.CleartextNoTail.fst` proves a cleartext handshake message
occupies its record fragment *exactly*, so the coalescing shape is **uninhabited**
there. The exception is self-policing: if a future extension makes a cleartext
record carry a tail, `lemma_cleartext_handshake_fragment_has_no_tail` stops
verifying.

One gotcha found the hard way and worth knowing when reading that file: "`hs_buffers`
is unchanged across `step_handshake_message`" is **false** — several branches
legitimately write the certificate leaf DER and the CertificateVerify input. The
preservation lemmas therefore name only `hb_encrypted_server_handshake_bytes` and
`hb_encrypted_server_handshake_parsed`.

### 6. The result is enforced by the interface, not by convention

After the merge, `process_network_bytes` (the record-transition primitive) had
**no caller outside `TLS13.Impl.Client`** — all three production client callers
(`Driver.BufferedNetwork`, `Client.Engine`, `Client.CanonicalProtocol`) go
through `process_coalesced_network_bytes`. So it was removed from the `.fsti`.

This survives extraction. KaRaMeL emits both private helpers as `static` in
`TLS13_Impl_Client.c`:

```c
static TLS13_Impl_Endpoint_Types_endpoint_buffer_response
process_network_bytes(...)

static TLS13_Impl_Endpoint_Types_endpoint_buffer_response
process_direct_record(...)
```

so neither F* nor C can take a receive step that bypasses the pipeline. The
public header exposes exactly three client entry points:
`_process_coalesced_network_bytes` (network),
`_process_pending_protected_handshake` (internal), `_process_local_event` (local).

Also in this area: a vacuous `head_shaped` guard and its dead `else` branch were
deleted (`parse_handshake_prefix` already proves `consumed <= B.length input`),
and `process_legacy_coalesced_fallback` was renamed `process_direct_record` — the
old name was actively misleading, since it is not legacy, not a fallback, and is
the *normal* path for alerts, change-cipher-spec, application data and
post-handshake messages.

### 7. Samples and the gate

All five sample protocols instantiate the same generic classes, so Phase 1's new
fields broke them. Rather than copy the TLS no-internal template into seven
`protocol_implementation` instances, `Common.ProtocolImplementation` gained three
generic definitions — `no_internal_frame_pre`, `no_internal_frame_post` (both
`emp`) and `quiescent_process_internal`. Each instance then needs five one-line
fields.

The migration surfaced ten `Error 19` subtyping failures. Those were **not**
churn: seven from `pi_process_local`'s new `~(pi_internal ev)` precondition and
three from `pe_next_action`'s `action_not_internal` obligation. That is the type
system checking the internal/local split holds outside TLS too.

The root `Makefile` gained `verify-samples`, and `test` now depends on it, so a
future change to `Common.ProtocolImplementation` can no longer silently break a
sample. `admit-count` / `check-admits` were widened from
`src calc_sample/spec calc_sample/impl` to `src common $(SAMPLE_DIRS)`.

## Verification

No admits. No assumes. Green at every one of the 30 commits' phase boundaries,
and at the tip:

```
make -j64 test check-admits
```

```
0 admit(s) found
All F* modules verified                         (289 .fst/.fsti under src/, 19 under common/)
All sample protocols verified                   (96 .fst/.fsti across 5 samples)
extracted client OpenSSL echo test passed
transport-neutral client engine OpenSSL echo test passed
extracted server OpenSSL client interop test passed
Chromium-style async HTTPS demo passed (1 certificate, scheme 0x0804)
OpenSSL HTTP server speculative-preconnect test passed
key schedule binding test passed
```

Expect roughly 15–20 min for `verify` and 5–10 min for the test phase on a
64-way machine, from a warm `_cache`.

## Two things left open — stated, not hidden

**1. `tls_application_ready s ==> tls_settled s` is not proved at the spec level.**

It is discharged *operationally* instead: `TLS13.Impl.Client.Engine.poll` carries
`EngineReady ==> ~(D.internal_pending st1)` in its postcondition, and
`lemma_settled_of_client_quiescent` lifts that to `tls_settled`. So the C API's
Ready signal is literally the antecedent of the flagship theorem.

The purely spec-level derivation was attempted and abandoned: the query crashed
Z3 with an internal assertion failure in `lar_solver.cpp`, and a real proof needs
a replay-level argument that the pending buffer is empty at the completion
boundary. It is not required — the flagship takes `tls_settled` as a hypothesis
and every production caller discharges it — so I recorded it as open rather than
forcing it. It is the **one unticked box** in `INTERNAL_EVENT_PLAN.md` §8.

**2. `test/unit/test_connection_bindings.c` is orphaned.**

Referenced by no Makefile, script or workflow, and calls `process_network_bytes`
unqualified so it does not compile today. It predates this work. Deleting another
author's test seemed out of scope; flagging it so it is not mistaken for
coverage.

## Note on the merge direction

`origin/agentic` has not moved since 2026‑07‑30 (`93e13a73`), which is the merge
base for this branch. `chromium` is 58 commits ahead and 0 behind, and every
`agentic_*` sibling branch is also an ancestor of this tip.

If this PR is opened as `chromium` → `agentic` it will therefore carry **58**
commits, not the 30 described above. The other 28 are pre-existing chromium-branch
work that landed before the refactor began:

- commits 1–11: the transport-neutral client engine, its stable C API, the
  Chromium-style async HTTPS demo and provider integration;
- commits 12–24: the original coalesced protected-handshake modelling — i.e. the
  work that *introduced* the head/tail shape, and with it the fork this PR removes;
- commits 25–28: browser failure reporting, public browsing, ATLAS protocol tracing.

Those account for essentially all of the `runtime/` and `c_stubs/` growth in the
full 58-commit range (+3479 and +229 lines). It may be worth landing them
separately so this PR's "zero C change" property is visible in the diff rather
than only in the phase range.
