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
and records the decisions and every phase "as built". Nothing in it is left
open; the last item, and the latent defect that closing it exposed, is described
under "The last open item" below.

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

`c7bec267b..e1f47d5d3`, 34 commits.

```
 88 files changed, 9674 insertions(+), 2221 deletions(-)
```

| Area | Files | +/- |
|---|---|---|
| `src/spec` | 22 | +2288 / −277 |
| `src/impl` | 29 | +3576 / −466 |
| `docs` (incl. the plan) | 8 | +2831 / −143 |
| `common` | 2 | +586 / −2 |
| samples | 20 | +221 / −25 |
| `Makefile` | 1 | +89 / −7 |
| `scripts/`, `setup.sh`, `generated/` | 4 | +82 / −3 |
| **`runtime/` + `c_stubs/` (C)** | **0** | **0 / 0** |

The deletion count is dominated by the stale `test/unit/test_connection_bindings.c`
(1297 lines) described below.

Two of the 34 commits are not part of the refactor proper and can be reviewed
independently:

- **`Upgrade the toolchain to Z3 4.15.3`.** Z3 4.13.3 aborts with an internal
  assertion failure in `lar_solver.cpp` on arithmetic-heavy queries, which F*
  surfaces only as `Failure("Parse error: </labels> not found")`. The upgrade is
  wired through `Z3_VERSION` in the Makefiles and `scripts/install-z3.sh`; A/B
  against the old solver with `make verify Z3_VERSION=4.13.3`. It carries nine
  proof repairs — all resource exhaustion rather than genuine failures, so all
  fixed by making the obligation smaller. Note `.checked` files do not record
  the solver version, so any re-measurement needs the caches wiped.
- **`Delete the stale test/unit/test_connection_bindings.c`.**

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

## The last open item, and the bug it turned up

`INTERNAL_EVENT_PLAN.md` §8 has **no unticked boxes**. The last one —
`tls_application_ready s ==> tls_settled s` — is now
`TLS13.System.Internal.lemma_application_ready_settled`. Getting there found a
real defect, so it is worth reading rather than skimming.

The statement was **false as originally written**, and the earlier attempt to
prove it was looking for an argument that cannot exist. The claim was that
application readiness implies no internal step is enabled. But:

- the client reaches `ControlApplicationData` by *sending* its own Finished —
  `step_handshake_message`, case `CL.Sent, M.Finished _, ControlHandshaking
  HsServerFinishedVerified` — which is a local event with no precondition on the
  pending protected-handshake buffer; and
- `legal_protected_handshake_step` deliberately does *not* require a record's
  plaintext to be drained to the end. A head step may take delivery of a record
  and leave a remainder; that permissiveness is what removed the receive-path
  fork in the first place.

Composing the two: a client that is handed a coalesced record, drains as far as
the server Finished, and then sends its own Finished, is application-ready with
protected-handshake plaintext still buffered — that is, with an internal step
still enabled. No replay-level argument could have closed that, because there
was nothing to close; the predicate was simply too weak.

### It is worse than a weak predicate: the state was wedged

`legal_handshake_message` admits **no** message at all in
`ControlApplicationData` — it falls through to `| _, _, _ -> False`. So the
leftover plaintext in that state can never be consumed by any legal step. A
server that appends trailing bytes after its Finished in the same record parks
the client permanently unsettled: `tls_internal_pending` holds forever, and no
drain can clear it.

This is a liveness defect rather than an injection one — nothing can be smuggled
in, precisely because nothing at all is legal post-handshake — but it is a real
defect in the model, not merely an inconvenience for one proof.

Both halves of that were machine-checked before the fix was written:

- the `Sent Finished` transition provably carries a **non-empty** buffer through
  into `ControlApplicationData`; and
- in `ControlApplicationData`, `legal_protected_handshake_step` is provably
  false for **every** step.

`client_end_to_end_invariant` does not exclude the state either — the obvious
`Lemma` attempting to derive buffer-emptiness from it does not go through.

### The fix, at the state machine

An earlier revision of this branch strengthened only
`client_driver_application_ready`, adding the buffer conjunct so the lemma went
through. That made the lemma true but left the model unchanged — it excluded the
bad state by hypothesis instead of making it unreachable, and quietly weakened
every theorem that takes readiness as an antecedent. Review caught it. The fix
now lands where the defect is:

- **`legal_handshake_message`** requires `protected_handshake_buffer_empty` on
  the client's `CL.Sent, M.Finished _, ControlHandshaking
  HsServerFinishedVerified` case. The client may not declare the handshake
  finished while holding unconsumed protected-handshake plaintext. (There is
  precedent for strengthening this predicate — see the existing notes in
  `TLS13.Impl.Server.fst` and `…ConnectionState.Queries.fst`.)
- **`can_send_client_finished_runtime`** checks it, reusing the existing
  `protected_handshake_buffer_empty_runtime` query, which is what discharges the
  new obligation in `try_send_client_finished`.
- **`client_driver_application_ready`** keeps the conjunct. That is not
  redundancy: it is the honest reading of "has finished reacting" rather than
  "has arrived", and it is the conjunct the lemma consumes.

The whole tree absorbed this in **two** proof failures, both exactly where the
obligation should land: the client's Finished send path, and
`lemma_client_step_preserves_stage_ok` in `TLS13.System.fst`. The latter was
pure resource cost — `--query_stats` showed one of seven split queries going
`reason-unknown=canceled` at the full rlimit 100 while its neighbours used
0.08–24 — and was fixed by splitting the network arm on the message direction,
which brought it to 0.4 and 21.9. No rlimit was raised.

**The interop tests are the evidence the guard is satisfiable.** It is now a
runtime precondition on sending Finished: if real servers left trailing bytes
after their Finished, `can_send_client_finished_runtime` would return false and
the handshake would fail outright. The OpenSSL echo, extracted-server,
client-engine and Chromium async HTTPS tests all still pass.

The operational route is unchanged and still available:
`TLS13.Impl.Client.Engine.poll` carries `EngineReady ==> ~(D.internal_pending
st1)`, which `lemma_settled_of_client_quiescent` lifts to `tls_settled`.

### Also in this PR: one stale test deleted

`test/unit/test_connection_bindings.c` (1297 lines) predated this work,
was referenced by no Makefile rule, script or workflow, and did not compile — it
called `process_network_bytes` unqualified. It was removed along with its whole
footprint: the `test/test_connection_bindings` line in `.gitignore`, and the
`BindingTest` node plus its `BindingTest -> Client` edge in `arch.dot`, with
`arch.svg` regenerated by `dot -Tsvg`. No gate changes, because it was in no gate.

Six further orphans remain under `test/unit/` (`test_common_tcp_stubs.c`,
`test_connection_driver_bindings.c`, `test_extracted_client_driver_slice.c`,
`test_extracted_server_driver_slice.c`, `test_openssl_stubs.c`,
`test_record_bindings.c`). They are out of scope here and untouched, but worth a
look separately — they are equally unreferenced by the build.

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
