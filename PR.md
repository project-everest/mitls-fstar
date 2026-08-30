# Close parity gaps G2 and G3: secp256r1 key exchange, and cross-record reassembly of cleartext handshake messages

Merges the `interop`/`g3` line into `agentic`.  Two of the gaps recorded in
`docs/server-client-parity.md` close here, and with them **every gap that
document tracks**:

* **G2** — the verified server now negotiates **secp256r1 (P-256)** key exchange
  in addition to X25519.
* **G3** — **both roles** now reassemble a cleartext handshake message that
  arrives split across several TLS records: the server a ClientHello, the client
  a ServerHello.

The server capability matrix grows from 34 to 35 cells and the client framing
matrix from 3 to 4; six previously-`refused` cells flip to `ok`.

---

## Part 1 — G2: secp256r1 key exchange

### What this changes for a peer

Before, the server rejected any ClientHello that did not carry a well-formed
32-byte X25519 `key_share`.  It now also accepts one whose only `key_share` is a
well-formed 65-byte uncompressed secp256r1 point, runs the ECDH at whichever
group the acceptance gate picked, tags the ServerHello with that group, and
sizes the record accordingly.  The default `server_supported_groups` becomes
`[X25519; Secp256r1]`.

**X25519 still wins whenever both shares are well formed**, so no pre-existing
peer changes behaviour.

### Interop ledger

| cell | before | after |
| --- | --- | --- |
| `p256-only` | refused | **ok**, at `prime256v1` |
| `p256-first-x25519-listed` | refused | **ok**, at `prime256v1` |
| `ecdsa-credential-p256-only` | refused | **ok**, at `prime256v1` |

`p256-first-x25519-listed` flipped **without** HelloRetryRequest, contrary to the
prediction recorded when the gap was written up.  Given `P-256:X25519`, OpenSSL
sends its `key_share` for P-256 only and merely *lists* X25519 in
`supported_groups`; the gate follows the share that was actually sent.  HRR
remains unimplemented and is now unexercised by the ledger.

### How it is staged

50 commits, in the staging discipline laid out in `docs/server-p256-plan.md`.
S1 through S6.8c are all **capability-neutral**: each makes some layer
group-parametric while the acceptance gate still refuses P-256, so the ledger
does not move and every intermediate commit verifies.

The behavioural flip is a single commit, `c6fdefad6` (S6.8d).  It has to be
indivisible: widening the gate is what makes the group non-constant, and the
ECDH, the ServerHello group tag, the record length arithmetic and the
representation invariant cannot handle a non-constant group until they all move
together.

Three design points that were not obvious:

* **The group pin is a pure *policy* pin.**  Pulse's `rewrite A as B` requires
  both sides provably equal, so a predicate that must survive a state transition
  may only mention what the transition does not change.  Giving the pin the
  handshake state, or even just `hs_client_hello`, breaks the *client* role,
  whose `sent_client_hello_state` rewrites `hs_client_hello` while the selection
  is `None`.  The pin is therefore phrased over
  `sel.server_selected_client_hello`, and the link back to the state comes from
  the reachability lemmas in `TLS13.ConnectionState.Lemmas`.

* **`server_selection_key_share_consistent` now states that the X25519 and P-256
  privates are the same 32 bytes.**  That is what the server does -- one scalar
  is drawn per handshake and used at whichever group is selected -- and it is
  what makes `server_kex_private sel g` reduce for both `g`.

* **The driver-level correctness properties were X25519-specific too.**
  `BN.local_event_success_correct` and
  `BH.derive_shared_secret_from_payload_correct` live two layers above the ECDH
  and were stated with `x25519_shared`; they are now stated with `kex_shared` at
  `client_hello_kex_group_for`.

---

## Part 2 — G3: cross-record reassembly of cleartext handshake messages

### What this changes for a peer

Before, one handshake message had to fit in one TLS record.  A peer whose
ClientHello did not fit -- or whose stack simply chose to fragment it -- could
not connect.  That is a live concern as client hellos grow: post-quantum key
shares push a ClientHello past 1500 bytes and some stacks split them.  The
symmetric case was equally broken and previously unmeasured: the verified
**client** refused a ServerHello torn across two records for exactly the same
reason.

Both directions now work, for arbitrarily many records up to the cap.

Note what is *not* in scope: several handshake messages **coalesced into one**
record are still rejected on the **cleartext** path, because `parse_tls_message`
requires `consumed == B.length fragment`.  That restriction does **not** apply to
the protected path, which has drained several messages out of one record since
`baaa66317` -- `protected_handshake_step` carries an `offset` and a `consumed`
count, and a non-`head` step continues inside the buffer its head published.
It is also close to vacuous in the clear: a ClientHello is the client's whole
cleartext flight and a ServerHello the server's, and a CCS has a different
content type and so cannot share their record.

### Interop ledger

Server matrix (`test/unit/test_server_interop_matrix.c`):

| cell | before | after |
| --- | --- | --- |
| `clienthello-across-two-records` | refused | **ok** |
| `aes128-clienthello-across-two-records` | refused | **ok** |
| `clienthello-across-three-records` | *(new)* | **ok** |

Client matrix (`test/unit/test_client_record_split.c`):

| cell | before | after |
| --- | --- | --- |
| `serverhello-across-two-records` | refused | **ok** |
| `serverhello-across-three-records` | *(new)* | **ok** |

The **three**-record cells are not redundant with the two-record ones.  Two
records only ever buffer onto an EMPTY pending buffer and then deliver; three
make the middle record coalesce onto an ALREADY NON-EMPTY buffer, which is a
distinct branch of the buffering step and was otherwise unexercised.

Both matrices keep their control cells (`passthrough`, `*-tcp-dribble`), and
they are load-bearing in both directions.  They separate the two fragmentations
that are easy to conflate: **TCP-level** segmentation, which the retained
receive buffer and the `NeedMoreInput` retry loop already absorbed, from
**record-level** segmentation, which is what G3 adds.  Without them, a red split
cell could not be distinguished from a broken proxy.

### The design, in one page

The mechanism is a new *buffering step*: a record whose fragment does not parse
as a whole message is consumed, its plaintext set aside, and no message
delivered.  One record is still exactly one protocol step, which is what keeps
`wire_message`, the canonical protocol refinement and the cross-endpoint pairing
theorems intact.

* **One new event.**  `CS.ConnCleartextHandshake` carries a fragment and the
  resulting stream.  `CS.legal_cleartext_handshake_step` gates it on a non-empty
  fragment, on the role's pre-hello control stage, on
  `stream <= max_pending_cleartext_handshake` (32768), and on
  `parse_tls_message Handshake stream == None`.  That last conjunct makes
  buffering a **last resort**: a record whose fragment already parses as a whole
  message can never be buffered instead of delivered, so the pre-existing
  single-record path keeps its meaning exactly.

* **One new raw-delta rule.**  `CS.received_cleartext_tls_message_raw_buffered`
  reads the pending buffer out of the model: with an empty buffer it is
  byte-equality against the canonical single-record serialization (the old
  rule); with a non-empty one it is a parse of `pending ++ fragment`.  It is an
  `if`, not a disjunction, because the replay-determinism proofs in
  `ProtectedWireSegmentation` need the rule to be a **function** of the raw
  bytes.

* **An empty-buffer bridge with an `SMTPat`.**
  `lemma_received_cleartext_tls_message_raw_buffered_of_empty` collapses the new
  rule onto the old one whenever the buffer is empty.  This is why the change is
  affordable: `tls_system_inv` pins both endpoints' cleartext buffers empty, so
  **`TLS13.System.fst` needed no change at all**.  Buffering only ever happens
  *inside* one endpoint's `process_network_bytes`, between two system-visible
  states.

* **A concrete buffer beside the ghost one**, in `ConnectionState.Repr` /
  `.Network` / `.Queries`, with role-agnostic
  `can_buffer_cleartext_handshake` / `copy_pending_cleartext_handshake`.

* **Two entry points per role**, chained ahead of the ordinary decode-error
  path: a delivery that fires only when the pending buffer is NON-empty
  (`try_deliver_reassembled_client_hello`, `try_deliver_reassembled_server_hello`)
  and a buffering step behind it (`try_buffer_cleartext_handshake_record`, one
  per role).  The delivery goes first and both hang off the *"this record did
  not parse"* arm, because **the record that completes a split hello also fails
  to parse on its own fragment** -- it is only the tail.

### Where the two roles genuinely differ

The client's end-to-end correctness statement is stronger than the server's: it
projects a DECODED MESSAGE out of every consumed record.  A message spread over
several records has no such projection, so on the client the reassembled
delivery lands in the **weak** disjunct (`coalesced_head_step_correct`), which
was widened to admit a received cleartext `ConnNetworkEvent` carrying
`raw_record_parse_success` explicitly.  A delivery supplies exactly that
disjunct's four obligations, including a **vacuous** decode projection -- its
guard is `network_message_is_cleartext ... == false`.

One related subtlety: `EC.network_input_message_projection`'s cleartext arm had
to become a **disjunction** of the record-local rule and the buffered one, not a
replacement.  The record decoder is shared by both roles and can only ever prove
the record-local disjunct; it knows nothing about the connection's buffer.  The
empty-buffer `SMTPat` collapses the two everywhere the buffer is empty, so the
disjunction is free.

Likewise, the record-local ServerHello delivery in
`TLS13.Impl.Handle.Handshake` still gates on `can_receive && buffer_empty`, so
it declines to fire while a partial message is pending.
`CN.mark_received_server_hello` itself imposes no such gate -- which is exactly
what lets the reassembled path take the buffered reading without disturbing the
unbuffered one, and is why that module is untouched.

### Resource safety

The threat models of the two roles are not the same, and the cap is where that
is discharged.  The client's pre-existing *protected* buffering only accumulates
bytes that have already been AEAD-authenticated: only the genuine peer can grow
that buffer.  A server buffering a ClientHello is accumulating bytes from an
**unauthenticated** attacker before any key exists, so
`max_pending_cleartext_handshake` is load-bearing for resource safety and not
merely for a record-counting argument.  The implementation additionally caps the
coalesced stream at `Bounds.max_client_hello_len_sz` (8192) -- sound because it
is only ever a refusal to buffer, and below `parse_tls_message`'s
`max_record_fragment_len` precondition.

### How it is staged

Commits `B1`..`B15`, described stage by stage in `docs/server-p256-plan.md`.
The ordering was corrected once during the work and the correction is recorded:
the **concrete** pending buffer has to land before the step relation is
un-restricted, not after.  An earlier spec-only attempt
(`g3-route-b-spec-attempt`) is superseded by this series, which does the
representation work first and re-lands the spec mechanism on top of it.

Every intermediate commit verifies.  Several are deliberately capability-neutral
-- B11, for instance, buffers only onto an empty buffer, so a split hello is
still ultimately refused; the first record is absorbed and the second still
errors.  That is a green-at-every-step increment, not a bug.

---

## Merge of `agentic` (fstar2 simplified effect system)

The EverParse/F* bump is merged in and both gates re-established on top of it.

* `--split_queries` no longer exists, so the three occurrences this branch added
  since the fork are stripped.
* Five definitions needed the rlimit retuning the bump commit describes.  One is
  a real fix rather than headroom: the S6.8d ServerHello dispatch computes
  `63 + |share| + |session_id|` with `SZ.add`, and the `fits` obligation now
  needs its bounds stated explicitly rather than found by the solver.

### One build fix worth calling out

`generated/cache/*.checked` and `_cache/*.checked` are gitignored build products
that survive both `git pull` and a toolchain rebuild.  F* validates a cached
module against its source hash but **not** against the version of F* that wrote
it, and loading a `.checked` from a different build does not fail cleanly -- it
**segfaults the typechecker** inside `FStarC.Syntax.Subst`, with nothing in the
output implicating the cache.  Four modules crashed this way after the bump,
including ones this branch never touches.

`scripts/invalidate-stale-cache.sh` now records the F* version alongside the
caches and discards them when it changes.  The Makefile calls it at **parse
time**, not from a recipe: deleting the generated `.checked` files partway
through a build pulls rules out from under a dependency graph make has already
computed.

---

## Verification

* `make verify` — 0 errors (320 modules)
* `make check-admits` — **0 admits**
* `make test` — all suites pass: **35/35** server capability-matrix cells and
  **4/4** client framing-matrix cells match their ledgers, plus ATLAS↔ATLAS
  loopback, OpenSSL interop in both directions, and the Chromium demo

No theorem was weakened to land either gap.  The one proved property that G3
does restrict is the cross-endpoint pairing family
(`lemma_paired_replay_split_prefixes_equal_single_client_hello` and its two
companions), which now carries a `cleartext_handshake_buffer_empty` hypothesis
-- and `tls_system_inv` supplies it at every system-visible state.

## Docs

`docs/server-client-parity.md` now records G1–G5 as **all closed**: the header,
both ledger tables, the G2 and G3 sections and the P2/P2b harness prose.  §G3
additionally carries a retrospective recording where the pre-implementation
scoping was right (the concrete pending buffer had to come first; the
exhaustiveness fallout is mechanical; the pairing theorems need an empty-buffer
hypothesis) and where it was wrong (no buffer-aware `network_input_wf` was
needed, and no third decoder outcome either).

`docs/server-p256-plan.md` records every G2 stage and every G3 commit as landed,
with the design decisions and the two false starts written up at the point they
were made.
