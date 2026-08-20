# Close parity gap G2: secp256r1 key exchange on the verified TLS 1.3 server

Merges the `interop` branch into `agentic`.  The verified server now negotiates
**secp256r1 (P-256)** key exchange in addition to X25519, closing gap G2 from
`docs/server-client-parity.md`.  Three cells of the 34-cell server capability
matrix move from `refused` to `ok`.

## What this changes for a peer

Before, the server rejected any ClientHello that did not carry a well-formed
32-byte X25519 `key_share`.  It now also accepts one whose only `key_share` is a
well-formed 65-byte uncompressed secp256r1 point, runs the ECDH at whichever
group the acceptance gate picked, tags the ServerHello with that group, and
sizes the record accordingly.  The default `server_supported_groups` becomes
`[X25519; Secp256r1]`.

**X25519 still wins whenever both shares are well formed**, so no pre-existing
peer changes behaviour.

## Interop ledger

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

## How it is staged

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

## Merge of `agentic` (fstar2 simplified effect system)

The final commit merges the EverParse/F* bump and re-establishes both gates on
top of it.

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

## Verification

* `make verify` — 0 errors (320 modules)
* `make check-admits` — 0 admits
* `make test` — all suites pass: 34/34 capability-matrix cells match the ledger,
  ATLAS↔ATLAS loopback, OpenSSL interop in both directions, Chromium demo

## Docs

`docs/server-client-parity.md` records G2 as closed in the header, the capability
table, the G2 section and the ledger.  `docs/server-p256-plan.md` records every
stage as landed and adds a retrospective comparing the plan's estimate against
what the flip actually cost.
