# G2 implementation plan: secp256r1 key exchange on the verified server

Companion to `docs/server-client-parity.md`, which says *what* the gap is and
*why* it matters.  This file says *where* the edits go, in what order, and what
each step has to prove.  Line numbers are as of commit `c2e73aa7a`.

A line-level plan for **G3** (cross-record ClientHello reassembly) is in the
last section, because the two share a staging discipline and one of them will
be picked up first.

---

## Where to pick up (updated 2026-08-18, HEAD `c6fdefad6`)

**G2 is closed.**  The tree is **green**: `make verify` 0 errors,
`make check-admits` 0 admits, `make -j60 test` 34/34 matrix cells plus loopback
and OpenSSL interop.  Stages S1–S5, S6.1–S6.7, S6.7b/c/d, S6.8a, S6.8b,
S6.8c-1, S6.8c-2 and finally **S6.8d** have all landed; S6.8d is the one that
moved the ledger.

Nothing in this plan remains to be done.  What follows is kept as the record of
how it was staged, and because the **G3** plan in the last section reuses the
same discipline.

### S6.8c-2 as landed — the send path's share buffer is 65 bytes wide

The send path now carries its own share at the uniform 65-byte width the
representation and the peer-share path already used, so the only thing between
it and a P-256 ServerHello is the selection policy.

* `Send.fst`'s stack-local in
  `process_send_server_hello_with_derived_public_from_private_array` is
  `[| 0uy; 65sz |]`, filled by `KEX.kex_public_from_private_runtime` at the
  literal `CryptoSpec.KexX25519`.  S6.8d changes only that group argument.
* `process_send_server_hello_from_arrays` and `build_server_hello_from_arrays`
  take a 65-byte share, and every witness use is
  `CryptoSpec.unpad_share_65 'server_key_share_bytes 32`.  **The width is still
  the literal `32`** — the single token S6.8d turns into `kex_public_len g`.
  Mirrored in `Server.fsti` / `Server.fst`; no driver module moved, exactly as
  measured.
* `build_server_hello_from_arrays` stores the caller's buffer verbatim with
  `CR.copy_fixed65_array_to_vec`; the padding now happens one layer up.
  `CR.copy_padded32_array_to_vec65` is consequently unused — S6.8d can delete
  it, or leave it for a client-side caller.

Two supporting additions, both of which S6.8d inherits:

* **`CryptoSpec.padded_share_65 share len`** (`TLS13.Crypto.Spec.fsti:~228`) —
  "the 65-byte buffer is `pad_share_65` of its own `len`-byte prefix".  This is
  the precondition the send path carries, and at S6.8d `len` becomes
  `kex_public_len g` with nothing else moving.
* **`KEX.kex_public_from_private_runtime` gained an additive postcondition**: a
  caller handing in a *zeroed* buffer gets back exactly
  `pad_share_65 (kex_public_from_private g sk)`.  The X25519 arm needs it
  because it writes 32 bytes and leaves the tail as it found it; at P-256 the
  share fills the buffer and the padding is the identity.  No caller was
  affected — there were none.  The proof is
  `lemma_pad_share_65_from_zeroed_prefix_copy` in `TLS13.KEX.fst`.

**One Pulse gotcha worth carrying** (the first write-up of this got the rule
wrong; corrected here).  `introduce` is *not* rejected in a `#lang-pulse` file.
The only Pulse-specific rule is that **the whole `introduce ... with ...` must
be parenthesised**, so Pulse parses it as an F* ghost term rather than as a
Pulse statement.  Without the parens you get `Expected type
Pulse.Lib.Core.slprop but ... has type Prims.prop`.  All three connectives work:

```fstar
(introduce forall x. x >= x
 with ());
(introduce exists x. r x
 with 0 and (mk 0));
(introduce p ==> q          // p2q () : Lemma (requires p) (ensures q)
 with p2q ());
```

The `with h. e` form that the earlier note tripped over is not a Pulse
restriction at all: F* itself dropped it ("`introduce` and `eliminate` no longer
bind names for hypotheses; write `with e` instead of `with h. e`.  The
hypothesis is available in the proof context of `e`"), and it fails identically
in a plain `.fst`.  So `FStar.Classical.arrow_to_impl` is *not* required for
implications; the one use of it in `TLS13.KEX.fst` is a stylistic leftover.

### S6.8d as landed — the behavioural flip, one commit (`c6fdefad6`)

Measured surface: **78** `KexX25519` sites in `src/impl`, **32**
`is_valid_client_hello` sites, **12** `server_selection_group_pinned` sites to
delete, and ~24 state-keyed `95 + |sid|` statements.  §7's "S6.8c — the
remaining flip" lists all seven items at file and line.

**Why the state-keyed lengths must be here and not earlier:** the ~24
statements of `95 + Seq.length (CM.stored_client_hello_session_id 'st0)` are
keyed on the connection *state*, so their group is
`CM.stored_client_hello_kex_group 'st0` = `client_hello_kex_group_for m`, which
is provably `KexX25519` **only** from the acceptance gate's X25519 clause inside
`IM.is_valid_client_hello` — never from the pure part of a postcondition.
Generalising them changes what every caller must prove, so unlike the
selection-keyed arithmetic S6.8c-1 moved, they cannot be staged
capability-neutrally.  They travel with the gate.

**Budget one or two risk-R7 repairs.**  S6.8d grows `is_valid_client_hello` /
`client_hello_slot_exactly`, which is exactly the shape that broke *distant,
unrelated* queries twice during S2.  Do **not** reach for `--z3rlimit` or
`--z3seed`; name the failing projection as a lemma, or discharge it in explicit
`assert (pure ...)` steps before the call that needs it.  See §8, R7.

#### What it actually took

The predictions above held, with four things the plan had not foreseen.

* **The group pin had to stay a *pure policy* pin.**  The first two attempts
  gave `server_selection_presence_exactly` more arguments — first the whole
  handshake state, then the two projections `hs_server_selection` and
  `hs_client_hello`.  Both fail, because Pulse's `rewrite A as B` needs `A` and
  `B` provably equal, so a predicate that must survive a state transition may
  only mention things the transition does not change.  The second attempt broke
  the *client* role: `sent_client_hello_state` rewrites `hs_client_hello` while
  the selection is `None`, and `rewrite` cannot exploit that.  The design that
  works is `server_selection_group_pinned (sel:option server_handshake_selection)`
  — one argument, phrased over `sel.server_selected_client_hello`, with the
  link `hs_client_hello == Some sel.server_selected_client_hello` supplied
  separately by the reachability lemmas in `TLS13.ConnectionState.Lemmas`.

* **Two spec-level predicates had to be strengthened**, both for free:
  `CS.server_selection_key_share_consistent` now states that the X25519 and
  P-256 privates are the *same* 32 bytes (which is what the server does — one
  scalar per handshake), and
  `lemma_connection_state_consistent_server_pre_server_hello_shape` now also
  yields `hs_client_hello == Some selection.server_selected_client_hello`.

* **The driver-level correctness properties were X25519-specific too**, and the
  plan's site census had missed them because they live in `.fsti` files two
  layers above the ECDH: `BN.local_event_success_correct` and
  `BH.derive_shared_secret_from_payload_correct` both said `x25519_shared` /
  `CS.client_hello_key_share`.  They are now stated with `kex_shared` at
  `client_hello_kex_group_for`.

* **Pulse does not carry `SZ.add`'s `Pure` postcondition out of an `if`
  condition**, and not reliably out of a plain `let` either.  The
  LocalSendServerHello dispatch in `Server.fst` needed the sum let-bound and
  then stepped through `assert (pure (SZ.v 63sz == 63))` and
  `assert (pure (SZ.v total == 63 + SZ.v a + SZ.v b))` before the semantic form.

R7 materialised exactly once, in `Network.fst`'s store path, and was repaired by
restating the assert as the two-armed disjunction — not by rlimit or seed, as
the rule above demands.  R9 materialised as a `padded_share_65 … 32` left
behind in an `.fsti`, which surfaced as a 200-line "Could not prove subtyping of
fn …" in which the *only* difference between the two printed types was that one
constant.

#### The interop ledger, and one trap in it

Three cells flip to `OK`: `p256-only`, `p256-first-x25519-listed` and
`ecdsa-credential-p256-only`.  `p256-first-x25519-listed` **does** flip — the
open question of whether it would is settled.  OpenSSL, given
`P-256:X25519`, sends its key_share for P-256 only and merely *lists* X25519 in
`supported_groups`, and the acceptance gate follows the share that was actually
sent.  (`x25519-and-p256` still lands on X25519, because there OpenSSL sends
both shares and the gate prefers X25519.)

The trap: `expect_group` is compared against `OBJ_nid2sn(SSL_get_negotiated_group(…))`,
whose short name for P-256 is **`prime256v1`**, not `P-256`.  `P-256` is only
accepted on the `SSL_CTX_set1_groups_list` *input* side, so a row can perfectly
well configure `"P-256"` and still have to expect `"prime256v1"`.  Getting this
wrong produces the maximally confusing diagnostic
`negotiated group prime256v1, expected P-256` immediately followed by
`expected the server to accept this offer but it refused it` — the handshake had
in fact succeeded at P-256, and only the post-handshake parameter check failed.

### Working rules that have paid off every stage

* Verify `.fsti` **first**, then `.fst` — never together.  A `.fst` does not
  inherit its `.fsti`'s module abbreviations.
* Iterate with `make -j8 _cache/<M>.fst.checked` (2–10 min), not a full verify
  (25–35 min).  **`rm -rf _cache_quick` before any real `make verify`.**
* Grep verify output for `^\* Error`.  `make -k` skips a failed module's
  dependents, so an error count is a lower bound.  ~40 "Interface … admitted
  without an implementation" warnings are normal.
* For mechanical multi-file edits, assert an exact occurrence count on every
  replacement (risk R10).
* Rollback is always `git checkout -- src/`.

### Related artifacts kept outside this branch

The **G3** Route B spec attempt is archived on the branch
`g3-route-b-spec-attempt` (24 files, +529/-20).  It does not verify green and is
deliberately unmerged; its commit message carries the full fallout enumeration,
and `docs/server-client-parity.md`'s G3 entry explains why step (1) of the route
-- a concrete reassembly buffer in the server representation -- must come first.
Recover it with `git diff interop...g3-route-b-spec-attempt`.

---

## 0. What does not change

This is the single most important input to the estimate, and it is the reason
the raw occurrence counts (166 / 78 / 41) overstate the work.  Everything below
is **already group-agile, already proved, and already exercised end to end by
the client**, which offers and completes P-256 today:

| layer | symbol | file:line |
| --- | --- | --- |
| crypto spec | `kex_group`, `kex_public_len`, `kex_public g` | `src/spec/assumptions/TLS13.Crypto.Spec.fsti:182,186,192` |
| crypto spec | `kex_public_from_private g`, `kex_shared g` | `TLS13.Crypto.Spec.fsti:195,200` |
| crypto spec | `pad_share_65` / `unpad_share_65` + injectivity | `TLS13.Crypto.Spec.fsti:214,218,226` |
| crypto spec | `lemma_kex_shared_agreement g` | `TLS13.Crypto.Spec.fsti:233` |
| binding | `p256_public_from_private` | `src/impl/extern/TLS13.Crypto.fsti:186` |
| runtime ECDH | `kex_shared_runtime g sk pk65 out` | `src/impl/TLS13.KEX.fsti` |
| model accessor | `kex_group_of_named_group` | `src/spec/core/TLS13.Spec.StateMachine.fst:278` |
| model accessor | `server_hello_kex`, `client_hello_kex` | `TLS13.Spec.StateMachine.fst:296,337` |
| model accessor | `client_hello_p256_key_share` | `TLS13.Spec.StateMachine.fst:264` |
| model accessor | `start_kex_private` / `start_kex_public` | `TLS13.Spec.StateMachine.fst:326,331` |
| semantics | `kse_list_find_secp256r1`, `clientHello_key_share_secp256r1` | `src/spec/core/TLS13.Wire.Semantics.fst:139,156` |
| semantics | `serverHello_kex_share` + shape lemmas | `TLS13.Wire.Semantics.fst:301,322,353` |
| impl mirror | `IM.server_hello` is *already* 65-byte padded with a `server_hello_kex_group` tag | `src/impl/TLS13.Impl.Messages.fst:99-105` |

**No new cryptography, no new binding, no new spec-level KEX vocabulary.**

## 1. Design decisions

### D1 — additive two-field selection, not a dependent pair

`server_handshake_selection` (`TLS13.Spec.StateMachine.fst:184`) gets **two new
fields** rather than having its existing two re-typed:

```fstar
  server_key_share_private: option C.x25519_private;   (* unchanged *)
  server_key_share_public: C.x25519_public;            (* unchanged *)
  server_p256_private: option C.kex_private;           (* NEW *)
  server_p256_public: C.kex_public C.KexP256;          (* NEW *)
```

This is exactly what `handshake_start` already does for the client
(`start_client_key_share_private/public` + `start_client_p256_private/public`,
`TLS13.Spec.StateMachine.fst:101-103`).  The payoff is large: **the ~150
existing `server_key_share_private` / `server_key_share_public` occurrences keep
their current meaning and their current proofs**, and only the sites that need
the negotiated group change.  A dependent field
`server_key_share_public: C.kex_public (kex_group_of_named_group
selection.server_selected_group)` would be prettier and would force every one of
those 150 sites through a re-proof.

The server then gets the accessors that mirror `start_kex_private/public`, to be
added immediately after `server_selection_key_share_consistent`
(`TLS13.Spec.StateMachine.fst:194`):

```fstar
let server_kex_private (sel:server_handshake_selection) (g:C.kex_group)
  : option C.kex_private
  = match g with
    | C.KexX25519 -> sel.server_key_share_private
    | C.KexP256   -> sel.server_p256_private

let server_kex_public (sel:server_handshake_selection) (g:C.kex_group)
  : C.kex_public g
  = match g with
    | C.KexX25519 -> sel.server_key_share_public
    | C.KexP256   -> sel.server_p256_public

let server_selected_kex_group (sel:server_handshake_selection) : C.kex_group
  = kex_group_of_named_group sel.server_selected_group
```

**Cost accepted:** the server generates *both* keypairs on every connection and
throws one away, as the client already does.  Generating only the selected one
would need the selection to precede keygen, which would make the selection
record dependently typed — precisely what D1 avoids.  One wasted P-256 scalar
multiplication per handshake is the price of keeping ~150 proofs intact.

### D2 — two ClientHello key-share slots, not one widened slot

`IM.client_hello` (`src/impl/TLS13.Impl.Messages.fst:75`) gets a second vector
beside the existing 32-byte `client_hello_key_share:85`:

```fstar
  client_hello_key_share: V.vec U8.t;        (* 32 bytes, X25519, unchanged *)
  client_hello_p256_key_share: V.vec U8.t;   (* NEW: 65 bytes, padded *)
  client_hello_has_x25519: bool;             (* NEW *)
  client_hello_has_p256: bool;               (* NEW *)
```

Same rationale as D1: every existing `is_valid_client_hello` clause about the
32-byte slot survives verbatim; the *acceptance* widening is the two new
booleans.  Widening the one slot to 65 bytes instead would re-prove every
`Seq.equal key_share k` obligation in the tree.

### D3 — `ch_extensions` carries two share options

`TLS13.Wire.Spec.ch_extensions` (`src/spec/core/TLS13.Wire.Spec.fst:269`)
currently threads `key_share:option (B.bytes_of_len 32)`.  It becomes two
accumulators:

```fstar
  (ks_x25519:option (B.bytes_of_len 32))
  (ks_p256:option (B.bytes_of_len 65))
```

and `clientHello_representable` (`TLS13.Wire.Spec.fst:472`) changes its gate
from `Some (server_name, Some key_share, _, sig_schemes)` to
`Some (server_name, ks_x, ks_p, _, sig_schemes)` with `(Some? ks_x || Some? ks_p)`.
**This one disjunct is the whole capability widening.**  Everything else in this
document exists to make it provable and usable.

### D4 — server ECDH goes through `TLS13.KEX`, driven by a stored group tag

Not by a share length, and not by a fresh parse.  This is the invariant the
whole codebase already keeps for the client (`TLS13.KEX.fsti` header comment)
and it must not be broken here.

### D5 — staging: every commit is green, and only the last one flips a cell

Six stages (S1..S6).  S1..S5 are capability-neutral by construction — the
server's configured `server_supported_groups` stays `[T.X25519]`
(`src/impl/TLS13.Impl.ConnectionState.Repr.fsti:1390`), so no P-256 handshake is
reachable and the matrix ledger cannot move.  **S6 is a one-line config change**
plus the ledger flip.  If the work has to be abandoned partway, the tree is
green and no theorem has been weakened — the failure mode that forced the G3
revert.

Each stage ends with: `make -k -j60 verify` (0 errors), `make check-admits`
(0 admits), `make -j60 test` (34/34 cells, unchanged until S6).

---

## 2. Stage S1 — spec: agile server selection (no capability)

**Goal:** `server_handshake_selection` can *describe* a P-256 server.  Nothing
yet produces a P-256 selection.

> **Landed, with one scope change.**  The stage as written also rewrote the
> server's `LocalDeriveSharedSecret` arm of `legal_event` into the
> group-dispatched form.  That was tried, measured, and pulled back out; see
> "S1 as landed" below.

#### S1 as landed

Rewriting the derive arm to
`match server_kex_private selection (server_selected_kex_group selection)` cost
**7 errors in 5 files** -- `Impl.Server.Send`, `ConnectionState.Lemmas` (x3),
`Impl.ConnectionState.LocalHandshake`, `Impl.Server.Driver.BufferedNetwork`,
`Impl.Driver.Pairing` -- and all 7 have the same root cause, which the plan had
not anticipated:

> Both directions of those proofs need *"the selected group is X25519"*, and
> nothing in the **spec** can supply it.  `server_selection_acceptable` gives
> `named_group_offered cfg.server_supported_groups selection.server_selected_group`,
> but `cfg.server_supported_groups` is an arbitrary list at the spec level -- it
> is only `[T.X25519]` in the *implementation's* config
> (`Impl.ConnectionState.Repr.fsti:1390`).  So the fact is true of every
> reachable state today but is not stated by any invariant.

The invariant that would state it is the `server_x25519_*_projection` family
(`Spec.StateMachine.Correspondence.fst:310,334,373`), and generalising it to
`server_kex_public` drags in every consumer that reads the ServerHello's
32-byte share -- `Impl.Server.Send`, `Impl.Driver.Pairing`,
`ConnectionState.ServerHelloSelectionLink`.  That is the same body of work as
S5, so **the derive-arm rewrite moves out of S1 and into a combined S4/S5**,
and a comment at the arm records why.

What S1 did land, all green:

| file | change |
| --- | --- |
| `Spec.StateMachine.fst` | `server_p256_private : option C.p256_private` and `server_p256_public : C.p256_public` added to `server_handshake_selection` |
| `Spec.StateMachine.fst` | `server_selection_key_share_consistent` becomes a two-clause conjunction, one clause per group |
| `Spec.StateMachine.fst` | `server_p256_absent : C.p256_public` -- the stand-in public value used wherever no P-256 keypair was generated |
| `Spec.StateMachine.fst` | `server_kex_private`, `server_kex_public`, `server_selected_kex_group`, `lemma_server_kex_x25519_is_legacy` (with `SMTPat`), `lemma_server_kex_public_from_private` |
| 10 impl files, 39 literals | `server_p256_private = None; server_p256_public = server_p256_absent` |
| `ConnectionState.Lemmas.fst:1301` | `server_selected_client_hello_reachable_shape` now says `server_selection_key_share_consistent selection` rather than inlining only the X25519 clause |
| `Correspondence.fst:310,334` | both server projections gain `server_selection_key_share_consistent selection` as a conjunct |
| `Impl.Server.Send.fst(i)` | `lemma_input_ready_server_hello_of_selection` takes the full consistency as a hypothesis -- `material` carries only the X25519 pair, so the P-256 clause cannot be reconstructed from it |

The last three rows are the interesting ones: the *only* real content of S1 is
that "the selection agrees with itself about its keypairs" is now a
group-indexed statement, and every invariant that carried the X25519 reading of
it now carries the group-indexed one.  That is exactly the hook S4/S5 need.

### S1.1 `src/spec/core/TLS13.Spec.StateMachine.fst`

| line | edit |
| --- | --- |
| `184-193` | add `server_p256_private: option C.kex_private;` and `server_p256_public: C.kex_public C.KexP256;` to `server_handshake_selection` |
| `194-198` | extend `server_selection_key_share_consistent` with the P-256 conjunct: `(match sel.server_p256_private with \| Some sk -> C.kex_public_from_private C.KexP256 sk == sel.server_p256_public \| None -> True)` |
| after `198` | add `server_kex_private`, `server_kex_public`, `server_selected_kex_group` (D1), and `lemma_server_kex_public_from_private` mirroring `lemma_start_kex_public_from_private` (`TLS13.Spec.StateMachine.fst:1433`, used at `LocalHandshake.fst:4966`) |
| `1466-1477` | `server_hello_matches_selection`: replace the `Sem.serverHello_key_share_x25519` clause with one on `Sem.serverHello_kex_share sh`, requiring the named group to be `sel.server_selected_group` and the share to equal `server_kex_public sel (server_selected_kex_group sel)`.  `lemma_serverHello_kex_share_x25519` (`Wire.Semantics.fst:353`) is the bridge that keeps the X25519 instance provable from the old form |
| `1626-1640` | rewrite the server's `LocalDeriveSharedSecret` arm in the shape of the *client's* arm at `1607-1625`: dispatch on `server_selected_kex_group selection`, take `server_kex_private selection g`, read the peer share with `client_hello_kex selection.server_selected_client_hello g` (already exists, `:337`), and conclude `C.kex_shared g sk k == Some shared` |
| `1387-1410` | `server_selection_acceptable`: no change needed — `named_group_offered cfg.server_supported_groups selection.server_selected_group` (`:1398`) already does the gating, and the config still lists only X25519 until S6 |

**Provability note for `1626`:** the X25519 instance must still reduce to the
old statement, or every downstream server proof breaks.  It does:
`server_kex_private sel KexX25519 == sel.server_key_share_private` and
`C.kex_shared KexX25519 == C.x25519_shared` are both definitional.  Add an
`SMTPat`-carrying `lemma_server_kex_x25519_is_legacy` next to the accessors if
Z3 does not unfold them at the ~40 downstream sites.

### S1.2 Record-literal fallout — 42 sites, all mechanical

`grep -rn "server_selected_client_hello *=" src/` lists them.  Every one gains
`CS.server_p256_private = None; CS.server_p256_public = <65 zero bytes>;`.
Concentrations: `TLS13.Impl.Server.Setup.fst` (`:477,505,533,587,618,647,702`),
`TLS13.Impl.ConnectionState.LocalHandshake.fst`,
`TLS13.Impl.Server.Driver.BufferedHandshake.fst`,
`TLS13.Impl.ConnectionState.Queries.fst(i)`, `TLS13.Impl.Server.fst(i)`,
`TLS13.Impl.Server.Types.fst`,
`src/spec/properties/TLS13.Spec.StateMachine.Correspondence.fst`.

> **Expected pain point.** `server_selection_key_share_consistent` is quoted
> inside `ConnectionState.Lemmas.fst` (10 sites), `ServerHelloSelectionLink.fst`,
> `HandshakeAgreementNonReady.fst` and `ServerCanonicalShape.fst`.  The new
> conjunct is `True` whenever `server_p256_private = None`, so these should hold
> by `norm`, but budget one iteration for each to need an explicit
> `assert (pure ...)`.

### S1.3 `src/impl/TLS13.Impl.ConnectionState.Model.fsti`

`server_hello_of_selection:597` reads `sel.CS.server_key_share_public` for the
ServerHello's `ks`.  Change to `server_kex_public sel (server_selected_kex_group sel)`.
Add `server_selected_kex_group_policy (st:CS.connection_state) : C.kex_group`
next to `server_selected_suite:559`, in the same shape (a function of the stored
ClientHello alone, so the send path can recover it at run time — this is the G1
lesson and it is what stops a group parameter having to be threaded through the
driver).  Prefer X25519 when offered, else P-256:

```fstar
let server_selected_kex_group_policy (st:CS.connection_state) : C.kex_group
  = match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
    | Some ch -> if Some? (CS.client_hello_kex ch C.KexX25519)
                 then C.KexX25519 else C.KexP256
    | None -> C.KexX25519
```

**Gate S1.** No behaviour change; 34/34 cells unchanged.

---

## 3. Stage S2 — parser: accept a P-256 ClientHello (no capability)

> **RESCOPED — see "S2 as landed" at the end of this section (commit
> `76c48ed62`).**  S2.1 (the `Wire.Spec.fst` acceptance gate) and the
> acceptance half of S2.2 were measured to be too expensive for the capability
> they buy at this stage and were **moved to S6**.  What actually landed is
> S2.3 + S2.4 only: storage plumbing.  The subsections below are kept as the
> record of the original design; read them together with the landing note.

**Goal:** a P-256-only ClientHello *parses* and lands in the mirror.  The server
still refuses it later, because its configured groups are X25519-only.

### S2.1 `src/spec/core/TLS13.Wire.Spec.fst`

| line | edit |
| --- | --- |
| `236-249` | add `ch_find_key_share_p256` beside `ch_find_key_share`, returning `option (B.bytes_of_len 65)` via a new `key_exchange_to_key65` (mirror `key_exchange_to_key32` at `:234`) |
| `269-308` | `ch_extensions`: split `key_share` into `ks_x25519` / `ks_p256` per D3; in the `Extension_data_key_share` arm (`:295-303`) scan for *both* groups.  Keep the commit-on-first discipline: the arm is entered only when both accumulators are `None` |
| `472-482` | `clientHello_representable`: gate on `Some? ks_x25519 \|\| Some? ks_p256` |
| `484-487` | `lemma_clientHello_representable_scan` — definitional, should still be `()` |
| `493-497` | `lemma_ch_extensions_connect`: add a `lemma_connect_ks_p256` companion to `lemma_connect_ks` tying `ks_p256` to `Sem.clientHello_key_share_secp256r1` (`Wire.Semantics.fst:156`) |

Also update the `.fsti` declarations for each of the above.

> **Expected pain point — the sharpest in S2.** `Sem.kse_list_find_x25519`
> (`Wire.Semantics.fst:113`) *stops* at the first X25519 entry, while
> `Wire.Spec.ch_find_key_share:240` *continues* past a bad-length one.  The two
> are reconciled today by `lemma_ch_extensions_connect`.  Adding a second group
> doubles the case analysis in that reconciliation.  Do the P-256 finder in the
> `Sem` "stop at first entry of this group" style so the two proofs are
> symmetric rather than subtly different.

### S2.2 `src/impl/TLS13.Impl.Parser.fst`

| line | edit |
| --- | --- |
| `3729-3775` | `probe_copy_x25519_key` — keep as is, still needed for the X25519 slot |
| after `3775` | add `probe_copy_p256_key`, same shape, `V.length key_vec == 65`, testing `GNG.Secp256r1?` and length 65.  **Template: `try_copy_kex_share:3632`**, which already does the group-tagged padded copy for the ServerHello side |
| `4287-4442` | `scan_ch_key_share`: take *two* vectors (32-byte and 65-byte) and return `(found_x25519, found_p256)`.  The loop must not stop at the first X25519 entry any more — it must run to the end of the entry list, or stop once both are found |
| `4443+` | `scan_ch_extensions`: thread the second vector and the second flag; the accept condition becomes `found_x25519 || found_p256` |
| `769-776` | `lemma_ch_extensions_cons_ks`: the `Sem.kse_list_find_x25519` case analysis gains its P-256 twin |

### S2.3 `src/impl/TLS13.Impl.Messages.fst`

| line | edit |
| --- | --- |
| `75-90` | `client_hello`: add `client_hello_p256_key_share`, `client_hello_has_x25519`, `client_hello_has_p256` (D2) |
| `493-545` | `is_valid_client_hello`: add `V.pts_to l.client_hello_p256_key_share p256_key_share` and the length/fullness clauses (`== 65`); **change the key-share clause at `531-533`** from an unconditional `match Sem.clientHello_key_share_x25519 m with ... \| None -> False` to a pair of flag-guarded clauses, with `client_hello_has_x25519 <==> Some? (Sem.clientHello_key_share_x25519 m)` and the P-256 twin, plus `pure (l.client_hello_has_x25519 \/ l.client_hello_has_p256)` |
| `719` | free the new vector |

### S2.4 `src/impl/TLS13.Impl.ConnectionState.Repr.fsti` / `.fst`

| line | edit |
| --- | --- |
| `.fsti:890-925` | `client_hello_slot_exactly`: add the 65-byte slot clauses beside `:900,906,912` |
| `.fst:1563` | allocate `V.alloc 0uy 65sz` for the new slot (compare the client's own pair at `:1494,1496`) |
| `.fst` free path | free it |

**Gate S2.** A P-256-only ClientHello now parses; the server still refuses it at
`server_selection_acceptable` because `server_supported_groups = [T.X25519]`.
34/34 cells unchanged — **`p256-only` must still be `refused`**, and the matrix
proves it.

### S2 as landed (commit `76c48ed62`)

**Measurement that forced the rescope.** `ch_extensions` has **169**
occurrences (62 in `TLS13.Impl.Parser.fst`, 51 in
`TLS13.Wire.Spec.Reveal.Handshake.fst(i)`).  Changing its arity — the whole of
S2.1 and the acceptance half of S2.2 — touches every one of them and buys *no*
capability while `server_supported_groups = [T.X25519]`, because the request is
refused one layer up regardless.  S2 was therefore reduced to pure storage
plumbing and **the acceptance gate moved wholesale into S6**, where it is paid
for by an actual matrix-cell flip.

**Additive slot, not a widened one.** `client_hello_key_share` has 72
occurrences in 25 files but only **3 real construction sites**
(`Repr.fst:1563`, `Serializer.fst:~2063`, `Parser.fst:~6133`).  Rather than
widen it to a group-tagged 65-byte slot, S2 added a *separate*
`client_hello_p256_key_share : V.vec U8.t` (65 bytes) plus
`client_hello_has_p256_key_share : bool`, so all 72 existing occurrences keep
meaning exactly what they meant.  `is_valid_client_hello` got the matching
existential, `pts_to`, shape facts, and a one-directional meaning clause tying
the flag to `Sem.clientHello_key_share_secp256r1`.

**Finding — the flag cannot live in `client_hello_slot_exactly`.**  The slot
invariant describes an `IM.client_hello` struct that is **allocated once** and
thereafter mutated only through its vectors; its *scalar* fields cannot be
rewritten.  Constraining `client_hello_has_p256_key_share` there is therefore
unprovable.  This is precisely why the codebase already keeps the session-id
width in a separate metadata **`Box`** rather than in the struct (see the
comment at `ConnectionState.Network.fst` ~`:914`).  The slot invariant
consequently carries **ownership and shape only**; the meaning stays in
`is_valid_client_hello`, whose structs the parser builds fresh.

> **Consequence for S4/S6.**  Before anything actually *fills* the P-256 slot,
> `client_hello_has_p256_key_share` must be lifted out of the struct into a
> metadata `Box` beside the session-id width.  Budget this as the first task of
> S6.  A comment at `Repr.fsti`'s `client_hello_slot_exactly` records it.

**`Serializer.fst` needs a scratch vector.**  `l_poc` shares `l`'s vectors, but
`l`'s caller owns no secp256r1 slot — the *client's own* P-256 share travels
separately as `start_p256_key_share`.  `l_poc` therefore gets a scratch 65-byte
vector, allocated before the record and freed immediately after the
`is_valid_client_hello` unfold.

**Two distant proofs destabilised.**  Growing a slprop this widely used
enlarges the SMT context of every proof that mentions it:

| site | symptom | repair |
| --- | --- | --- |
| `Client.ChannelImplementation.lemma_network_response_app_out_length:409` | already at `--split_queries always --z3rlimit 50`, started failing | new named projection lemma `Client.Types.lemma_legal_response_for_event_wf`.  An intermediate `assert` alone only moved the error one line down — that is what identified the *projection*, not the witness, as the cost |
| `Impl.Server.process_local_event:2910` (`LocalSendServerHello` arm) | the call's precondition (a bundle of `server_end_to_end_invariant`, the `95 + |sid|` length equation and `can_send_server_hello`) no longer discharged | discharge `process_local_event`'s guarded `LocalSendServerHello` hypothesis in **two named `assert (pure ...)`s before the call**, instead of letting Z3 instantiate the implication inside the call's VC |

Neither repair is an rlimit or `z3seed` bump.  Both are instances of the same
rule: when context growth breaks a distant proof, *name the projection*.

**Gates as landed.** `make verify` 0 errors, `make check-admits` 0 admits,
`make test` 34/34 cells matching the ledger — no cell moved, S2 being
capability-neutral by construction.

---

## 4. Stage S3 — server generates a P-256 keypair (no capability)

**Goal:** `server_p256_private/public` are populated with real key material.

### S3.1 `src/impl/TLS13.Impl.ConnectionState.LocalHandshake.fst`

`try_start_handshake:63` is the template, specifically its client P-256 block at
`:139-161`:

```
139:    let mut p256_private_key = [| 0uy; 32sz |];
140:    let p256_private_ok = Crypto.random_bytes p256_private_key 32sz;
160:    let mut p256_public_key = [| 0uy; 65sz |];
161:    Crypto.p256_public_from_private p256_private_key p256_public_key;
```

Copy this into the server's parameter-selection path.

### S3.2 `src/impl/TLS13.Impl.Server.Setup.fst`

Three parallel variants exist and all three carry the selection literal and its
32-byte preconditions:

| variant | signature lines | selection literal |
| --- | --- | --- |
| no-private | `461-467` | `477-487`, `505-515`, `533-543` |
| with-private | `570-576` | `587-597`, `618-628`, `647-657` |
| from-array | `686-692`, `725-731` | `702-712` |

Each gains a 65-byte `server_p256_key_share` array parameter and its
`B.length ... == 65` precondition, and each literal gains the two D1 fields.
The keygen call itself sits beside `Crypto.x25519_public_from_private` at
`LocalHandshake.fst:154` / `Setup.fst:710`.

`CS.server_selected_group = T.X25519` at `:477,505,533,587,618,647,702` stays
X25519 for now — S5 makes it a function of the ClientHello.

**Gate S3.** Still no P-256 handshake reachable.

### S3 as landed (commit `b97d28f3b`)

**One finding collapsed the whole stage.**  `C.x25519_private` and
`C.p256_private` are *both* `B.bytes_of_len 32`.  A server transmits exactly one
key share and runs exactly one ECDH — the one named by `server_selected_group` —
so a single 32-byte secret derives both publics, with no cross-group exposure
and no way for the peer to observe the unused one.

So the plan above over-built.  There is no second random, no extra 65-byte array
parameter, and no change to the driver's payload width: the existing
`LocalPayloadServerPrivateKey` / `LocalPayloadServerRandomAndPrivateKey` carriers
already deliver everything both groups need.  `Setup.fst`'s selection literals
gained `server_p256_private = Some <the same bytes>` and
`server_p256_public = CryptoSpec.p256_public_from_private <the same bytes>`,
which is exactly the shape `server_selection_key_share_consistent` wants.

S3 verified with **zero** proof repair — the only stage so far that did.

---

## 5. Stage S4 — server ECDH through `TLS13.KEX` (no capability)

**Goal:** the server computes its shared secret agilely.  With
`server_selected_group` still pinned to X25519 the runtime path is unchanged,
but it is now *stated* over `kex_shared`.

### S4.1 `src/impl/TLS13.Impl.ConnectionState.LocalHandshake.fst`

`try_derive_server_shared_secret_from_private_array:5136` is rewritten against
the client's `try_derive_shared_secret:4801`, whose relevant lines are:

```
4910:  let kex_group = !c.handshake.server_key_share.group;
4934:  load_kex_private ... kex_group kex_sk;
4952:  KEX.kex_shared_runtime kex_group kex_sk (V.vec_to_array ...) shared_out;
4966:  CS.lemma_start_kex_public_from_private start_spec kex_group;
```

Server-side edits:

| line | edit |
| --- | --- |
| `5155-5162` | postcondition restated over `CS.server_kex_private` / `C.kex_shared g` |
| `5202-5209` | the peer share is read from the *group-selected* slot, not unconditionally from `Sem.clientHello_key_share_x25519`; the ghost side becomes `CS.client_hello_kex ch g` |
| `5231-5236` | `Crypto.x25519_shared_runtime` → `KEX.kex_shared_runtime g ...`, with `KEX.lemma_kex_shared_call_success` replacing the x25519 one |
| new | a `load_server_kex_private` helper mirroring `load_kex_private:4735` |

The peer share must be handed to `kex_shared_runtime` as a **65-byte padded
buffer** (its precondition), so the X25519 path pads its 32-byte slot with
`pad_share_65` — this is what makes D2's two-slot mirror pay off: the 65-byte
slot is already the right shape and the 32-byte one needs a copy-and-pad.

### S4.2 `src/impl/TLS13.Impl.Server.Keys.fst` / `.fsti`

`.fsti:26,91,118` and `.fst:49,220,247` name `x25519_shared_secret` and
`x25519_shared` in the derive obligation.  `kex_shared_secret == x25519_shared_secret`
(`TLS13.Crypto.Spec.fsti:193`) so the *type* needs no change; the `x25519_shared`
applications become `kex_shared g`.

**Gate S4.** Runtime behaviour identical (g is always `KexX25519`).

---

## 6. Stage S5 — ServerHello writes the negotiated group (no capability)

**Goal:** the ServerHello writer is group-parametric.  Still only ever called
with X25519 until S6.

### S5.1 `src/impl/TLS13.Impl.Server.Send.fst`

| line | edit |
| --- | --- |
| `182-203` | `mk_server_hello_witness`: `GKE.group = GNG.X25519` (`:202`) and `GNG.namedGroup_bytesize_eq GNG.X25519` (`:203`) become parametric in the selected `namedGroup`; the 32-byte clamp at `:199` becomes a `kex_public_len`-byte clamp |
| `256-277` | `lemma_mk_server_hello_witness_bytesize`: `90 + \|session_id\|` (`:269`) becomes `90 + (kex_public_len g - 32) + \|session_id\|`; `:276` parametric |
| `335,358,494,524,533` | the `90` / `122` comments, bounds and obligations follow.  `122 -> 155`; `155 <= Bounds.max_transcript_len (65535)` still holds trivially |
| `601,643,1066,1400,1499` | `95 + \|sid\|` → `95 + (kex_public_len g - 32) + \|sid\|`.  The output buffer is *already* runtime-sized, so this is arithmetic, not restructuring |
| `1311-1360` | `build_server_hello_from_arrays`: the 65-byte `key_share_vec` at `:1347` is already right; replace the hard-coded `IM.server_hello_kex_group = CryptoSpec.KexX25519` at `:1356` with the recovered group, and widen the `server_key_share` input precondition from 32 to 65 bytes |
| `1545` | `let mut server_key_share = [\| 0uy; 32sz \|]` → `65sz` |

The group is recovered at run time from the stored ClientHello mirror via
`server_selected_kex_group_policy` (S1.3), exactly as `read_negotiated_server_suite`
(`TLS13.Impl.ConnectionState.Queries.fsti:1212`) recovers the suite for G1 — **no group parameter is threaded through the driver.**

### S5.2 `src/impl/TLS13.Impl.Serializer.Handshake.fst`

`GNG.X25519` is baked into the ServerHello key-share serializer at
`:453,467,470,481,483,486,520,525,760,762,764,855,858,863,866`.  These are the
`repack_kse` / `intro_vmatch_extSH_key_share` chain; each needs the group as a
parameter and `namedGroup_bytesize_eq` applied to it.  Note `:1432-1438` already
handles *both* groups for the `supported_groups` list, so the bytesize lemmas for
`Secp256r1` are already in use in this file.

> **Expected pain point — the largest single one in G2.** This serializer chain
> is `assert`-dense low-level EverParse plumbing.  Budget the most time here, and
> consider doing it as two sub-commits: first make every lemma take the group and
> instantiate it at `GNG.X25519` (green, no behaviour change), then let the
> caller pass the real group.

**Gate S5.** Still 34/34.

### S4/S5 as landed (commit `c02ab1b13`) — rescoped

> **S4 and S5 are one commit, and they are a specification change.**

**Why they cannot be separated.**  `server_x25519_key_share_projection` is
*derived from* `connection_state_consistent`, which is derived from
`legal_event`.  The moment `legal_event`'s server `LocalDeriveSharedSecret` arm
mentions a group variable, the only projection still derivable is the
group-indexed one, and every consumer has to move with it in the same commit.
This is risk R6 coming due.

**Why the implementation stays at X25519.**  Making the ServerHello *writer*
group-parametric means making its length arithmetic parametric (`90 + |sid|` →
`58 + |ks| + |sid|`, `95 + |sid|` → `63 + |ks| + |sid|`), which touches ~40
numeric sites plus the assert-dense EverParse chain in
`Impl.Serializer.Handshake.fst:453-880`.  While every selection literal still
says `T.X25519` that buys **no capability**, so it is deferred to S6, where it
is paid for by the acceptance-gate widening and the ledger flip.

So the rescope is: **S4/S5 = the specification becomes fully group-parametric;
the implementation says "X25519" out loud in named places.**

**Where the group comes from.**  At the spec level `server_supported_groups` is
an arbitrary list, so no configuration fact fixes the choice (the S1 finding).
Two answers, both already used by the client:

| situation | source of the group |
| --- | --- |
| a ServerHello exists | the *message*: `server_hello_kex sh` |
| before the ServerHello | the selection: `server_selected_kex_group selection` |
| inside the implementation | **nowhere** — see below |

**The runtime stores no group tag.**  `connection_state` keeps thirty-two
private bytes and a presence flag, nothing else, so no implementation-side proof
can learn its own selection's group from the representation.  It has to be
*asserted* by it.  Hence **`CR.server_selection_group_pinned`** in
`TLS13.Impl.ConnectionState.Repr.fsti`, a single named predicate carried as a
`pure` conjunct of `server_selection_presence_exactly` and surfaced through the
query postconditions.  Deleting it, and the conjuncts that reference it, is the
S6 off-switch.

**The propagation cascade** (unavoidable, discovered the hard way):

```
server_x25519_*_projection
  -> paired_x25519_key_shares
    -> server_hello_corresponds / client_hello_corresponds
       / paired_cleartext_hello_key_shares
      -> HandshakeAgreementNonReady helpers
      -> Impl.Driver.Pairing producers
      -> ConnectionState.Lemmas' shared-secret agreement
```

Two correspondence predicates had to grow: `client_hello_corresponds` now also
equates `Sem.clientHello_key_share_secp256r1`, and `server_hello_corresponds`
now also equates `Sem.serverHello_kex_share`.  With a group variable in play,
agreeing on the legacy X25519 field is no longer enough to conclude that the two
endpoints are talking about the same share.
`server_selection_key_share_consistent` gains a third conjunct,
`Some? server_key_share_private <==> Some? server_p256_private`, so that "the
selection has a private key" is a group-independent fact.

**Proof-engineering findings** (see also R7):

* A Pulse `match` on an enum does **not** refine the scrutinee in a `_`
  catch-all.  `Server.Driver.BufferedNetwork`'s dispatch had to become a boolean
  `if`, whose `else` branch does give the disequality.
* An `.fsti` `val`'s `requires` must imply the `.fst` `let`'s `requires`.
  Growing `Impl.Server.Send.fst`'s precondition without syncing the `.fsti`
  produced an "Assertion failed" at the *body* and cost several rounds to find.
* What worked against context growth: naming intermediate conclusions with
  explicit `assert (pure ...)` before the consumer, and factoring long assert
  chains into their own lemma (`lemma_transcript_checkpoints_of_event_trace`).
  Raising **fuel** made two proofs strictly worse.
* `Impl.Driver.Pairing`'s producers additionally needed the three *presence*
  facts named at the group read off the ServerHello: the dependent pair
  `(| g, sh_ks |)` otherwise hides `g` from the case analysis and the impossible
  branches cannot be discharged.

**Gate S4/S5.** `make verify` 0 errors, `make check-admits` 0 admits,
`make test` 34/34 — capability-neutral, no cell moved.

---

## 7. Stage S6 — turn it on, flip the ledger

> **S6 absorbed the acceptance gate that S2 originally carried.**  Before the
> steps below, S6 must first do what S2.1/S2.2 described: widen
> `Wire.Spec.clientHello_representable:472`, the `ch_extensions` key-share arm,
> `Impl.Parser.scan_ch_key_share:4287` / `scan_ch_extensions:4443`, and
> `is_valid_client_hello`'s key-share clause, so that a P-256-only ClientHello
> is *accepted*.  It must also lift `client_hello_has_p256_key_share` out of the
> `IM.client_hello` struct into a metadata `Box` (see "S2 as landed", finding
> R8), since the slot invariant cannot constrain a struct scalar.

1. `src/impl/TLS13.Impl.ConnectionState.Repr.fsti:1390` —
   `CS.server_supported_groups = [T.X25519]` → `[T.X25519; T.Secp256r1]`.
2. `Setup.fst:477,505,533,587,618,647,702` — `CS.server_selected_group = T.X25519`
   becomes the S1.3 policy applied to the stored ClientHello.
3. `test/unit/test_server_interop_matrix.c` — flip **both** `p256-only`
   (`:202`) and `ecdsa-credential-p256-only` (`:226`) to `OK` with `expect_group` `"P-256"`.
   The paired rows are exactly what proves the fix is not credential-specific.
4. Add two new cells while the harness is open: `p256-only-aes128` and
   `p256-only-no-middlebox-compat`, so the new capability is crossed with G1 and
   G4 the way G5 is.
5. `docs/server-client-parity.md` — move G2 to CLOSED (summary table `:57-62`,
   ledger `:461+`, roadmap item 5); `STATUS_SERVER.md:82`.

`p256-first-x25519-listed` **stays `refused`**: it needs HelloRetryRequest,
which is a separate flight in the server state machine and is out of scope here.

### S6 as measured (after S4/S5, commit `c02ab1b13`)

**There is no partial credit in S6.**  A `p256-only` ClientHello is blocked at
five independent points, and *all five* must move before any cell flips:

| # | blocker | site | status |
| --- | --- | --- | --- |
| 1 | the parse gate demands an X25519 share | `Wire.Spec.clientHello_representable:472` and its Parser mirror | open |
| 2 | the concrete mirror's invariant demands one too | `Impl.Messages.is_valid_client_hello:542` (`\| None -> False`) | open |
| 3 | the configured groups are X25519-only | `Impl.ConnectionState.Repr.fsti` `server_supported_groups` | open |
| 4 | the ServerHello writer emits `GNG.X25519` and a 32-byte share | `Impl.ConnectionState.Model.fsti` `server_hello_of_selection` | **closed by S6.3** |
| 5 | the ECDH is `x25519_shared` | `Impl.ConnectionState.LocalHandshake.fst` | open |

So S6 cannot be staged capability-neutrally the way S1-S5 were.  It is one
commit, and the order below is the dependency order.

> **Superseded in part.**  The paragraph above is correct about the *capability*
> but too pessimistic about the *work*: see "S6 as landed, part 1" below.  Four
> capability-neutral halves (S6.1-S6.5) landed as separate verified commits, one
> of them closing blocker 4 outright, and they also revealed a **sixth** blocker
> the table missed — the negotiated group is not recoverable at runtime at all
> and needed its own metadata box.  The ordering given immediately below (gate
> first) is *not* the order that was executed; it breaks every downstream proof
> at once.  The executed order generalises first and gates last.

**S6.1 — the secp256r1 finder's reveal lemmas.**
`Sem.kse_list_find_secp256r1` / `ch_find_key_share_secp256r1` /
`clientHello_key_share_secp256r1` already exist (`Wire.Semantics.fst:138-156`,
landed in S1).  What is missing is the pair of reveal lemmas the Pulse scanner
needs, exactly mirroring `lemma_reveal_kse_list_find_x25519_nil` / `_cons`
(`Wire.Spec.Reveal.Handshake.fsti:138-145`, bodies `= ()` at `.fst:77-79`).

**S6.2 — the scanner.**  Mirror `Impl.Parser.scan_ch_key_share:4287-4440` as a
65-byte `scan_ch_p256_key_share`.  `try_copy_kex_share:3632` already handles
both groups and returns the group it found, so the entry-level copy is done; the
new work is the list walk and its `list_drop` invariant.

> **Do not widen `scan_ch_extensions`.**  It carries
> `--z3rlimit 800 --fuel 2 --ifuel 2 --restart-solver`, returns an 8-tuple, and
> its loop invariant threads nine mutable references plus three ghost
> accumulators through a four-way extension dispatch.  Adding a ninth and tenth
> component means re-proving all of that.
>
> Take a **second, standalone pass** over the same extension list instead:
>
> ```
> fn scan_ch_p256_key_share
>   (ext_lo: GCH.clientHello_extensions_lowtype)
>   (#cext: Ghost.erased GCH.clientHello_extensions_mid)
>   requires  PPVCL.vmatch_vclist ... ext_lo cext
>   returns   res: (V.vec U8.t & bool)
>   ensures   PPVCL.vmatch_vclist ... ext_lo cext ** exists* kb.
>             V.pts_to (fst res) kb ** pure (Seq.length kb == 65 /\ ...)
> ```
>
> This is legitimate rather than a workaround: `clientHello_key_share_secp256r1`
> is *specified* as an independent walk (`Wire.Semantics.fst:147-156`), not as a
> component of the commit-first `ch_extensions` scan, so a separate pass matches
> the specification's own structure and its proof obligation is a single arm
> rather than a fifth thread through a four-way dispatch.  The cost is one extra
> O(n) pass over an extension list bounded by the record size.
>
> The walker needs `RV.reveal_ch_find_key_share_secp256r1` with nil/cons
> lemmas, the two `kse_list_find_secp256r1` reveal lemmas of S6.1, and a
> `probe_copy_p256_key` beside `probe_copy_x25519_key:3683`.  Land all of it
> *before* touching representability, so a failure here costs nothing else.

**S6.3 — the acceptance gate.**  `clientHello_representable:472` becomes

```
| Some (server_name, key_share, _, sig_schemes) ->
  (Some? key_share || ch_offers_p256_share b) && ...
```

with `ch_offers_p256_share b = (match Sem.clientHello_key_share_secp256r1 b with
Some k -> B.length k = 65 | None -> false)`.

> **This deliberately does not change `ch_extensions`' arity.**  The S2
> measurement (169 occurrences, 62 in `Impl.Parser.fst` and 51 in
> `Wire.Spec.Reveal.Handshake.fst(i)`) was the cost of a *fifth tuple
> component*.  Reading the P-256 offer straight off the message with a
> `Sem.*` accessor, rather than threading it through the commit-first scan,
> avoids that cost entirely: the scan's four components keep their meaning and
> every one of the 169 sites is untouched.

`is_valid_client_hello:542` then turns its X25519 clause into a disjunction and
its P-256 clause into an iff.  Per finding R8 this needs
`client_hello_has_p256_key_share` *and* a new `has_x25519_key_share` to live in
metadata `Box`es, not in the `IM.client_hello` struct: the slot invariant
describes a struct allocated once whose scalars are never rewritten.

**S6.4 — the writer.**  `server_hello_of_selection` builds at
`CS.server_selected_kex_group sel`, taking its share from
`CS.server_kex_public sel (CS.server_selected_kex_group sel)`; `valid_selection`
drops its third conjunct.  `lemma_server_hello_of_selection_bytesize` becomes
`58 + |ks| + |sid|`, so `90 + |sid|` and `95 + |sid|` become runtime lengths.

Measured: **35 numeric sites in 8 files** —
`Impl.ConnectionState.Model.fst:504,517,540`,
`Impl.ConnectionState.Model.fsti:809,823,830`,
`Impl.Serializer.fst:1527,1561`,
`Impl.Serializer.Handshake.fst:517,798`,
`Impl.Serializer.ServerHello.fst:39,75`,
`Impl.Server.Driver.BufferedHandshake.fst:699,701,1247,1252,1310,1409`,
`Impl.Server.fst:798,880,961,2674,2915,3218`,
`Impl.Server.Send.fst:250,269,335,358,533,539,542,610,652,1075,1409,1508`.

The runtime recovers the length the same way G1 recovers the cipher suite and
G4 recovers the session-id width: as a function of the stored ClientHello, via a
new `CM.server_selected_group` policy beside `CM.server_selected_suite`.  No new
driver payload and no new connection-state field is needed.

**S6.5 — the ECDH.**  `KEX.kex_shared_runtime g`, following the client template
at `Impl.ConnectionState.LocalHandshake.fst:4801`, padding with
`CryptoSpec.pad_share_65`.

**S6.6 — turn it on.**  `server_supported_groups` to
`[T.X25519; T.Secp256r1]`, policy "prefer X25519 when offered, else P-256" (so
`make test-atlas-loopback` keeps selecting X25519), then **delete
`CR.server_selection_group_pinned`** and every conjunct that mentions it
(`Model.fsti` `valid_selection`, `Impl.Server.Types` × 4, `LocalHandshake`,
`Server.Keys`, `Server`, `Queries`, `Server.Schedule`, `Server.Setup`,
`Server.Send`), and flip the two ledger cells.

---

### S6 as landed, part 1 — stages S6.1 to S6.5 (commits `5ee056664`,
### `b578465f0`, `0bd78b985`, `613e12980`)

The "no partial credit" reading above is right about the *capability* but wrong
about the *work*.  Four of the five blockers turned out to have a
capability-neutral half that can land, verified, before anything flips.  All
four landed green with the ledger unmoved.

**S6.1 + S6.2 — read the offer (`5ee056664`).**  Five reveal lemmas
(`lemma_reveal_kse_list_find_secp256r1_{nil,cons}`,
`lemma_reveal_ch_find_key_share_secp256r1_{nil,cons_ks,cons_other}`), and a
*second parser pass* rather than a wider `scan_ch_extensions`:
`probe_copy_p256_key`, `scan_kse_list_p256`, `scan_ch_p256_key_share`.  The
scan stays at four components, so the 169 `ch_extensions` occurrences S2
measured are untouched.  `Sem.clientHello_key_share_secp256r1` is *specified*
as an independent walk, so the second pass mirrors the specification's own
structure and reduces the obligation to a single extension arm.

**S6.3 — the writer builds at the selected group (`b578465f0`).**
`server_hello_of_selection` now takes its tag from `sho_named_group sel` and its
share from `sho_key_share sel = CS.server_kex_public sel (server_selected_kex_group sel)`.
`CM.valid_selection` keeps its X25519 conjunct, so every length in the tree is
still provably `90 + |sid|` and **none of the 35 numeric sites moved**.  Two
ghost bridges to the X25519-only `mk_server_hello_witness` gained
`requires server_selected_kex_group sel == KexX25519`; nothing had to be
threaded to supply it, because S4/S5 already put that conjunct into
`server_local_event_input_ready`/`LocalSendServerHello`.

**S6.4 — a runtime tag for the group (`0bd78b985`).**  This is the piece the
"five blockers" table missed.  The group is *not recoverable* at runtime:

  - `kex_share_storage.group` is the group the peer named in a **ServerHello**,
    so it is a client-side tag, and on the server `hs_server_hello` is still
    `None` when the shared secret is derived;
  - the stored ClientHello's bytes cannot answer it either, because an all-zero
    32-byte X25519 slot is a legal share.

So the group joins the ClientHello metadata, exactly as the session-id width did
for G4: `CM.client_hello_kex_group_for m` (the policy: prefer X25519 when
offered, else secp256r1) plus a `client_hello_kex_group : box kex_group` in
`handshake_message_storage`, threaded through 33 argument lists in 6 files and
written by the store path.

*Pulse note:* `with` binds a **prefix** of an slprop's existentials, and several
sites bind only four of `client_hello_metadata_exactly`'s five.  Appending the
new existential last is what kept every one of those binders valid unchanged.

**S6.5 — the offer becomes observable end-to-end (`613e12980`).**
`IM.is_valid_client_hello`'s secp256r1 clause became an iff; a secp256r1 entry
at a length other than 65 is no offer rather than a parse failure (RFC 8446
4.2.8).  `client_hello_slot_exactly` now constrains the stored secp256r1 bytes,
and the server's store path copies them.  The *client's* own mirror had to catch
up: the canonical ClientHello offers two `KeyShareEntry` values, so
`serialize_client_hello_from_start` now owns `l.client_hello_p256_key_share` and
fills it from `start_p256_key_share` (the scratch allocation and its free are
gone).  `SerH.lemma_ch_p256_key_share` proves by `= ()`.

**S6.6 — the ECDH dispatches on the group (`c360e2165`).**  This closes the
*implementation* half of blocker 5.  `TLS13.KEX` gains
`kex_shared_split_runtime`, a second entry point beside `kex_shared_runtime`:
the existing one suits the client, whose mirror stores whichever single share
the server named, padded to a uniform 65 bytes, whereas a server's mirror holds
the ClientHello's *offer*, which may carry both groups at once in a 32-byte slot
and a 65-byte slot side by side.  Padding the 32-byte one only to have
`unpad_share_65` undo it would cost a copy and two extensional-equality lemmas
per call, so both arms go straight to the raw binding.
`lemma_client_hello_kex_split_share` does the case analysis as a pure F* lemma —
inside the Pulse function it would mean duplicating the whole fold/unfold
discipline (eight slot existentials, six metadata boxes, five nested slprops) in
both arms — and both of its hypotheses are conditional, so it survives the gate
widening untouched.

The *signature* stays pinned.  The general form was written and verified (the
body proves the group-indexed `CS.legal_event` arm and then specialises back),
but it would have to be threaded up through `Server.Keys` -> `Server` -> both
drivers -> the canonical-protocol lemmas that discharge
`server_local_event_input_ready`, and that thread belongs to the flip.  The body
therefore derives the two facts it needs from the slot invariant, in three named
asserts the flip will delete.


### S6.7 as landed — the ServerHello length arithmetic, pre-staged

`poc_canonical_sh` now takes the group as a parameter and accepts any share
width in `32..65`; `lemma_sh_size` correspondingly proves

```fstar
GHS.handshake_bytesize (GHS.Body_server_hello (poc_canonical_sh rnd ks sid g cs))
  == 58 + Seq.length ks + Seq.length sid
```

which is `90 + |sid|` at X25519's 32-byte share and `123 + |sid|` at
secp256r1's 65-byte one.  Every one of the nineteen application sites still
passes `GNG.X25519`, and every downstream precondition still says
`Seq.length ks == 32`, so all forty numeric sites keep deriving `90 + |sid|` by
arithmetic and **none of them moved**.  Capability-neutral; the matrix stayed at
34/34.

The proof needed one ingredient that the X25519-specific version got for free.
At a literal group Z3 computes `namedGroup_bytesize GNG.X25519 == 2` by
evaluation; at a variable group it cannot.  `namedGroup`'s parser kind is
`LP.strong_parser_kind 2 2 (Some LP.ParserKindMetadataTotal)`, so
`LP.serialize_length GNG.namedGroup_serializer g` supplies `2 <= len <= 2`
generically.  With that one call added, both the interface and the
implementation verified on the first attempt at the existing `--fuel 8 --ifuel 8
--z3rlimit 120`.  The precedent that made this predictable was
`CM.server_hello_of_selection` (`Impl.ConnectionState.Model.fsti:652`), which has
built a ServerHello at a variable group since S4/S5 — it just never had to
state a *size*.

Files touched: `Impl.Serializer.Handshake.fsti/.fst`, `Impl.Serializer.fsti/.fst`,
`Impl.Serializer.ServerHello.fsti/.fst`, `Impl.Server.Send.fst`.

### S6.7b — as landed (`2537d001c`)

S6.7 generalised the *spec-level* size arithmetic.  S6.7b carries it through the
Pulse write chain above it, so that at the flip nothing in the serializer has to
move — only the selection policy does.  Capability-neutral: every caller still
passes X25519 and a 32-byte share, the wire output is byte-identical, and the
34-cell ledger did not move.

**One prediction below was wrong, in ATLAS's favour.**  The plan assumed level 2
would need a new concrete `(ks_len: SZ.t)` parameter threaded from level 5 down.
It does not.  `IM.is_valid_server_hello` (`Impl.Messages.fst:573`) has *always*
been group-parametric — it matches `Sem.serverHello_kex_share m` for
`Some (g, k)` and stores the group in `l.server_hello_kex_group` beside a
65-byte padded share — so the writer recovers both the wire tag and the share
width from the mirror it already holds:

```
let ks_len = sh_share_len_sz lsh.L.server_hello_kex_group;
let ng     = sh_named_group_of_kex lsh.L.server_hello_kex_group;
```

`sh_named_group_of_kex` and `sh_share_len_sz` are new `inline_for_extraction`
helpers, with `lemma_sh_named_group_of_kex_inv` inverting
`Sem.kex_group_of_named_group` on the two offered groups (it is `Secp256r1 ->
KexP256 | _ -> KexX25519`, hence not injective in general).  So levels 3-5 gained
only a *ghost* `#g`, and the concrete parameter list of every function in the
chain is unchanged.

The second useful surprise is at level 4: the record writer's fragment buffer
had been sized `90sz + sid_len`.  It is now `out_len - 5sz`, which is exact for
any share width and needs no access to the mirror at all.

The one genuinely new lemma is `lemma_canonical_kex_share`, connecting the
canonical ServerHello to `Sem.serverHello_kex_share` at a variable group.  As
first written it was *false*: `Sem.sh_find_kex_share` has a `| _ -> None` arm and
checks a group-specific width, so the lemma requires
`(g == X25519 \/ g == Secp256r1)` and is proved by an explicit two-arm match.
`lemma_canonical_key_share` (the X25519-specific one, going through
`Sem.serverHello_key_share_x25519`) was left alone; it still has other consumers
and moves at the flip.

Level 5 (`Impl.Server.Send`) keeps its `90`/`95` constants and simply passes
`#(Ghost.hide GNG.X25519)` at both call sites.  Those constants are pinned by
`mk_server_hello_witness` and `CM.valid_selection`, which are part of the S6.8
atomic flip and cannot move before it.

Diff: 7 files, +189/-89.  Gate: verify 0 errors, admits 0, 34/34 cells.

#### The stage as originally specified, for the record

S6.7 generalised the *spec-level* size arithmetic.  The Pulse write chain above
it is still pinned, and it can be pre-staged the same way: give it a runtime
share width and have every caller pass `32sz`.  That is capability-neutral, and
it retires the last runtime-length question before the flip.

The chain, bottom to top:

| # | declaration | file |
| --- | --- | --- |
| 1 | `poc_sh_mid`, `lemma_sh_conv_fwd`, `lemma_canonical_random/_session_id/_cs`, `lemma_ks_ext_conv`, `lemma_sh_handshake_conv_fwd` | `Impl.Serializer.Handshake.fst:449,465,742,754,759,766,784` |
| 2 | `serialize_server_hello_handshake_poc` | `Impl.Serializer.Handshake.fsti:259`, `.fst:794` |
| 3 | `serialize_server_hello_handshake` and its `_poc` wrapper | `Impl.Serializer.fsti:312,349`, `.fst:1527,1567` |
| 4 | `serialize_server_hello*` | `Impl.Serializer.ServerHello.fsti:40,77`, `.fst:39,81` |
| 5 | `serialize_server_hello_from_selection` and `fragment_len` | `Impl.Server.Send.fst:1158` and its `.fsti` |

The uniform edit at every level:

* add `(g: GNG.namedGroup)` (ghost above level 2, since the group tag is erased
  at run time) and `(ks_len: SZ.t)` (concrete from level 2 up);
* `Seq.length ks == 32` becomes `SZ.v ks_len == Seq.length ks /\ 32 <= SZ.v ks_len /\ SZ.v ks_len <= 65`;
* `SZ.v out_len == 90 + Seq.length sid` becomes `SZ.v out_len == 58 + SZ.v ks_len + Seq.length sid`;
* every caller passes `GNG.X25519` and `32sz`, so all forty numeric sites still
  derive `90 + |sid|` and the matrix cannot move.

Two things in the body of `serialize_server_hello_handshake_poc`
(`Impl.Serializer.Handshake.fst:794-975`) are genuinely X25519-shaped and are
the real content of the stage:

* `Seq.lemma_eq_elim key_share (CryptoSpec.pad_share_65 (reveal ks))` followed
  by `assert (pure (Seq.equal (Seq.slice key_share 0 32) (reveal ks)))` — the
  `32` becomes `SZ.v ks_len`, and the `alloc_copy_vec_exact` of the share must
  copy `ks_len` bytes rather than `32sz`.  The mirror is already a 65-byte vec,
  so nothing widens; only the prefix width becomes a variable.
* `lemma_canonical_key_share` (`:742`) concludes through
  `Sem.serverHello_key_share_x25519`, which is group-specific by construction.
  It should stay pinned at X25519 in this stage and move to
  `Sem.serverHello_key_share_bytes` / `serverHello_key_share_group` (both of
  which already exist, `Wire.Semantics.fst:239,247`) at the flip, when its
  consumers move too.

After S6.7b (landed) the flip reduces to: the acceptance gate (the 169
`ch_extensions` occurrences, now the only large item left), the ECDH's
specification, `Setup.fst`'s seven selection builders, the configured group list
and the three named pins, and the ledger.

### S6.7c — as landed (`e4594e008`): the acceptance scan becomes group-tagged

The "169 `ch_extensions` occurrences" item above was measured and found to be
confined to five files — `Impl.Parser.fst` (66), `Wire.Spec.Reveal.Handshake.fsti`
(34), `Wire.Spec.fst` (29), `Wire.Spec.fsti` (27), `Reveal.Handshake.fst` (18) —
and, more importantly, to be almost entirely *type* churn rather than proof
churn.  The commit-on-first scan `WS.ch_extensions` carried its key-share
accumulator at type `option (B.bytes_of_len 32)`: the 32 is the only thing that
is X25519-specific about it, and it forces every statement made over the scan to
be X25519-specific too.

The obvious alternative — keep a bare `option offered_share` and recover the
group from the share's length — is explicitly ruled out by the codebase's own
design law at `Crypto.Spec.fsti:176`: *the group is carried as an explicit tag
and is never recovered from a share's length.*  So the accumulator becomes a
tagged pair, the same shape `Sem.sh_find_kex_share` already returns on the
ServerHello side:

```fstar
let ch_key_share_offer = (GNG.namedGroup & Sem.offered_share)
```

(`Sem.offered_share = C.kex_public_any`, a byte string of length 32 or 65.)

The scan body still calls `Sem.kse_list_find_x25519` and stores
`(GNG.X25519, raw)`, so **acceptance is bit-identical** and the ledger did not
move.  The X25519-specific `key_exchange_to_key32` / `ch_find_key_share` pair was
deliberately left at 32 bytes: it is the *finder*, not the accumulator, and it is
precisely the one expression S6.8 replaces.

Fallout was three `k` -> `snd k` projections in the connect lemmas' conclusions
(no X25519 pin was needed — `Sem.ch_find_key_share` is itself the X25519 finder
and carries the width in its own result type) and four sites in
`Impl.Parser.fst`.  `module Sem = TLS13.Wire.Semantics` had to be added to
`Wire.Spec.fsti` and `Reveal.Handshake.fsti`; there is no cycle, as
`Wire.Spec.fsti` already referred to `TLS13.Wire.Semantics` fully qualified.

Diff: 4 files, +61/-39.  Gate: verify 154 modules 0 errors, admits 0, 34/34.

**Consequence for S6.8: the acceptance gate is no longer a 169-site item.**  It
is now one expression — the finder in the `key_share` arm of `ch_extensions`
(`Wire.Spec.fst:~299`, mirrored in `Wire.Spec.fsti:~270`,
`Reveal.Handshake.fsti:~215` and `Impl.Parser.fst:~774`) — plus the
`| None -> False` clause in `IM.is_valid_client_hello`.

### S6.7d — as landed (`1cac89cab`): the ECDH specification becomes group-indexed

Item 2 of the atomic flip below ("ECDH specification") is in two halves: the
*postcondition*, which says what the derived secret is, and the *precondition*,
which says which groups may reach the function.  Only the first can be
pre-staged, and S6.7d does it.

The postconditions of `try_derive_server_shared_secret_from_private_array`
(`LocalHandshake`), `process_derive_shared_secret_from_private_array`
(`Server.Keys`) and its `Impl.Server` wrapper no longer mention
`Crypto.Spec.x25519_shared`.  They now read

```fstar
match CS.client_hello_kex selection.CS.server_selected_client_hello
                          (CS.server_selected_kex_group selection) with
| Some k -> TLS13.Crypto.Spec.kex_shared
              (CS.server_selected_kex_group selection)
              (reveal 'server_private_key_bytes) k == Some shared
| None   -> False
```

This is zero-fallout because `LocalHandshake`'s body **already proved exactly
this** (S6.6 left the group-parametric assertion in place and then specialised it
back down); that specialisation block is now deleted.  Every precondition is
untouched — `server_selected_kex_group selection == KexX25519` still pins the
chain — so no caller, query, input gate or selection builder moves.

Diff: 6 files, +46/-30.  Gate: verify 0 errors, admits 0, 34/34.

#### Negative result: the precondition half cannot be pre-staged

For the record, because it costs an hour to rediscover.  Replacing the
precondition pin with the *policy-agreement* clause

```fstar
CS.server_selected_kex_group selection
  == CM.client_hello_kex_group_for selection.CS.server_selected_client_hello
```

verifies all the way up: `LocalHandshake` -> `Server.Keys` -> `Impl.Server` ->
`Impl.Server.Types.server_local_event_input_ready` (both `LocalDeriveSharedSecret`
arms) -> `CR.server_selection_group_pinned` ->
`Queries.can_schedule_derive_shared_secret_runtime` -> `Schedule`.  It then dies
at `Setup.fst`'s seven selection builders.

`CM.client_hello_kex_group_for m` is
`if Some? (Sem.clientHello_key_share_x25519 m) then KexX25519 else KexP256`
(`Model.fsti:153`), so a builder proving it equals `KexX25519` needs
`Some? (Sem.clientHello_key_share_x25519 ch)` — and that fact exists **only in
the runtime mirror** (`IM.is_valid_client_hello`'s `| None -> False`), not in any
spec-level invariant.  Checked and ruled out as sources: `server_selection_-
acceptable` (constrains the *config*'s groups, not the ClientHello's),
`legal_event`'s `LocalSelectServerParameters` arm, `server_end_to_end_invariant`,
and `client_hello_matches_start` (which does carry it, but is client-side).
Surfacing it needs a new ghost Pulse query unfolding `connection_exactly` /
`client_hello_slot_exactly` — which is real work and belongs to S6.8, where the
selection policy actually changes.  **That query is therefore the recommended
first move of S6.8**: both the selection builders and the ECDH precondition
removal depend on it.

### S6.8a — as landed (`c40d2e1cc`): the send-path witness becomes group-parametric

Item 4 below ("Lengths") had one piece left after S6.7b: `mk_server_hello_witness`,
the *abstract* ServerHello the whole server send path is stated against, still
built an X25519 `KeyShareEntry` over a 32-byte share.  It now takes the wire
`NamedGroup` as its first argument and accepts any share of 32..65 bytes —
the same shape as `SerH.poc_canonical_sh`, which S6.7 had already generalised
and which this witness is proved equal to.  With it:

* `lemma_mk_server_hello_witness_bytesize` concludes
  `58 + |key_share| + |session_id|` instead of `90 + |session_id|`.  At X25519's
  32-byte share those are the same number, which is why every consumer still
  derives its `90 + |sid|` unchanged — the generalisation is free.
* `lemma_mk_server_hello_witness_eq_poc` drops its X25519 pin.
* `lemma_server_hello_of_selection_eq_witness` drops its X25519 **requires**
  entirely and is stated at `CM.sho_named_group sel` / `CM.sho_key_share sel`,
  which is literally what `CM.server_hello_of_selection` builds with.

The witness's accessor refinement keeps its `serverHello_key_share_x25519`
clause, now guarded by `g == GNG.X25519`, so no consumer of that clause moved.
About fifty call sites gained a leading `GNG.X25519`.

Diff: 6 files, +101/-72.  Gate: verify 0 errors, admits 0, 34/34.

### S6.8b — as landed (`b80502853`): the two runtime prerequisites

Purely additive; two new declarations, nothing existing restated.

1. **`TLS13.KEX.kex_public_from_private_runtime`** — the build-direction
   counterpart of `kex_shared_runtime`.  Given the negotiated group and the
   server's 32 secret bytes it writes the server's own share into the uniform
   65-byte send buffer and returns its true wire width.  It branches on the
   explicit group tag, never on a length, so the C stubs still do no dispatch.
2. **`Queries.read_client_hello_kex_group`**, with its ghost counterpart
   `Model.stored_client_hello_kex_group` — reads the `client_hello_kex_group`
   metadata box S6.4 added and returns the group the policy picks for the
   stored ClientHello.

These are exactly what the flip was blocked on: with them the send path can
size its ServerHello as `63 + kex_public_len g + |session_id|` and fill its
share at the negotiated group, instead of the constants `90`/`95` and a
32-byte X25519 public.

### S6.8c-1 as landed — the model's ServerHello bytesize is group-parametric

`CM.lemma_server_hello_of_selection_bytesize` concluded the X25519-specific
`90 + |session_id|`; it now concludes

```
58 + CryptoSpec.kex_public_len (CS.server_selected_kex_group sel) + |session_id|
```

This is the S6.8a treatment of `mk_server_hello_witness` applied one layer down.
The body needed **no new reasoning** — only the deletion of two specialisation
steps.  It already went through `sho_named_group` / `sho_key_share` (which S6.7
made fully group-parametric) and then asserted them equal to `GNG.X25519` and to
the legacy 32-byte `server_key_share_public`; the bytesize equations are now
applied at `sho_named_group sel` and `sho_key_share sel` directly, and
`sho_key_share`'s refinement already gives its length as that group's
`kex_public_len`.

`valid_selection` is **unchanged** — its third conjunct still pins the group —
so the commit is capability-neutral.  `kex_public_len` is a total match on a
two-constructor datatype, so at `KexX25519` it reduces to `32` definitionally,
and the lemma has exactly **two** consumers in the whole tree
(`Send.fst:555`, `Driver.BufferedHandshake.fst:1248`), both of which keep
deriving `90 + |sid|` untouched.  Verify 0 errors, admits 0, matrix 34/34.

**The ordering rule this confirms**, and it is what makes the rest tractable:
the length arithmetic must generalise *before* the selection policy.  The moment
`valid_selection` stops forcing a literal group the `90` is underivable at every
site that states it, so a commit that flipped the policy first would be
repairing arithmetic under a broken tree.

### S6.8c — a measured correction to the remaining scope

The entry below says the concrete share widening must be "threaded through
`Send.fst` -> `Driver.BufferedHandshake` -> `Server.fst/.fsti`".  **The driver is
not on that path.**  `Driver.BufferedHandshake.fst:721` calls
`process_send_server_hello_with_derived_public_from_private_array`, which takes
the **private** key — and `CryptoSpec.kex_private = bytes_of_len 32` for *both*
groups, so nothing about that signature changes when P-256 is selected.  The
65-byte public buffer is a stack-local `let mut server_key_share = [| 0uy; 32sz |]`
inside that function's body (`Send.fst:1572`), handed to
`process_send_server_hello_from_arrays`.

**S6.8c-2 has since landed this widening** (`bf2581056`); what follows is the
measurement it was planned from, kept for the record.  The widening touches
only:

* `Send.fst:1572`'s stack-local (32sz -> 65sz, with
  `KEX.kex_public_from_private_runtime` in place of
  `Crypto.x25519_public_from_private` — the S6.8b primitive, which exists for
  exactly this), and
* `process_send_server_hello_from_arrays`' signature in `Send.fsti` / `Send.fst`
  and its re-export in `Server.fsti:596` / `Server.fst:863,926`.

`Driver.BufferedHandshake`, `Driver.BufferedWorkflow` and every other module are
untouched by the widening.  That is a materially smaller job than the entry
below assumed, and it is why the widening is *not* what makes the rest
indivisible.

**What genuinely is indivisible** is the length statements.  The ~24 sites
stating `95 + |stored session id|` are keyed on the connection state `'st0`, so
their group is `CM.stored_client_hello_kex_group 'st0` — and that is
`client_hello_kex_group_for m`, which is only *provably* `KexX25519` from the
acceptance gate's X25519 clause inside `IM.is_valid_client_hello`, not from the
pure part of a postcondition.  Generalising those statements therefore changes
what every caller must prove, and it cannot be done capability-neutrally the way
the selection-keyed arithmetic just was.  That, not the buffer, is the wall.

### S6.8c — the remaining flip, as measured after S6.7b/c/d and S6.8a/b

Everything above was capability-neutral.  What is left is genuinely one
indivisible commit, and it is now *only* the parts that change behaviour:

1. **Acceptance gate** (one expression, thanks to S6.7c): the finder in the
   `key_share` arm of `WS.ch_extensions` (`Wire.Spec.fst:~299`, mirrored in
   `Wire.Spec.fsti:~270`, `Reveal.Handshake.fsti:~215`, `Impl.Parser.fst:~774`),
   plus `IM.is_valid_client_hello`'s `| None -> False` and
   `CR.client_hello_slot_exactly`'s matching clause, which become the two-group
   disjunction.  (Both P-256 clauses are already iffs.)
2. **Selection policy**: `Setup.fst`'s seven builders (`:484,514,544,625,659,
   691,757,791,831`) set `CS.server_selected_group` from
   `CM.stored_client_hello_kex_group` rather than the literal `T.X25519`, and
   the concrete share they hand on comes from
   `KEX.kex_public_from_private_runtime` at that group.  On the *send* path
   that call already exists (S6.8c-2); only its group argument — the literal
   `CryptoSpec.KexX25519` in
   `process_send_server_hello_with_derived_public_from_private_array` — and the
   two `unpad_share_65 ... 32` widths in
   `process_send_server_hello_from_arrays` / `build_server_hello_from_arrays`
   have to become `kex_public_len g`, together with the
   `CryptoSpec.padded_share_65 ... 32` preconditions beside them.
3. **`CM.valid_selection`** (`Model.fsti:539`) drops its third conjunct, and
   `lemma_server_hello_of_selection_bytesize` (`Model.fsti:~864`, `.fst:~511`)
   concludes `58 + kex_public_len (server_selected_kex_group sel) + |sid|`.
4. **Lengths**: the ~20 occurrences of `95 + |stored session id|`
   (`Server.fsti:551,613,675,1914,1995`, `Server.fst:798,880,961,2677,2910,
   2918,3221`, `Send.fsti:267,391,453,515`, `Driver.BufferedHandshake.fst:701,
   702`) and the ~8 of `90 + |sid|` become
   `63 + kex_public_len (stored_client_hello_kex_group st) + |sid|` and
   `58 + kex_public_len ... + |sid|`; the runtime sizes read the group with
   `read_client_hello_kex_group`.  `Send.fst:~1158`'s `fragment_len` follows.
5. **ECDH precondition**: drop `server_selected_kex_group selection ==
   KexX25519` at `LocalHandshake.fsti:122,149` / `.fst:537,685`,
   `Server.Keys.fsti/.fst`, `Server.fsti:185,1168` / `.fst:333,1592`,
   `Server.Types.fst:110,124,426,533`, `Queries.fsti:540,563` /
   `.fst:2481,2563,2637,2733`, `Send.fsti:160,228` / `.fst:418,524`,
   `Setup.fsti:82,125` / `.fst:173,320`, `Schedule.fst:199,220`, replacing it
   with the policy-agreement clause.  S6.7d verified that this propagates; the
   only obligation it leaves is at the selection builders, which item 2 above
   discharges by *construction* — the builder no longer claims X25519, it
   claims the policy's answer, which is true definitionally.
6. **Pins**: delete `CR.server_selection_group_pinned` (`Repr.fsti:1178`) and
   every conjunct mentioning it.
7. **Config and ledger**: `server_supported_groups = [T.X25519; T.Secp256r1]`;
   `p256-only` and `ecdsa-credential-p256-only` flip to `ok` with
   `expect_group "P-256"`.

Note that item 5's negative result from S6.7d is *resolved* by item 2 and not
by a new ghost query: once the builder sets the group from the policy rather
than to a literal, `server_selected_kex_group sel == client_hello_kex_group_for
ch` holds by definition.  The ghost query is needed only if one insists on
keeping the builders at a literal `T.X25519`.

### S6 as re-measured — what is left is one atomic commit

With S6.1-S6.5 landed, the remaining work is genuinely indivisible, and the
reason is sharper than "five blockers".  It is this:

> The acceptance gate is what makes `client_hello_kex_group_for` constant.
> Widening the gate is therefore not a step that can be taken on its own: the
> moment a ClientHello without an X25519 share is accepted, the ECDH, the
> selection policy, the ServerHello length and `server_supported_groups` all
> face a group they cannot yet handle, and there is no runtime rejection path
> to fall back on.

Concretely the single commit must carry, together:

1. **Gate.**  ~~`Wire.Spec.clientHello_representable:472` becomes ...~~
   **Reduced by S6.7c.**  The scan's accumulator is already group-tagged, so the
   gate is now: replace the finder in the `key_share` arm of `ch_extensions`
   (`Wire.Spec.fst:~299`, mirrored in `Wire.Spec.fsti:~270`,
   `Reveal.Handshake.fsti:~215`, `Impl.Parser.fst:~774`) with one that also
   accepts a secp256r1 entry, and turn `IM.is_valid_client_hello`'s X25519 clause
   (`| None -> False`) — and `client_hello_slot_exactly`'s — into the two-group
   disjunction.  The P-256 clauses on both are already iffs.
2. **ECDH specification.**  The dispatch itself landed in S6.6; the
   *postcondition* landed in S6.7d, and the specialisation asserts are already
   deleted.  What remains is the *precondition*:
   `try_derive_server_shared_secret_from_private_array`'s
   `server_selected_kex_group selection == KexX25519` becomes
   `== client_hello_kex_group_for ch` plus
   `Some? (CS.client_hello_kex ch (client_hello_kex_group_for ch))`.  It
   propagates through `Server.Keys` -> `Server` -> `Driver.BufferedHandshake` /
   `Driver.BufferedNetwork` and bottoms out at
   `ST.server_local_event_input_ready`, discharged by
   `Impl.Server.CanonicalQueries` / `CanonicalProtocol` — those are where the
   two new conjuncts must actually be proved, from the canonical ClientHello.
   S6.7d verified this whole propagation; the only unmet obligation is at
   `Setup.fst` (see the negative result above), which the ghost query fixes.
3. **Policy.**  `Setup.fst`'s seven selection builders set
   `server_selected_group` from the stored ClientHello (the runtime value is now
   available: it is the S6.4 box).
4. **Lengths.**  ~~This is the part that cannot be pre-staged.~~  **It was
   pre-staged; see S6.7 below.**  The claim rested on `SerH.poc_canonical_sh`
   (`Serializer.Handshake.fsti:71`) pinning **two** things at once —
   `GKSE.group = GNG.X25519` and `requires Seq.length ks == 32` — which is
   true, and on the inference that because they must move together they must
   move *at the flip*, which does not follow.  Moving both together is
   capability-neutral as long as every caller keeps passing X25519 and a
   32-byte share.  What remains at flip time is the single runtime expression
   `fragment_len = 90sz `SZ.add` sid_len`
   (`Impl.Server.Send.fst:1158`), which becomes `58sz + ks_len + sid_len` once
   `valid_selection` drops its third conjunct, plus the `Seq.length ks == 32`
   preconditions on the Pulse serializer chain.  One thing was already right:
   the concrete mirror's `IM.server_hello_key_share` is **already** a 65-byte
   vec (`Impl.Messages.fst:587`), so no storage widens.
5. **Groups and pins.**  `server_supported_groups = [T.X25519; T.Secp256r1]`;
   delete `CR.server_selection_group_pinned` and every conjunct mentioning it,
   plus the three hypotheses S6.3 introduced.
6. **Ledger.**  `p256-only` and `ecdsa-credential-p256-only` to `OK` with
   `expect_group "P-256"`, and the two new crossed cells.

---

## 8. Risk register

| # | risk | mitigation |
| --- | --- | --- |
| R1 | The 42 selection literals cascade into `ConnectionState.Lemmas`, `ServerCanonicalShape`, `HandshakeAgreementNonReady`, `ProtectedWireSegmentation` | S1 is capability-neutral; if it will not close, abandon with `git checkout -- src/` and the tree is still green |
| R2 | `lemma_ch_extensions_connect` doubles in case count (S2.1) | write the P-256 finder in the same "stop at first entry of this group" style as `Sem.kse_list_find_x25519` so the two proofs are literally symmetric |
| R3 | The EverParse serializer chain (S5.2) resists parameterisation | split into "add the parameter, instantiate at X25519" then "pass the real group" |
| R4 | Z3 stops unfolding `server_kex_private/public` at the ~40 legacy sites | ship `lemma_server_kex_x25519_is_legacy` with an `SMTPat` in S1 |
| R6 | *(observed in S1)* A spec-level obligation "the selected group is X25519" is unprovable, because the spec's `server_supported_groups` is an arbitrary list | keep `legal_event`'s server derive arm X25519-shaped until S4/S5 generalise the `server_x25519_*_projection` family in the same commit |
| R7 | *(observed in S2)* Growing a widely-used slprop (here `is_valid_client_hello` / `client_hello_slot_exactly`) enlarges the SMT context of every proof that mentions it and breaks *distant, unrelated* queries | do **not** reach for `--z3rlimit` or `--z3seed`.  Name the failing projection as a lemma, or discharge a guarded hypothesis in explicit `assert (pure ...)` steps before the call that needs it.  Two such repairs were needed in S2 (`ChannelImplementation:409`, `Server:2910`); budget one or two per structural slprop change |
| R8 | *(observed in S2)* A `bool` field of a struct that the slot invariant owns cannot be constrained by that invariant — the struct is allocated once and its scalars are never rewritten | keep meaning in `is_valid_client_hello` (fresh structs) and move any flag the slot must know about into a metadata `Box`, as the session-id width already is.  **Resolved in S6.4/S6.5**: the slot states the secp256r1 bytes as a property of the *spec message* (no flag at all), and the one genuinely non-recoverable datum — the negotiated group — became the `client_hello_kex_group` box |
| R9 | *(observed in S6.3)* Adding a `requires` to a `.fst` `let` but not to the `.fsti` `val` reports **"Assertion failed" spanning the whole lemma body**, because F\* checks the body against the interface's precondition | the tell is the *range*: a whole-body range with "Assertion failed" is a signature mismatch, not a proof failure.  `--split_queries always` does not narrow it |
| R10 | *(observed in S6.4)* A mechanical multi-file edit to an slprop's argument list can silently mis-target, because a `#push-options` string or an argument name may occur more than once | assert an exact occurrence count for every whole-block replacement, and prefer appending to an existential list over inserting into one (Pulse `with` binds a prefix) |
| R5 | Verify cycles are 10-24 min, so blind iteration is expensive | iterate per-module with `fstar.exe` first; `make` dies at the `.depend` stage (`Makefile:315`) on any syntax error, so never run `make` on unparsed code |

## 9. Exit criteria

- `make -k -j60 verify` — 0 errors; `make check-admits` — 0 admits.
- `make -j60 test` — 36 cells (34 + 2 new), `p256-only` and
  `ecdsa-credential-p256-only` both `ok` with `expect_group == "P-256"`.
- `make test-atlas-loopback` still green — the verified client's offer leads
  with X25519, so the policy must still pick X25519 there.  This is the
  regression that a "prefer the client's first group" policy would cause, and
  it is why S1.3 prefers X25519 unconditionally.
- No `admit`, no `assume`, no weakened theorem.

---

# G3 line-level plan: server cross-record ClientHello reassembly

**Status: re-scoped and re-measured.  The blocker recorded in the first version
of this section was wrong.  The real one is one layer higher, and there are now
two costed routes instead of one.**

## What the first version of this plan got wrong

It named
`TLS13.Impl.Parser.DecoderWF.lemma_mk_cleartext_network_input_wf:245`
as "the blocker", on the theory that a reassembled ClientHello could not be
handed to the server's processing layer without a buffer-aware
`network_input_wf`.  That is not so.  `process_client_hello`
(`src/impl/TLS13.Impl.Server.Network.fsti:33`, `.fst:83`) takes `raw` and
`fragment` as **two separate arrays**, and constrains them independently:

- on `raw`: `CS.event_raw_delta_legal ... raw_bytes` (hence
  `received_cleartext_tls_message_raw`);
- on `fragment`: `Seq.equal fragment_bytes (WS.serialize_handshake (M.ClientHello ch))`.

There is **no** requirement anywhere in that contract that `fragment` be *the
fragment of a single record of* `raw`.  So the whole server ClientHello
processing layer is already record-count-agnostic, and a server-only coalescing
decoder can discharge both obligations directly without ever going through
`decoder_fragment_relation` / `network_input_wf`.  Those two predicates are
shared by every receive path on both roles and need not be weakened.

## The measurement

Widening the ClientHello arm of `received_cleartext_tls_message_raw`
(`src/spec/core/TLS13.Spec.StateMachine.fst`) **as a disjunction** — keeping the
existing single-record disjunct verbatim and adding
"n >= 1 Handshake records whose concatenated fragments parse as the message" —
was implemented as a probe and put through a full `make -k -j60 verify`.

Keeping the old disjunct verbatim is what makes this tractable: only *inversion*
sites can break, never *establishing* sites.  The result was **two** errors
across 89 rebuilt modules:

| # | site | nature |
| --- | --- | --- |
| 1 | `src/spec/properties/TLS13.Spec.WireFormatLemmas.fst:128-152` (`lemma_client_hello_sent_received_eq`); an earlier probe with a slightly different disjunct surfaced `lemma_received_client_hello_raw_length` (`:243`) in the same module instead | Benign.  It has the *sender's* form (`cleartext_tls_message_raw`, which pins one record) and `Seq.equal sent_raw received_raw` in scope, so the n >= 2 disjunct is refutable.  Needs one bridge lemma: a one-record stream's `concat_record_fragments` is that record's fragment.  The proof already exists inside `ConnectionState.Lemmas.lemma_raw_records_exactly_single_serialized`, which derives `parse_record_prefix raw == { values = [{outer; fragment}]; residual = empty }` explicitly. |
| 2 | `src/impl/TLS13.Impl.Server.CanonicalProtocol.fst:324` (`lemma_received_tls_raw_delta_legal_raw_record_parse_success`) | **Not benign.  This is the real wall.** |

## The real wall: one protocol step consumes exactly one record

Site 2 concludes `CT.raw_record_parse_success raw_received`, i.e.
`parse_record_wire raw == Some (ct, frag, B.length raw)` — the *whole* of the
step's received bytes is one record.  For a two-record ClientHello that is
simply false.  It is not an artefact: it feeds
`lemma_server_consumed_prefix_parse`, which turns the consumed bytes into a
`CW.wire_message`, and

```fstar
(* src/spec/core/TLS13.Spec.Endpoint.Wire.fst *)
type wire_message = {
  wm_raw: B.bytes;
  wm_content_type: T.content_type;
  wm_fragment: M.sealed_record;
  wm_parse_ok:
    squash (WS.parse_record_wire wm_raw ==
              Some (wm_content_type, wm_fragment, B.length wm_raw));
}
```

`wire_message` is **one record by construction**, `wire_parse` consumes exactly
one record, and the server driver's entire correctness statement is phrased
against this class through `TLS13.Impl.Server.CanonicalProtocol`.  That module
is *not* a standalone meta-theorem — it is aliased as `SP`/`CP` by
`Server.CanonicalQueries`, `Server.ChannelImplementation`, `Server.Driver` and
all six `Server.Driver.Buffered*` modules.  So:

> **The invariant that blocks G3 is "one network protocol step consumes exactly
> one TLS record", and it is load-bearing for the server driver, the canonical
> protocol refinement, and the cross-endpoint pairing theorems.**

Note also that error 2 failing means its dependents were skipped by `make -k`;
"2 errors" is a lower bound on that route's fallout, not the total.

## The two routes, costed

### Route A — widen the raw (the probe's route)

One protocol step may consume n >= 1 records.  Implementation cost is near zero
(`process_client_hello` already accepts it).  Spec cost is the wire-format
layer: `wire_message` must become "the record *group* consumed by one step",
`wire_parse` must become a streaming parser that coalesces consecutive Handshake
records until the concatenation is a whole handshake message, and every
`Common.WireFormat` law (prefix determinism, consumed-length, append
invariance) must be re-proven for it.  `Server.CanonicalProtocol` and the
pairing theory are generic over the class, so in principle they follow — but
site 2 shows they also reason about the one-record shape directly.

- Pro: no new event, no ghost buffer, no concrete buffer, no third decoder
  outcome, trivial implementation.
- Con: touches the semantic core that both roles and the pairing theorems are
  built on.  A regression here is a regression in the flagship theorems.

### Route B — the buffering event (the archived design)

`files/g3-spec-attempt.patch` in the session workspace (1212 lines) adds a
`ConnCleartextHandshake` event, an `hb_cleartext_handshake_bytes` ghost buffer,
`legal_cleartext_handshake_step`, and a concrete server reassembly buffer.

The point that was *not* appreciated when it was archived: **Route B preserves
"one step = one record"**.  Each buffering step consumes exactly one record and
appends its fragment to the buffer; the final step consumes the last record and
takes the ClientHello transition.  So `wire_message`, `wire_parse`,
`Server.CanonicalProtocol` and the pairing theorems keep their present shape.
That is why the archived design added an event instead of widening the raw — it
is architecturally the conservative choice, and the earlier verdict that it was
"wrong-headed" was itself wrong.

- Pro: the semantic core is untouched; the risk is confined to the server.
- Con: 87 occurrences across 20 files for the concrete buffer, a third decoder
  outcome in `TLS13.Impl.Parser.fst:7163-7210` (call sites `:7184,7194,7581,7592`),
  a buffer-aware `network_input_wf`, and
  `cleartext_handshake_buffer_empty server_model` added to the three
  cross-endpoint pairing lemmas
  (`ProtectedWireSegmentation.fst(i):4281,4703,5539,5709`).

### Recommendation

**Route B.**  It is the larger diff but the smaller blast radius, and unlike
Route A it cannot regress the client or the pairing theorems.  Route A should
only be revisited if the wire-format class turns out to admit a streaming
`wire_parse` cheaply — that is a self-contained experiment on one small file
(`TLS13.Spec.Endpoint.Wire.fst`) and is the right first probe if Route A is ever
reopened.

## Route B, ordered

| # | step | where |
| --- | --- | --- |
| 1 | Re-apply the archived spec patch (`ConnCleartextHandshake` event, `hb_cleartext_handshake_bytes`, `legal_cleartext_handshake_step`, `step_cleartext_handshake`, the empty-buffer bridge lemma with its `SMTPat`) | `src/spec/core/TLS13.Spec.StateMachine.fst` |
| 2 | Add `cleartext_handshake_buffer_empty server_model` to the three cross-endpoint pairing lemmas | `ProtectedWireSegmentation.fst(i):4281,4703,5539,5709` |
| 3 | Concrete pending buffer in the server representation plus the invariant tying it to the ghost buffer.  Mirror `hb_encrypted_server_handshake_bytes` — 87 occurrences across 20 files | `src/impl/` |
| 4 | Third decoder outcome ("complete record, incomplete handshake message") | `src/impl/TLS13.Impl.Parser.fst:7163-7210`, call sites `:7184,7194,7581,7592` |
| 5 | Buffer-aware `network_input_wf` and `lemma_mk_cleartext_network_input_wf` | `Client.Types.fst:1992`, `Parser.DecoderWF.fst:232,245,274` |
| 6 | Byte cap, mirroring `max_pending_protected_handshake = 32768` | `src/spec/core/TLS13.Spec.StateMachine.fst` |
| 7 | Flip `clienthello-across-two-records` **and** `aes128-clienthello-across-two-records`; add a three-record cell and an over-cap cell | `test/unit/test_server_interop_matrix.c` |

### The A/B split (decided while landing step 1)

Steps 1-2 as tabled above are **not** the right first commit.  Measured against
the tree, the archived patch bundles two separable things:

- **(a) the buffering *event* machinery** -- the `ConnCleartextHandshake`
  constructor, `hb_cleartext_handshake_bytes`, `legal_cleartext_handshake_step`,
  `step_cleartext_handshake`, the `event_raw_delta_legal` rule, and the
  ClientHello-delivery drain;
- **(b) the generalised *delivery rule*** -- `received_cleartext_tls_message_raw_buffered`,
  which makes the ClientHello raw-delta depend on the buffer.

Only (b) has hard fallout.  It breaks
`Impl.Parser.DecoderWF.lemma_mk_cleartext_network_input_wf`, whose `st0` is a
universally-quantified ghost with no invariant in scope, so the emptiness
obligation has to propagate through the record decoder's signature -- which is
shared by **both roles** -- up to the driver.  (b) is therefore inseparable from
steps 3-5.

So the landing order is:

- **Commit A = (a) only.**  Fully inert: the buffer is machinery without a
  consumer, because the delivery rule still requires the delivering record to
  carry the whole ClientHello, and `server_step` still does not admit a
  `ConnCleartextHandshake`.  No pairing theorem is touched, so **step 2 moves
  into commit B**.  The ledger does not move.
- **Commit B = (b) + steps 2-7**, landing together, exactly the discipline G2
  used (S1-S6.6 capability-neutral, S6.8d indivisible).

Two findings from landing commit A that commit B should carry forward:

1. `lemma_step_cleartext_handshake_inert` (`TLS13.Spec.StateMachine.fst`) is
   what makes a new `conn_event` constructor tractable.  Adding a constructor
   forces an arm onto every exhaustive `match ev with` in the tree (~60 sites,
   26 files); with that lemma in scope almost all of them collapse to a
   three-line `assert_norm` + lemma call.  An `SMTPat`-triggered variant keyed
   on `step_model` was tried and does **not** fire, because the branch context
   holds `step_model model ev` with `ev` a variable, not the constructor
   application -- the explicit `assert_norm` is what recovers the equation.
2. Adding the constructor widens some already-tight VCs past their rlimit.
   Three needed a bump, none needed a proof change:
   `ConnectionState.Lemmas.lemma_step_model_record_keys_consistent_for_role`
   and `Impl.Server.CanonicalProtocol.lemma_server_network_nonstep_canonical_step`.

### Commit B, measured

Commit B's spec half -- `received_cleartext_tls_message_raw_buffered`, its
empty-buffer bridge lemma (with `SMTPat`), and the rewiring of
`network_message_raw_delta_legal`'s `CL.Received` arm -- was applied on top of
commit A and verified tree-wide, purely to measure the blast radius.  **It is
three sites, not a cascade:**

| site | what fails | fix |
| --- | --- | --- |
| `ProtectedWireSegmentation.fst:316` | an `assert` of the *unbuffered* rule | the empty-buffer hypothesis of step 2 |
| `Impl.Server.CanonicalProtocol.fst:328` | same | same |
| `Impl.Parser.DecoderWF.fst:269` (`lemma_mk_cleartext_network_input_wf`) | `network_input_wf`'s obligation | **the real blocker; see below** |

The first two are step 2 and are cheap.  The third is the one that makes (b)
inseparable from the implementation, and the measurement pins down exactly why:

`network_input_wf st0 ct fragment raw` promises "if the FRAGMENT ALONE parses to
`msg`, the raw delta is legal for delivering `msg`".  Under the buffered rule
that is only true when the buffer is empty.  `st0` reaches the decoder as an
**erased ghost** (`(reveal 'st0)` at `Impl.Parser.fst:7702,7712,8099,8110`) with
no invariant attached, and the decoder is shared by both roles, so the emptiness
fact cannot be produced there.

The right shape for commit B is therefore **not** to gate `network_input_wf` on
emptiness -- that only moves the obligation to callers who equally cannot
discharge it -- but to **split the predicate**:

- the decoder keeps promising the *unbuffered* delta (`received_cleartext_tls_message_raw`),
  which is role-agnostic and needs no state knowledge;
- the *driver*, which does hold the server's concrete pending buffer, applies a
  bridge lemma to turn that into the buffered delta when the buffer is empty,
  and takes the reassembling path (parse `pending ++ fragment`) when it is not.

This keeps the shared record decoder out of the reassembly story entirely, and
is what makes steps 3-5 land as one coherent change rather than as a
signature-propagation exercise across both roles.

Step 2 must not simply weaken the three pairing guarantees.
`lemma_paired_replay_split_prefixes_equal_single_client_hello`
(`ProtectedWireSegmentation.fsti:1398`) has **no callers in `src/`** -- it is a
published guarantee, so the added `cleartext_handshake_buffer_empty server_model`
hypothesis is a real weakening rather than a caller-discharged one.  It is also
genuinely necessary for the statement as written (`server_model` is
unconstrained, so a mid-reassembly server falsifies the record-aligned
conclusion).  Commit B should therefore add the hypothesis **and** a
fresh-server corollary, so the guarantee for real connections is unweakened.

## Related limitation, both roles

`WS.parse_tls_message` (`src/spec/core/TLS13.Wire.Spec.fst:921`) requires
`consumed == B.length fragment`, so **two handshake messages coalesced into one
record** are rejected on both the client and the server.  This is a separate
gap from G3 and is not addressed by either route above.

### Commit B, unblocked: un-fusing the cleartext delivery rule

The "Commit B, measured" note above concluded that `Impl.Parser.DecoderWF` was an
immovable obstruction, because the shared record decoder would have to prove a
*state-dependent* fact about an erased ghost `'st0`.  That conclusion was wrong,
and the reason it was wrong is worth recording, because it is the whole shape of
the design.

**The asymmetry has nothing to do with encryption.**  Compare the two receive
paths in the model:

| | record-shape obligation | message-identity obligation |
|---|---|---|
| protected | `event_raw_delta_legal`: `raw_records_exactly raw Application_data 1` — state-free, proved by the **decoder** | `SMCan.received_event_decode_projection` — state-aware (needs the read keys), proved by the **driver** |
| cleartext (before) | `event_raw_delta_legal`: `∃f. parse_record_wire raw = Some (Handshake,f,·) ∧ parse_tls_message Handshake f = Some msg` — **both, fused**, proved by the decoder | `received_event_decode_projection` — literally `True` |

For protected records the fragment is only obtainable by decrypting under the
connection's keys, so the model was *forced* to keep the record-level obligation
apart from the message-level one, and to give the latter its own driver-side slot.
For cleartext records the fragment is right there in the record, so the original
design fused the two into a single predicate and left the driver-side slot empty.
That fusion — not encryption — is what made reassembly look impossible: it put a
buffer-relative claim into a predicate that the role-agnostic, state-blind decoder
has to discharge.

**The fix is to un-fuse at the decoder/driver boundary**, exactly mirroring the
protected path:

* `CT.received_tls_raw_delta_legal_unbuffered` (new, `Impl.Client.Types`) is what
  the decoder promises.  For a received cleartext message it is the *old*,
  state-free rule; for everything else it is unchanged.  So
  `network_input_wf`'s meaning is **bit-for-bit what it was before reassembly** —
  `lemma_mk_cleartext_network_input_wf` needed no change at all, and the
  `DecoderWF` "obstruction" simply evaporated.
* `CS.network_message_raw_delta_legal_unbuffered` (new, `Spec.StateMachine`) is the
  same split one level down, for `network_input_message_projection`.
* `CS.received_cleartext_tls_message_raw_buffered` is the generalised, buffer-relative
  model rule, wired into `network_message_raw_delta_legal`'s `Received` arm.
* The bridge between them is emptiness of the pending buffer, carried by two
  `SMTPat`-triggered lemmas
  (`lemma_received_cleartext_tls_message_raw_buffered_of_empty`,
  `lemma_network_message_raw_delta_legal_of_unbuffered`) plus a preservation lemma
  `lemma_step_model_preserves_cleartext_handshake_buffer_empty`
  (`hb_cleartext_handshake_bytes` is written in exactly three places, so an empty
  buffer stays empty across any non-buffering step).

**Where the obligation actually landed.**  Un-fusing pushed the buffer-relative
claim to precisely the places that own a buffer:

1. the **server's ClientHello delivery site** (`Impl.Server.Network`), via a
   staging conjunct on `ST.server_end_to_end_invariant`;
2. the **system-level wire bridges** (`TLS13.System`), via a staging conjunct on
   `tls_system_inv`;
3. the **cross-endpoint pairing theorems** (`ProtectedWireSegmentation`), via an
   explicit `cleartext_handshake_buffer_empty server_model` hypothesis on the
   published `.fsti` guarantees — the genuine, anticipated weakening.

Items 1 and 2 are *staging* invariants: they are true today only because nothing
emits a `ConnCleartextHandshake` step yet.  When the concrete pending buffer is
threaded through the server they are replaced by "the model buffer equals the
concrete buffer", and the delivery site proves the buffer-relative rule directly
instead of bridging from emptiness.  Item 3 is permanent, and should eventually be
accompanied by a fresh-server corollary that discharges the hypothesis from
`initial`/`LocalStartServer`.

State after this commit: `make -k -j48 verify` clean, `make check-admits` 0,
`make -j48 test` 34/34 MATCH.  Behaviour is unchanged — the model *permits*
reassembly now, and no implementation performs it yet.

### Commit B2: generalising `server_step`, and the second structural wall

The un-fusing above made the *model* permit reassembly.  This commit makes the
server's **state-machine relation** permit it: `ES.server_step`'s `WireEvent` arm
no longer says "there exists a received `tls_message`" but "there exists a
`conn_event` satisfying `ES.server_wire_received_event`", which admits a
`ConnCleartextHandshake` buffering step alongside a received network message.
This is a prerequisite for any implementation of reassembly — the impl must
produce a legal `server_step` — and it is capability-neutral: no code buffers yet.

**Generalising a step relation is a weakening, so only *inversion* sites break.**
Every break has the identical shape: a lemma does
`eliminate exists (msg:M.tls_message). (let conn_ev = ConnNetworkEvent {Received; msg} in …)`.
Twelve such sites were found across eight files (`WireStep` ×8, plus
`Impl.Server.CanonicalProtocol`, `ServerNoCcsInputs`, `ServerNoCcsOutputs`,
`PairingNoTailWireLogs`, `ServerReadRecvCount`, `ServerSfsRecovery`,
`TLS13.System`).  Commit A had already added `ConnCleartextHandshake` arms to the
generic per-event lemmas, so most needed only the `eliminate` generalised.

**The wall the plan did not anticipate.**  Two layers read the model as though a
cleartext handshake message always arrives in exactly one record, and neither
survives a buffering step:

1. **The system product** (`TLS13.System.tls_machine_iface`).  Its wire bridges
   read "the delivered raw bytes ARE the ClientHello" straight off a delivery, and
   `tls_system_inv` carries the staging emptiness conjunct.  A buffering step makes
   the buffer non-empty, so `tls_system_inv` is not preserved.
2. **The server shape invariant** (`ServerCanonicalShape.log_shape`).  It pins the
   event log to an EXACT list of milestone events per control state
   (`log == [ev_start]` at `HsAwaitingClientHello`,
   `log == [ev_start; ev_recv_ch ch]` at `HsClientHelloReceived`, …).  A buffering
   step *appends* to the log without moving the control, so it violates the
   awaiting arm and shifts every later arm.  Two flagship inversion lemmas
   (`ProtectedWireServerFlightInversion`, `ProtectedWireClientFinishedInversion`)
   consume the exact-list conclusion, so widening the arms — or filtering the log
   through a `visible_log` projection, the server counterpart of the client's
   `canonical_log` normalisation — weakens facts they depend on.  Both were tried;
   both push the existential all the way into the flagship theorems.

**The repair: one shared staging wrapper.**
`ES.server_step_nonbuffering st0 ev st1 out = server_step … /\ cleartext_handshake_buffer_empty st1.cs_model`.
Because `legal_cleartext_handshake_step` requires a NON-empty fragment, a buffering
step always leaves a non-empty buffer, so this relation is **exactly** the
pre-generalisation `server_step`: it admits every step the old one did and no
buffering step.  Nothing downstream is weakened, and the entire staging debt of the
generalisation is concentrated in one definition.  It is installed at four places —
`ES.server_state_machine`, `ES.server_canonical_step_rel`, `WStep.server_sm`, and
`TLS13.System.tls_machine_iface` — which is precisely the reachability + shape +
product layer.

Two reusable lemmas do the recovery work at the sites that still pin emptiness:

* `ES.lemma_wire_received_event_empty_buffer_not_buffering` — the vacuity argument
  (empty post-state buffer ⇒ the event was a received network message);
* `ES.lemma_server_wire_step_received_msg` — packages that into the exact existential
  the old inversion sites already `eliminate`, so each such site needs a single
  extra call in front of its unchanged body.

Sixteen system-layer lemmas gained a `cleartext_handshake_buffer_empty s'.cs_model`
requires; the three server shapes in `TLS13.System` (`server_send_shape`,
`deliver_to_server_shape`, and the `mp_*_intro` converses) now expose it, so callers
get it for free off a delivery.

**Lifting this is the whole of the remaining work.**  When the concrete pending
buffer is threaded through the server, `server_step_nonbuffering` is deleted, the
system bridges become buffer-relative, and `log_shape` moves onto a
buffering-filtered view of the log — at which point the two flagship inversion
lemmas must be restated over that view.  That restatement is the largest single
piece of G3 that remains, and it was not visible from the model layer at all.

State after this commit: `make -k -j48 verify` clean, `make check-admits` 0,
`make -j48 test` green (34/34 server matrix, 2/2 client record-split, all interop).
Behaviour is unchanged.

### A design fork worth weighing before commit B3

Landing B2 exposed a cheaper alternative that was not visible when commit A was
designed, and it is worth deciding deliberately rather than by inertia.

**Route B (what is built).**  Buffering is a MODEL event: `ConnCleartextHandshake`
is a `conn_event`, each partial record is a `step_cleartext_handshake`, and the
delivery rule is buffer-relative (`received_cleartext_tls_message_raw_buffered`,
`raw` = the LAST record, message = `pending ++ fragment`).  Cost: every buffering
step appends to `cs_event_log`, which is what collides with
`ServerCanonicalShape.log_shape`'s exact-list-per-control-state invariant and
forces the two flagship inversion lemmas to be restated over a filtered log.

**Route C (not built).**  Buffering is INVISIBLE to the model: the partial records
are held only in the concrete server representation, the model takes NO step while
buffering, and on completion the server takes a single ordinary
`ConnNetworkEvent Received (ClientHello ch)` step whose `delta_raw_received` is the
concatenation of ALL the records that carried the message.  No new `conn_event`, no
new log entry, `log_shape` untouched, both flagship inversion lemmas untouched.

What Route C needs instead:

* `received_cleartext_tls_message_raw`'s ClientHello arm widened from "`raw` parses
  as ONE Handshake record whose fragment is the message" to "`raw` parses as a
  SEQUENCE of Handshake records whose fragments concatenate to the message".  A
  local model change with no new constructor.
* The byte-pairing invariant relaxed from "model `raw_received` == everything the
  driver consumed" to "model `raw_received` ++ concrete pending == everything
  consumed".  This is the real cost, and it is not obviously smaller than Route B's
  flagship restatement — `cs_wire_log.raw_received` is coupled to the event log by
  `legal_connection_delta`, so the lag has to be carried explicitly.
* The same new `endpoint_status` constructor Route B needs (`NeedMoreInput` pins
  `consumed_len == 0sz`, `StepOk` pins `st1` to a "received X" state), so that is a
  wash.

Neither route avoids the concrete pending buffer, and both need the new status
constructor; the fork is purely about WHERE the lag is recorded — in the model's
event log (B) or in the impl/model byte-pairing (C).  Route B is already built and
green through the spec and step layers; Route C would mean reverting commit A's
`ConnCleartextHandshake` machinery.  Recommendation: measure the flagship
restatement (todo `g3-flagship`) FIRST — it is the only unquantified piece of
Route B, and it is the one thing Route C buys outright.
