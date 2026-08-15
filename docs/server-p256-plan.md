# G2 implementation plan: secp256r1 key exchange on the verified server

Companion to `docs/server-client-parity.md`, which says *what* the gap is and
*why* it matters.  This file says *where* the edits go, in what order, and what
each step has to prove.  Line numbers are as of commit `c2e73aa7a`.

A line-level plan for **G3** (cross-record ClientHello reassembly) is in the
last section, because the two share a staging discipline and one of them will
be picked up first.

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
| R8 | *(observed in S2)* A `bool` field of a struct that the slot invariant owns cannot be constrained by that invariant — the struct is allocated once and its scalars are never rewritten | keep meaning in `is_valid_client_hello` (fresh structs) and move any flag the slot must know about into a metadata `Box`, as the session-id width already is |
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

Recorded at the same granularity because the analysis is already done (see
`docs/server-client-parity.md`, roadmap item 4).  The spec mechanism exists as a
1212-line patch; the blocker is that it cannot be *used* without a concrete
buffer.  Order of work:

| # | step | where |
| --- | --- | --- |
| 1 | Concrete pending buffer in the server representation, plus the invariant tying it to the ghost `pending_cleartext_handshake`.  Mirror `hb_encrypted_server_handshake_bytes` — 87 occurrences across 20 files: `ConnectionState.Repr.fst(i)`, `ConnectionState.Network.fst(i)`, `ConnectionState.Queries.fst(i)`, `ConnectionState.LocalHandshake.fst`, `System.WireStep.fst`, `System.AppExtrasInv.fst`, `Client.Types.fst`, `Client.fst`, `Client.CanonicalProtocol.fst`, `Client.Drain.fst` | `src/impl/` |
| 2 | Third decoder outcome ("complete record, incomplete handshake message") in `TLS13.Impl.Parser.fst` cleartext path `:7163-7210`; call sites `:7184,7194,7581,7592` | `src/impl/TLS13.Impl.Parser.fst` |
| 3 | Buffer-aware `network_input_wf` (`TLS13.Impl.Client.Types.fst:1972`) so that `DecoderWF.lemma_mk_cleartext_network_input_wf:245` can discharge `received_tls_raw_delta_legal` — **this is the blocker; start here when scoping, finish here when building** | `src/impl/TLS13.Impl.Parser.DecoderWF.fst:245,274` |
| 4 | Re-apply the archived spec patch (`ConnCleartextHandshake` event, `hb_cleartext_handshake_bytes`, `legal_cleartext_handshake_step`, `step_cleartext_handshake`, the empty-buffer bridge lemma with its `SMTPat`) | `src/spec/core/TLS13.Spec.StateMachine.fst` |
| 5 | Add `cleartext_handshake_buffer_empty server_model` to the three cross-endpoint pairing lemmas | `TLS13.ConnectionState.ProtectedWireSegmentation.fst(i):4281,4703,5539,5709` |
| 6 | Flip `clienthello-across-two-records` **and** `aes128-clienthello-across-two-records`; add a three-record cell and an over-cap cell (>32768) | `test/unit/test_server_interop_matrix.c` |

Step 3 is the one that decides whether G3 is feasible; steps 1 and 2 are
prerequisites for it, and steps 4-6 are the parts already understood.
