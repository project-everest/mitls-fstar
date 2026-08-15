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

1. **Gate.**  `Wire.Spec.clientHello_representable:472` becomes
   `(Some? key_share || ch_offers_p256_share b)`; the Parser's accept
   computation mirrors it; `IM.is_valid_client_hello`'s X25519 clause
   (`| None -> False`) and `client_hello_slot_exactly`'s become the same
   disjunction.
2. **ECDH specification.**  The dispatch itself landed in S6.6; what remains is
   its signature.  `try_derive_server_shared_secret_from_private_array`'s
   precondition becomes
   `server_selected_kex_group selection == client_hello_kex_group_for ch` plus
   `Some? (CS.client_hello_kex ch (client_hello_kex_group_for ch))`, and its
   `ensures` becomes `CryptoSpec.kex_shared g ...`.  Both propagate through
   `Server.Keys` -> `Server` -> `Driver.BufferedHandshake` /
   `Driver.BufferedNetwork` and bottom out at
   `ST.server_local_event_input_ready`, which is discharged by
   `Impl.Server.CanonicalQueries` / `CanonicalProtocol` — those are where the
   two new conjuncts must actually be proved, from the canonical ClientHello.
   Delete the three specialisation asserts S6.6 left in the body.
3. **Policy.**  `Setup.fst`'s seven selection builders set
   `server_selected_group` from the stored ClientHello (the runtime value is now
   available: it is the S6.4 box).
4. **Lengths.**  The 35 numeric sites enumerated below become runtime lengths
   `58 + kex_public_len g + |sid|`, once `valid_selection` drops its third
   conjunct.  *This is the part that cannot be pre-staged, and the reason is
   `SerH.poc_canonical_sh` (`Serializer.Handshake.fsti:71`), the transparent
   canonical builder the whole write path is defined against.  It pins **two**
   things at once — `GKSE.group = GNG.X25519` and `requires Seq.length ks == 32`
   — and they are not separable: parameterising the tag while keeping the length
   at 32 builds a message no peer would accept, and relaxing the length is
   exactly the 35-site change.  29 occurrences across 9 files move together.*
   One thing is already right: the concrete mirror's
   `IM.server_hello_key_share` is **already** a 65-byte vec
   (`Impl.Messages.fst:587`), so no storage widens.
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
