# Plan: Replace TLS client+server spec/impl types with QuackyDucky-generated ones

## Goal
Replicate the `calc_sample` migration on the TLS 1.3 client and server: make the
**QuackyDucky-generated `TLS13.Wire.Generated.*` types** the source of truth and
replace the hand-written specification and implementation message/leaf types
across the codebase. **Design only — no implementation yet.**

This plan is *inspired by* the calc plan but must account for the fact that TLS is
~50× larger and, crucially, has a **different starting architecture** than calc had.

---

## Why TLS is not a calc-style clean swap (the central finding)

In `calc_sample` the generated record **was** the semantic message (`{op;operand}`),
so the generated type could directly replace the hand-written inductive. The TLS
codebase is structured around **three distinct representations** plus a large
correspondence layer:

| Layer | Modules | Role | Size |
|-------|---------|------|------|
| **Generated (wire grammar)** | `generated/TLS13.Wire.Generated.*` (78 modules) | Full RFC-8446 wire structure, parsers/serializers/copyful API | 156 files |
| **Reveal / Wire.Spec (correspondence)** | `TLS13.Wire.Spec`(+Reveal*, NonExact, RevealDecode, WireFormatLemmas) | Hand-written `parse_tls_message`/`parse_record`/`serialize_*` **fed by** the generated parsers, with lemmas proving they agree | **~10,692 lines, 16 modules** |
| **M (pure semantic model)** | `TLS13.Messages` (104 L), `TLS13.Types` (65 L) | Semantic projection: only the profile-relevant fields **+ a raw `body`** for transcript exactness | 169 lines |
| **L (extractable mirror)** | `TLS13.Impl.Messages` | "L counterparts of TLS13.Messages": machine ints + heap vectors, with `is_valid_*` predicates tying L↔M | large |

**The mismatch that dominates this task:** M is a *semantic projection*, not a wire
mirror. e.g. `M.client_hello = { random; server_name; key_share; cipher_suites;
signature_schemes; body }` (`TLS13.Messages.fst:13-20`) — a handful of fields plus
the **verbatim handshake bytes**. The generated `clientHello` is the *entire* wire
grammar (`legacy_version, random, legacy_session_id, cipher_suites,
legacy_compression_methods, extensions<list of typed envelopes>`). The `key_share`
and `signature_schemes` M cares about live **inside the generated extension list**,
so any code that today reads `ch.key_share` would, on generated types, have to walk
the extension list. M's `body` exists to guarantee byte-exact transcript replay
regardless of grammar quirks.

**M is the semantic spine of the whole system, not just a wire type:**
- `TLS13.StateMachine` events embed M records: `SendClientHello of M.client_hello`,
  `RecvServerHello of M.server_hello`, … and `step` branches on them
  (`TLS13.StateMachine.fst:52-64,224-258`).
- `TLS13.Spec.ConnectionState` stores `option M.client_hello/server_hello/…` and
  `server_selected_client_hello: M.client_hello`
  (`TLS13.Spec.ConnectionState.fst:224,244-251`).
- The layered-log predicates (`connection_view`, `connection_state_*_consistent`,
  `directed_message M.tls_message`) are stated over M (`TLS13.ConnectionLog.fst`,
  `TLS13.Spec.ConnectionState.fst:2922-3163`).
- The impl is saturated with M/T (e.g. `Server.Send` 463 M-refs, `Server.Keys` 237,
  `Server.Driver.Network` 360 T-refs, `Server.fst` 154/252).

So "replace the types all across" is, for TLS, a **re-architecting of the semantic
stack**, not a wire-layer swap. The plan must make the scope decision explicit.

### Type correspondence (the clean part)
The **leaf enums** map almost 1:1 (only the unknown-constructor payload differs:
hand-written `… of nat` vs generated `Unknown_… of U16.t`):

| Hand-written (`TLS13.Types`) | Generated |
|---|---|
| `content_type`, `protocol_version`, `alert_description` | `ContentType`, `ProtocolVersion`, `AlertDescription` |
| `cipher_suite` (`… \| UnknownCipherSuite of nat`) | `CipherSuite` (`… \| Unknown_cipherSuite of U16.t`) |
| `named_group`, `signature_scheme`, `extension_type` | `NamedGroup`, `SignatureScheme`, `ExtensionType` |
| `hostname = bytes` | `HostName` (vlbytes 1..65535) |

The **message records** map structurally-loosely (M projects; generated is full):
`client_hello/server_hello/encrypted_extensions/certificate_msg/certificate_verify/
finished/handshake_msg/plaintext` ↔ `ClientHello/ServerHello/EncryptedExtensions/
Certificate/CertificateVerify/Finished(=lseq 32)/Handshake/TLSPlaintext`. M-only,
no generated counterpart: `tls_message` (the semantic envelope:
Handshake/AppData/Alert/CCS/KeyUpdate dispatch), `tls_error`.

---

## Scoping options (the pivotal decision)

Because of the mismatch above, "replace M with generated" admits three very
different targets with very different cost:

### Option A — Full literal replacement ("all across")
Generated types become the **only** message types; delete `TLS13.Messages`,
`TLS13.Impl.Messages` (L), `TLS13.Wire.Spec` + the entire Reveal layer. The state
machine, connection-state spec, log predicates, and the entire client+server impl
are re-expressed over generated types, with **semantic accessors** (e.g.
`clientHello_key_share : GCH.clientHello -> …` that walk the extension list)
replacing today's M record-field reads, and transcript exactness re-founded on the
generated parse/serialize round-trip (replacing M's `body`).
- *Matches the request literally.* *Largest, riskiest scope:* re-opens the proven
  semantic stack (`StateMachine`, `ConnectionState` ~3.7K L, `ConnectionLog`) and
  every impl module; re-introduces the extension-navigation complexity M was
  designed to hide. Effectively a multi-month re-verification of ~130K lines.

### Option B — Codec replacement; M kept as a generated-derived semantic view (de-risking subset of A)
Make the generated parsers/serializers the codec and **delete the hand-written
`TLS13.Wire.Spec` + Reveal layer (~10.7K lines)** — its only purpose is to bridge
hand-written-spec ↔ generated, which is unnecessary once generated *is* the spec.
Re-found M's leaf/enum types on the generated enums, and define the M↔wire boundary
as **decode = generated-parse-then-project** and **encode = unproject-then-generated-
serialize**. Keep M's message records as the thin semantic model so the state
machine / connection-state / log stay stable; replace the L mirror with the
generated copyful lowtypes in the impl.
- *Captures most of the value* (deletes the 10.7K correspondence layer, single
  source of wire truth) *while keeping the semantic stack and its proofs intact.*
  Tractable, incremental, much lower risk.

### Option C — Enums/leaf-only
Replace just the `TLS13.Types` enums + `hostname` with the generated enums across
spec+impl; keep M records, Wire.Spec, and Reveal. Smallest, modest payoff, a safe
first slice of either A or B.

**DECISION (confirmed by user): Option A — full literal replacement.** The
generated `TLS13.Wire.Generated.*` types become the only message/leaf types; M
(`TLS13.Messages`/`TLS13.Types`), the L mirror (`TLS13.Impl.Messages`), and the
hand-written `TLS13.Wire.Spec` + Reveal layer are all deleted. Options B and C are
retained below only as **de-risking milestones inside A** (C — enums first — is the
recommended first slice; B's "delete Wire.Spec+Reveal" is subsumed by A). The two
hard A-specific problems and their designs:

**A-1. Semantic-accessor layer (replaces M's field projections).** M exists so the
state machine can read `ch.key_share`, `ch.cipher_suites`, `sh.cipher_suite`,
`ee.negotiated_alpn`, `cv.scheme`/`cv.signature`, `fin.verify_data` without walking
the wire grammar. Under A those fields live inside the generated records (often deep
in an extension list). Introduce a **new pure "semantic view" module** (e.g.
`TLS13.Wire.Generated.Semantics`) of total accessor functions over the generated
types — `clientHello_key_share : GCH.clientHello -> option x25519_public`,
`clientHello_cipher_suites`, `clientHello_server_name`, `clientHello_sig_algs`,
`serverHello_key_share`/`_cipher_suite`/`_selected_version` (navigating the
`if-then-else` ServerHello/HRR body), `ee_alpn`, etc. The state machine and
connection-state spec call these accessors where they used to read M fields. The
generated modules already emit per-field `accessor_*`/`clens_*` (e.g.
`accessor_request_op`); extension-list extraction is the bespoke part to write+prove.

**A-2. Transcript exactness without `body`.** M carries verbatim `body` bytes so the
transcript hash is byte-exact. Under A the parsed generated value carries no raw
bytes. Design: the **impl already holds the raw received network slice**, so it
hashes those bytes directly for the transcript and uses the parsed generated value
only for semantic decisions (this is how a real TLS stack works). At the *spec*
level, exactness is re-expressed via the generated **parse/serialize round-trip**
(`serialize (parse b) == b` on the covered grammar — the QuackyDucky parser is a
bijection on its language, incl. `default: opaque` unknown extensions and preserved
list order), so the `body`-based exactness lemmas are replaced by per-message
round-trip lemmas. Risk: any non-canonical input the peer sends must still be
covered by the generated grammar's opaque/echo arms — validate with interop.

---

## Phased plan (Option A — full replacement)

Ordering is **bottom-up** (leaf → semantic-view + message records + state stack →
codec → L → client → server) so each layer rests on already-migrated lower layers,
mirroring calc's spec-before-impl sequencing. Each phase is independently
`make verify`-gated and committed (per the established workflow), in the
devcontainer. Phases 2–4 are the spec re-architecting; 5–7 the impl; recommend
**client-first** within the impl to de-risk the pattern before the larger server.

### Phase 0 — Baseline & toolchain
- The generated codec already exists (`tls.qd.rfc` → `generated/`, with
  `make regen-generated/verify-generated/extract-generated`). Confirm a green
  baseline: `make verify` of the TLS client+server and the openssl-echo interop
  test, in the devcontainer (record the exact targets/time).
- Inventory `tls.qd.rfc` coverage vs the M/T types: confirm every M message + T
  enum has a generated counterpart (calc's Phase 1 is essentially **already done**).
  The semantic envelope `tls_message` (Handshake/AppData/Alert/CCS/KeyUpdate
  dispatch) and `tls_error` are message-layer, not wire — under A they are kept as
  small hand-written **dispatch/error** types (not part of the wire grammar), now
  wrapping generated payloads.

### Phase 1 — Extend `tls.qd.rfc` only if needed
- No new wire types expected. If a generated form is missing for anything the state
  machine needs structurally, add it; else skip. Gate: generated modules verify.

### Phase 2 — Replace the leaf/enum types (milestone C — clean wins first)
- Replace `TLS13.Types.{content_type, protocol_version, alert_description,
  cipher_suite, named_group, signature_scheme, extension_type, hostname}` with the
  generated enums (`ContentType`, …) across spec+impl. Handle the `nat`→`U16.t`
  unknown-payload change (the generated enums carry `U16.t`). This is broad-but-
  shallow (every `T.`-referencing module) and is the safest first slice of A.
  Gate: spec verifies, then ripple to impl.

### Phase 3 — Semantic-view layer + replace M message records + retarget the state stack
The largest, riskiest phase (see A-1/A-2 above). Sub-sequence:
- **3a. Semantic-view module** (`TLS13.Wire.Generated.Semantics`): total pure
  accessors over the generated records (key_share/cipher_suites/server_name/sig_algs
  from `clientHello`; cipher_suite/key_share/selected_version from `serverHello`'s
  if-then-else body; ALPN from `encryptedExtensions`; scheme/signature from
  `certificateVerify`; verify_data from `finished`). Verify in isolation.
- **3b. Replace `M.handshake_msg`/`tls_message` payloads with generated records**
  (e.g. `SendClientHello of GCH.clientHello`); delete the M record types. Keep a
  thin `tls_message` dispatch envelope + `tls_error` (Phase 0).
- **3c. Rewrite `TLS13.StateMachine`** (`step`, the event type) to branch on generated
  payloads and read fields via the 3a accessors instead of M record fields.
- **3d. Rewrite `TLS13.Spec.ConnectionState` + `TLS13.ConnectionLog` + `Transcript`**:
  store `option GCH.clientHello`/etc., re-express the layered-log predicates
  (`connection_view`, `connection_state_*_consistent`) over generated payloads, and
  re-found transcript exactness on the generated round-trip (A-2). This re-verifies
  the largest spec proofs (`ConnectionState` ~3.7K L).

### Phase 4 — Make the generated codec the spec; delete `TLS13.Wire.Spec` + Reveal
- Under A, `parse_tls_message`/`parse_record`/`serialize_*` collapse into: the
  generated `LP.parse`/`LP.serialize` for the payload (handshake already is —
  `TLS13.Wire.Spec.fst:823-829`) wrapped by the small `tls_message` content-type
  dispatch + record framing. There is **no M to bridge to**, so the entire
  **~10.7K-line `Wire.Spec` + Reveal/NonExact/RevealDecode/WireFormatLemmas layer is
  deleted** — the single highest-value deletion in the project. Re-prove the few
  framing facts the impl needs directly from the generated defs (consumers:
  `Impl.Parser`, `Impl.Serializer*`, `Impl.Client.FragmentBound`,
  `Impl.Parser.DecoderWF`).

### Phase 5 — Replace the L mirror with the generated copyful lowtypes
- Replace `TLS13.Impl.Messages` (L) with the generated `*_lowtype` + copyful
  `read_*`/`write_*` API (the calc copyful pattern, already used by
  `TLS13.Impl.Parser` via `GHS.read_handshake`). Re-express the `is_valid_*`
  ownership predicates in terms of the generated `vmatch`. Gate: `Impl.Parser` +
  `Impl.Serializer*` verify and **still extract** (the calc noextract-record lesson:
  use the copyful lowtype API, never materialize noextract records at runtime).

### Phase 6 — Client impl
- Retarget `TLS13.Impl.Client.Types`, `TLS13.Impl.Client`, and the client driver to
  the generated/derived types; keep the public entry points (`new_client`,
  `next_local_action`, `process_network_bytes`, `process_local_event`) and their
  contracts. Gate: client verifies + extracts.

### Phase 7 — Server impl (largest)
- Retarget the server stack — `Server.Types`, `Server.Send` (463 M-refs),
  `Server.Keys`, `Server.Network`, `Server.Auth/App/Setup/Schedule/Material`, and the
  `Server.Driver.*` modules — to the generated/derived types, keeping the `accept`/
  `process_*` entry points. This is the bulk of the impl work. Gate: server verifies
  + extracts.

### Phase 8 — Build, extraction, interop
- Update the top-level Makefile bundle (it already bundles
  `TLS13.Wire.Generated.*`); drop the deleted Wire.Spec/Reveal modules from the
  bundle. Re-run extraction and the **openssl-echo interop test** (client and server)
  as the end-to-end gate — the TLS analog of calc's `make test-c`.

### Phase 9 — Cleanup & docs
- Remove dead modules (Wire.Spec/Reveal/NonExact/RevealDecode, the old L mirror),
  update `TLS_DESIGN_AND_IMPL.md` / `TLS_SERVER_DESIGN_AND_IMPL.md` to the new
  source-of-truth architecture.

---

## Module impact map (where the work lands)
- **Delete (Option A):** `TLS13.Messages` + `TLS13.Types` message records (M),
  `TLS13.Impl.Messages` (L), and the entire `TLS13.Wire.Spec`(+`Reveal*`,`NonExact`,
  `RevealDecode`) + `TLS13.Spec.WireFormatLemmas` layer (~10.7K lines) — generated is
  the sole source of truth.
- **New (Option A):** `TLS13.Wire.Generated.Semantics` (pure accessor/"semantic view"
  layer, 3a); a small `tls_message` dispatch + `tls_error` envelope.
- **Retarget leaf types (Phase 2):** every `T.`-referencing module (broad, shallow).
- **Rewrite + re-verify (Phase 3):** `TLS13.StateMachine`, `TLS13.Spec.ConnectionState`
  (~3.7K L), `TLS13.ConnectionLog`, `TLS13.Transcript` — under A these are rewritten
  over generated payloads (accessors + round-trip exactness), the deepest proof work.
- **Heaviest impl (Phases 5–7):** `Impl.Parser` (6.6K L), `Impl.Serializer*` (~6K L
  total), `Impl.Server*` (`Server.fst` 3.3K, `Server.Send` 463 M-refs, `Server.Keys`,
  the drivers), `Impl.Client*`.

## Risks / scale
1. **Scale**: ~130K lines; this is a multi-month, multi-PR effort regardless of
   option. Sequence by the bottom-up phases; gate each with `make verify` + interop.
2. **Semantic-projection mismatch** (Option A): extension-list navigation + transcript
   exactness must be re-established; this re-opens proven connection-state proofs.
3. **Extraction (copyful)**: reuse the calc lesson — generated records are `noextract`;
   the impl must use the copyful `read_*`/`write_*` lowtype API to stay extractable.
4. **Connection-state proof churn**: the `connection_state_*_consistent` predicates are
   large and central; field-type changes (B) or shape changes (A) force re-verification.
5. **Interop**: the byte-exact transcript/record requirement must survive the codec
   swap; validate continuously with the openssl-echo test, not just `make verify`.

## Tooling
proof-copilot plugin for the proof-heavy phases (3–7): `fstarmcp`/`fstarverifier`
for incremental checking, `proofdebugging` for failures, and the `fstar-coder` agent
for the repetitive impl retargeting — as used successfully in the calc migration,
driven through the devcontainer.

## Decision points (confirm before implementing)
1. **Target scope — DECIDED: Option A** (full literal replacement; generated types
   everywhere, M/L and Wire.Spec/Reveal deleted). C (enums-first) is the recommended
   first slice / milestone toward A.
2. **Transcript exactness (A-2)**: rely on the generated parse/serialize round-trip +
   the impl hashing the raw received slice (recommended), vs keeping a verbatim
   `body` field (a partial retreat from full A).
3. **Client-first or server-first** for Phases 6–7 (client is lighter; server is the
   bulk). *Recommend client-first* to de-risk the pattern.
4. **Per-phase commit cadence** and which phases may land as intermediate
   (spec-verifies-but-impl-broken) commits, as in the calc migration.
4. **Per-phase commit cadence** and which phases may land as intermediate
   (spec-verifies-but-impl-broken) commits, as in the calc migration.
