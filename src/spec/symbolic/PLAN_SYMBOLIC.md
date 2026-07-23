# Symbolic Security Proof Plan for the TLS 1.3 1-RTT Profile

Status: **approved; Phase 7 complete; Phase 8 in progress**

This document is the review gate for the symbolic-security work. Until this
plan is approved, the only repository change in this workstream should be this
file. In particular, do not yet add the DY* dependency, change the build, or
create F* proof modules.

## 1. Objective

Build a machine-checked symbolic security proof for the server-authenticated
TLS 1.3 1-RTT profile implemented by this repository. The proof must be about
the existing pure TLS state machine and its canonical wire semantics, rather
than about a separate protocol model that only resembles the implementation.

The proof will use the extrinsic DY* core for:

- symbolic messages and ideal cryptographic constructors;
- explicit traces, freshness, state, protocol events, and corruption;
- attacker derivability;
- protocol-specific byte, state, event, and cryptographic invariants; and
- the theorem that attacker-known values must be publishable.

The existing TLS development remains authoritative for:

- legal endpoint transitions (`legal_connection_delta`);
- exact handshake and record serialization;
- transcript evolution;
- key-schedule computations;
- exact protected-record behavior (`canonical_wire_step`); and
- existing reachability, correspondence, and key-lineage results.

The central construction will be a multi-session **product semantics**. Each
honest transition advances a real TLS connection state and a symbolic shadow
of that state together. Erasing the symbolic components must yield an ordinary
execution of the existing TLS state machine.

## 2. Proof claims

The work should establish the following claims, in this order.

### 2.1 Foundational claims

1. **Concrete projection.** Every honest endpoint step in the product semantics
   is a `legal_connection_delta`; every honest wire receive/send is justified
   by `canonical_wire_step`.
2. **Per-session reachability.** Projecting any reachable product state onto
   any honest endpoint yields an existing TLS-reachable connection state.
3. **Concrete coverage.** Every concrete execution of the supported profile
   that satisfies the explicit cryptographic, freshness, and X.509 bridge
   premises lifts to a product execution whose concrete projection is the
   original execution.
4. **Trace invariant.** All reachable product traces satisfy the instantiated
   DY* trace invariant.
5. **Attacker closure.** Every attacker injection is derivable from the current
   DY* trace, and attacker steps preserve the trace invariant.

### 2.2 Authentication and agreement

At the point where an honest client verifies the server Finished message:

- either the selected server signing credential was compromised before the
  relevant CertificateVerify;
- or a server session using that credential produced the matching
  CertificateVerify and server Finished.

The matching sessions must agree on:

- the protocol version and supported profile;
- client and server randoms;
- client and server X25519 shares;
- cipher suite, group, and signature scheme;
- requested server name and authenticated leaf public key;
- the exact handshake transcript through server Finished;
- the shared secret and handshake traffic secrets; and
- the server Finished value.

The proof should be developed as a ladder:

1. server aliveness;
2. non-injective server agreement;
3. injective server agreement, using fresh session material; and
4. concrete transcript agreement via the canonical serializers.

At the point where an honest server verifies the client Finished message:

- there exists a client session, possibly adversarial, that possessed the
  matching client Finished key and produced the matching Finished value; and
- for an honest matching client, the two sessions agree on the complete
  transcript and traffic secrets.

This is **anonymous client key confirmation**, not named-client
authentication. The supported profile has no client certificate or other
client identity.

### 2.3 Secrecy and key separation

For honest matching sessions, prove secrecy of:

- the X25519 shared secret;
- client and server handshake traffic secrets;
- client and server handshake traffic keys;
- client and server application traffic secrets; and
- client and server application traffic keys.

Every secrecy theorem must state its exact compromise exceptions. In
particular:

- a client-side theorem allows prior compromise of the server signing
  credential, because that enables active server impersonation;
- either peer's ephemeral DH secret, or the live session state containing the
  derived secret, may expose the corresponding traffic secret;
- a server session initiated by the attacker is not claimed secret from that
  attacker merely because the server endpoint is honest; and
- the useful server-side specialization therefore assumes a matching honest
  client, or equivalently that the peer DH secret is not attacker-known.

Prove symbolic domain separation between:

- client and server handshake traffic secrets;
- handshake and application traffic secrets;
- client and server application traffic secrets;
- Finished keys and record keys; and
- record keys and record IVs.

This is initially a theorem about distinct DY constructors and distinct
HKDF labels/contexts. It must not be presented as a theorem that concrete
SHA-256 or HKDF outputs can never collide.

### 2.4 Protected records and application data

For protected handshake and application records, prove:

- accepted plaintext originated from an encryption under the matching traffic
  key, direction, epoch, sequence number, nonce, and additional data, unless
  that key was exposed;
- an attacker cannot alter a protected record into a different accepted
  plaintext without the relevant key;
- records from the opposite direction or epoch cannot be substituted;
- replay at a different sequence number is rejected in the symbolic model; and
- application plaintext remains secret while its traffic key remains secret.

These claims must be linked to exact raw TLS records through
`canonical_wire_step`, rather than proved only for an abstract message channel.

## 3. Supported profile

The initial theorem covers exactly:

- TLS 1.3;
- one full server-authenticated handshake;
- X25519 key exchange;
- `TLS_CHACHA20_POLY1305_SHA256`;
- SHA-256/HMAC-SHA-256/HKDF-SHA-256;
- RSA-PSS-RSAE-SHA256 CertificateVerify, matching the current RSA credential
  configuration;
- one ClientHello/ServerHello exchange;
- encrypted server Certificate, CertificateVerify, and Finished;
- encrypted client Finished;
- bidirectional application data after the handshake.

The following are out of scope for the first proof:

- PSK, session resumption, and binders;
- 0-RTT;
- HelloRetryRequest;
- client certificates and named-client authentication;
- post-handshake authentication;
- KeyUpdate and traffic-secret generations after generation zero;
- exporter and resumption master secret use;
- alternative cipher suites, groups, or signature schemes;
- certificate path-building algorithms, revocation, and PKI policy;
- forward secrecy, state erasure, and post-compromise security;
- denial of service, liveness, timing, traffic analysis, and side channels; and
- a computational reduction for the concrete cryptographic implementations.

The model and event vocabulary should leave room for these features, but no
generic framework should be built speculatively before the initial profile is
proved.

## 4. Attacker and compromise model

### 4.1 Network attacker

The attacker controls the network across arbitrarily many concurrent
sessions. It may:

- observe every sent record;
- delay, drop, reorder, duplicate, and replay records;
- route a record to any endpoint;
- construct and inject any DY-derivable value;
- start sessions in either role; and
- interleave all honest and attacker actions.

The network is a collection of attacker-visible raw/symbolic packet pairs, not
the single in-flight channel in `TLS13.System`.

An attacker delivery to an honest endpoint is accepted only if:

1. its symbolic component is DY-derivable;
2. its raw component is related to that symbolic component in the current
   execution; and
3. the existing TLS canonical wire/state-machine relation accepts the raw
   component.

### 4.2 Principals and sessions

- A DY principal identifies an endpoint owner.
- A fresh `state_id` identifies a connection attempt.
- A session identifier includes role and state identifier; randoms and key
  shares are agreement data, not the sole internal identifier.
- The server credential registry maps a server name and signature scheme to a
  public verification key and a labeled private signing key.
- Clients have no long-term authentication key in this profile.

### 4.3 Corruption classes

Model distinct labels and corruption events for:

- server long-term signing keys;
- certification/trust anchors, if CA compromise is included in the final
  X.509 bridge;
- client and server ephemeral X25519 private values;
- live handshake state;
- live application traffic-secret state; and
- individual traffic keys, if key-only compromise is needed separately from
  whole-session compromise.

Corruption reveals only the state covered by its label. In particular,
long-term signing-key compromise must not automatically reveal unrelated
ephemeral or traffic-key state.

### 4.4 Freshness

- Honest randoms, ephemeral X25519 private values, and RSA-PSS signing nonces
  are introduced by `RandGen` entries with role/session-specific usages.
- Freshness is trace-indexed; caller-provided concrete bytes are not silently
  assumed fresh.

## 5. Soundness boundary

### 5.1 No global concrete-to-symbolic function

Do not define a total function:

```text
Seq U8 -> DY.Core.bytes
```

Such a function would conflate equal concrete byte strings globally and would
silently require collision-freedom or injectivity of hashes, HKDF, AEAD, and
signatures.

Instead, use an execution-indexed relation:

```text
represents : product_trace -> concrete_bytes -> symbolic_bytes -> prop
```

and store the required witnesses in the symbolic shadow state and packet
records. The relation may associate the same concrete bytes with different
symbolic terms in different executions or contexts.

### 5.2 Product-semantics guarantee

Prove both directions:

```text
product_execution p
  ==> concrete_execution (erase p)

concrete_execution c /\ symbolically_realizable_execution c
  ==> exists p. product_execution p /\ erase p == c
```

Projection establishes that every modeled honest step is a real TLS step.
Conditional lifting establishes coverage: the symbolic model cannot silently
exclude a concrete behavior that satisfies the stated bridge premises.

`symbolically_realizable_execution` must independently spell out those
premises. Honest randomness must have fresh `RandGen` witnesses; X25519,
hashes, HKDF, signatures, Finished MACs, AEAD, and X.509 results must have the
expected symbolic witnesses; and concrete collisions or forgeries must not
invalidate those witnesses. It must not be defined circularly as merely
"there exists a product execution."

The implementation keeps structural product reachability separate from DY
security hygiene. `secure_product_step` combines a real `product_step` with
`trace_extension_hygienic`, which checks the DY entry invariant for exactly
the trace entries added by that step. `securely_realizable_execution` requires
the same explicit per-transition witnesses. It never assumes the invariant of
the post-state; `trace_extension_preserves_invariant` proves that result.

The authentication, secrecy, and record-security results must therefore be
exported both for product executions and, through lifting, for every concrete
execution satisfying `symbolically_realizable_execution`. This premise
embodies the ideal-cryptography boundary; the lifting theorem does not itself
constitute a computational proof.

A protocol-origin event produced by an honest transition is required to be
fresh in the pre-transition trace. This is an explicit realization condition,
not a field of `product_well_formed`. Initial traces contain no protocol-origin
events, and freshness is preserved inductively by every product step. Thus
injective agreement is a theorem of reachable executions rather than an
assumed global uniqueness property.

A future computational proof may discharge the realizability premises for
concrete implementations.

The documentation must not claim that a DY proof alone establishes
computational security of OpenSSL, HACL*, or the extracted TLS binary.

### 5.3 Exact public encodings

Public constants, lengths, labels, algorithm identifiers, record headers, and
serialized public fields may be represented as DY `Literal` values.

Structured transcripts are represented compositionally so that signatures,
Finished messages, and key derivation refer to the same symbolic transcript.
The relation to concrete bytes is proved using the existing exact serializers.

TLS record nonces are treated as public values, which is conservative and
appropriate for AEAD security. The product state still records that the
concrete nonce equals the TLS 1.3 static-IV/sequence-number computation, and
proves nonce non-reuse for each key, direction, and epoch. This avoids adding
an unsound symbolic approximation of XOR to DY*.

## 6. Symbolic vocabulary

### 6.1 Terms

Use the DY* constructors as follows:

| TLS value | DY representation |
| --- | --- |
| Public constants and encodings | `Literal` |
| Honest fresh random or private value | `Rand` |
| Concatenation/transcript structure | `Concat` |
| X25519 public share | `DhPub` |
| X25519 shared secret | `Dh` |
| Transcript hash | `Hash` |
| HKDF-Extract result | `KdfExtract` |
| HKDF-Expand-Label result | `KdfExpand` with exact labeled info term |
| Finished verify data | `Mac` |
| CertificateVerify | `Sign` |
| Protected record | `AeadEnc` |
| Server verification key | `Vk` |

Define TLS-specific smart constructors for:

- the profile/session context;
- the ordered handshake transcript;
- the CertificateVerify input;
- each HKDF-Expand-Label info value;
- client/server handshake traffic secrets;
- client/server application traffic secrets;
- Finished keys and verify data;
- record keys;
- public record nonces;
- protected record additional data; and
- structured application plaintext.

Each smart constructor needs shape, equality, label, usage, and
well-formedness lemmas. Exact label bytes must come from `TLS13.Keys`; the
symbolic layer must not duplicate them as unrelated strings.

The `HkdfLabel` info term is represented compositionally as its exact
output-length field, label-length field, `"tls13 "`-prefixed label from
`TLS13.Keys`, context-length field, and symbolic context. Phase 3 relates this
term to the concrete serializer without flattening the symbolic context into a
global concrete-byte-to-term function.

### 6.2 Usages

Instantiate `crypto_usages` with protocol-specific usages for:

- server RSA signing keys and signing nonces;
- client/server ephemeral X25519 private values;
- early, handshake, and master HKDF extract keys;
- each distinct HKDF expansion purpose;
- client/server Finished MAC keys;
- client/server handshake AEAD keys;
- client/server application AEAD keys; and
- any state value that must carry a compromise label.

Usage parameters should include role, session identifier, direction, epoch,
and generation where needed. Avoid a single undifferentiated `TrafficKey`
usage, because it makes key-separation and cross-direction authenticity harder
to state.

The DY* core assigns one fixed `KdfExpandKey` usage to every `KdfExtract`
node. Consequently, early, handshake, and master extract stages are
distinguished by their term lineage and TLS-specific stage descriptors, while
the customizable expansion usage assigns distinct client/server,
handshake/application, Finished, record-key, and record-IV usages. Wrapping an
extract in an artificial constructor merely to change its usage would not
model the concrete key schedule and is therefore rejected.

### 6.3 Protocol events

Define DY protocol events for at least:

- client session started;
- server session started;
- ClientHello sent/received;
- ServerHello sent/received;
- server CertificateVerify signed;
- client CertificateVerify accepted;
- server Finished sent;
- client server-Finished accepted;
- client Finished sent;
- server client-Finished accepted;
- handshake/application traffic secret installed;
- protected handshake/application record sent;
- protected handshake/application record accepted.

Event payloads use one canonical `session_context` containing all agreement
data. Event predicates then state origin and ordering facts without repeatedly
reconstructing that context.

## 7. Concrete/symbolic state relation

The symbolic shadow for one endpoint should record only security-relevant
information:

- principal, role, and session identifier;
- the concrete TLS connection state;
- symbolic client/server randoms and X25519 keys;
- symbolic transcript;
- authenticated server identity and signing key;
- symbolic key-schedule nodes;
- current write/read traffic keys, directions, epochs, and sequence numbers;
- live compromise labels;
- acceptance milestones.

Define `endpoint_refines` between this shadow and
`TLS13.Spec.StateMachine.connection_state`. It must cover every concrete field
used by a claimed theorem, including:

- transcript and transcript hashes;
- DH public/private/shared values;
- handshake/master/traffic secrets;
- record keys and IVs;
- certificate-validation result;
- CertificateVerify verification;
- Finished verification;
- read/write epoch and sequence number; and
- no-KeyUpdate profile restrictions.

For every honest transition, prove preservation of `endpoint_refines`.
Transition-specific lemmas should be small and follow the existing TLS event
boundaries rather than one monolithic automation-heavy proof.

## 8. Multi-session product semantics

The global product state contains:

- a finite map of session identifiers to endpoint shadows;
- the DY trace;
- attacker-visible packets;
- the credential/trust registry;
- the next fresh session identifier.

Define product steps for:

1. creating a fresh honest client session;
2. creating a fresh honest server session;
3. honest local randomness or cryptographic events;
4. honest canonical send;
5. attacker packet derivation/injection;
6. attacker delivery to an arbitrary endpoint;
7. honest canonical receive;
8. corruption of a specifically labeled live value;
9. record drop/reorder/replay bookkeeping.

Every honest send adds a `MsgSent` entry. Every honest state update adds the
minimal `SetState` summary needed by the security invariant. Security
milestones add protocol `Event` entries.

The product relation must not pair client and server sessions in advance. A
matching peer is discovered by authentication/agreement proofs from trace
events.

## 9. DY* invariant instantiation

### 9.1 Labels

Define labels so that:

- public handshake metadata is public;
- server signing keys depend on the server-credential corruption event;
- ephemeral secrets depend on their role/session corruption event;
- a DH shared secret depends on both DH-secret labels;
- derived traffic secrets inherit the relevant DH/session secrecy;
- Finished and traffic keys have distinct usages while preserving the required
  secrecy label.

Prove the required `can_flow` and label-join lemmas explicitly. Keep compromise
disjunctions visible in theorem statements rather than hiding them behind a
large opaque label.

### 9.2 Cryptographic predicates

Instantiate:

- `sign_pred` so an honest CertificateVerify signature implies the exact
  server event, credential, scheme, transcript, and context;
- `mac_pred` so an honest Finished MAC implies the correct role, transcript,
  and Finished key;
- `aead_pred` so an honest protected record binds direction, epoch, sequence
  number, AAD, plaintext kind, and send event; and
- no PKE predicate for the initial profile.

The `pred_later` obligations must be proved for trace extension without broad
automation or admitted facts.

### 9.3 State and event predicates

State predicates capture:

- ownership of fresh X25519 secrets;
- the key-schedule lineage of installed secrets;
- transcript evolution;
- accepted server identity;
- record sequence-number monotonicity.

Event predicates capture:

- required preceding events;
- origin of signatures, Finished values, and ciphertext;
- agreement-context consistency;
- freshness/injectivity of sessions; and
- acceptance only after the existing TLS checks.

The main invariant proof then shows preservation by every honest product step.
Attacker preservation should use the generic DY* attacker theorem rather than
reprove constructor closure.

## 10. Explicit bridge obligations

All unproved cryptographic or PKI statements must live in narrowly scoped,
clearly named symbolic bridge interfaces. Maintain a table in the source
documentation listing each assumption and the theorem that depends on it.

### 10.1 Freshness bridge

Relate concrete caller-provided random/private bytes to fresh `RandGen`
entries. Required obligations:

- correct lengths;
- no reuse within the modeled execution;
- role/session-specific usage; and
- independence from attacker-controlled inputs.

### 10.2 X25519 bridge

Relate:

- concrete public-key generation to `DhPub`;
- concrete shared-secret computation to symmetric `Dh`; and
- existing X25519 agreement lemmas to the product relation.

Do not postulate global injectivity of public keys or shared secrets.

### 10.3 Hash/HKDF/HMAC bridge

Relate concrete state-machine computations to `Hash`, `KdfExtract`,
`KdfExpand`, and `Mac` terms for this execution. Required obligations include:

- exact transcript input;
- exact TLS HKDF label encoding;
- exact context and output length;
- role/direction-specific key usage; and
- consistency with the concrete key-lineage theorems.

### 10.4 Signature bridge

Relate concrete RSA-PSS verification and server signing to `Vk` and `Sign`.
Required obligations:

- exact `Rsa_pss_rsae_sha256` scheme;
- exact CertificateVerify context and transcript hash;
- fresh signing nonce for honest signatures;
- selected leaf verification key; and
- signature-origin reasoning under the DY ideal-signature assumption.

### 10.5 X.509 identity bridge

Strengthen the current abstract chain-validation result enough to state:

- if an honest client accepts a chain for the requested server name, then the
  returned leaf public key is the verification key registered for that server,
  unless the relevant trust/credential authority is compromised.

This may be either:

- a registry-backed assumption for the first proof; or
- a theorem from a stronger `TLS13.X509.Spec` contract.

The first option is expected initially. It must be marked as trusted and must
not be confused with a proof of X.509 path validation.

### 10.6 AEAD bridge

Relate concrete ChaCha20-Poly1305 records to `AeadEnc` with:

- the exact key;
- the concrete TLS nonce, modeled as public;
- the exact five-byte record header/AAD;
- the exact inner plaintext; and
- the matching direction, epoch, and sequence number.

The DY authenticity result is an ideal AEAD assumption. Existing
open-after-seal correctness alone is not an authenticity theorem.

### 10.7 Authentication consumers and corruption labels

The Phase 6 concrete authentication theorems consume the bridge predicates
directly:

- `concrete_server_signature_bridge` connects the accepted X.509 leaf key,
  RSA-PSS CertificateVerify input and signature, trusted server registry, and
  exact pre-CertificateVerify transcript to symbolic signature verification;
- `concrete_finished_bridge` connects concrete HMAC-SHA256 computation and the
  exact pre-Finished transcript to symbolic Finished verification; and
- the transcript-evidence predicates connect the serialized
  CertificateVerify, server Finished, and client Finished messages to three
  distinct transcript checkpoints.

These are caller-provided, execution-local realizability obligations. The
authentication proof derives DY origin results from them; it does not prove
computational RSA-PSS, HMAC, or X.509 security.

Each authentication compromise exception uses the label stored on the exact
symbolic key used by the corresponding verification: the server credential
label for CertificateVerify, and the relevant role-specific handshake traffic
label for Finished. `DY.is_corrupt trace label` means that this labeled value
was exposed in the modeled trace. It does not imply compromise of unrelated
ephemeral, traffic, or peer state.

### 10.8 Key-schedule lineage and secrecy consumers

Phase 7 uses `complete_key_schedule_lineage` to bind an endpoint's represented
key-schedule fields to the exact TLS symbolic constructors at two historical
transcript checkpoints: the ServerHello transcript for handshake traffic
secrets and the server-Finished transcript for generation-zero application
traffic secrets. `schedule_target_matches` then identifies the particular
installed or derived secret named by a theorem. Both predicates are
load-bearing in `established_schedule_secret_secrecy`.

The caller must establish that the two ephemeral terms are the actual client
and server ephemeral secrets for the sessions, carry their role/session-specific
DH usages, and have the stated corruption labels. This is the execution-local
freshness and X25519 realization boundary; arbitrary representation bindings
alone do not establish it.

For a matching honest pair, attacker knowledge of any covered schedule secret
implies corruption of the client or server ephemeral label. The client-side
specialization permits server-credential compromise as the alternative to an
honest matching server. The server-side specialization explicitly requires the
honest-peer evidence; no secrecy is claimed for an attacker-chosen peer DH
share.

HKDF-derived terms inherit the symbolic label of their input secret under the
configured DY* KDF usage. Key separation is only constructor and exact-label
separation in the symbolic model. It is not a claim that concrete HKDF outputs
cannot collide.

## 11. Proposed module hierarchy

All new TLS proof modules live under `src/spec/symbolic`.

```text
src/spec/symbolic/
  PLAN_SYMBOLIC.md

  model/
    TLS13.Symbolic.Profile.fst
    TLS13.Symbolic.Terms.fst
    TLS13.Symbolic.Events.fst
    TLS13.Symbolic.Labels.fst
    TLS13.Symbolic.Usages.fst
    TLS13.Symbolic.Abstraction.fst
    TLS13.Symbolic.Endpoint.fst
    TLS13.Symbolic.Product.fst
    TLS13.Symbolic.Step.fst
    TLS13.Symbolic.Reachability.fst

  assumptions/
    TLS13.Symbolic.FreshnessBridge.fsti
    TLS13.Symbolic.CryptoBridge.fsti
    TLS13.Symbolic.X509Bridge.fsti

  invariants/
    TLS13.Symbolic.CryptoPredicates.fst
    TLS13.Symbolic.StatePredicates.fst
    TLS13.Symbolic.EventPredicates.fst
    TLS13.Symbolic.Invariant.fst
    TLS13.Symbolic.Preservation.fst

  projection/
    TLS13.Symbolic.Projection.fst
    TLS13.Symbolic.CanonicalWire.fst

  properties/
    TLS13.Symbolic.Properties.Context.fst
    TLS13.Symbolic.Properties.ServerAuthentication.fst
    TLS13.Symbolic.Properties.ClientKeyConfirmation.fst
    TLS13.Symbolic.Properties.TranscriptAgreement.fst
    TLS13.Symbolic.Properties.Secrecy.fst
    TLS13.Symbolic.Properties.KeySeparation.fst
    TLS13.Symbolic.Properties.RecordSecurity.fst
```

This is a target decomposition, not a requirement to create empty files.
Modules should be added only when a phase needs them. If two adjacent modules
remain small, combine them rather than preserving this hierarchy mechanically.

## 12. Dependency and build integration

The DY* fork is:

```text
https://github.com/nikswamy/dolev-yao-star-extrinsic
branch: fstar2-toolchain-upgrade
initial commit: b599e1fdca22a7fd97634320a7f882794fcbc28a
```

Add it as:

```text
third_party/dolev-yao-star-extrinsic
```

This follows the repository's existing `third_party` submodule convention.
The submodule must always be pinned to an exact reviewed commit. The initial
pin is `b599e1f`; any later DY-core change requires its own reviewed fork
commit followed by an explicit submodule-pin update.

The build must:

- verify only the Comparse-independent DY* core needed here;
- use the repository's F* `bfe600822` toolchain;
- verify the DY* core with Z3 4.15.3;
- verify all new `TLS13.Symbolic.*` modules with the repository default Z3
  4.13.3;
- avoid bringing the currently unported DY libraries/examples into the TLS
  dependency graph;
- cache DY* `.checked` files separately from ordinary TLS outputs;
- expose `verify-dy-core` and `verify-symbolic` targets;
- include symbolic verification in CI and in the final repository-wide
  verification gate; and
- preserve the existing TLS proof solver configuration.

The first integration commit must test whether F* can consume DY* core
`.checked` files produced with Z3 4.15.3 while the new TLS symbolic proofs use
Z3 4.13.3. If this checked-cache boundary is not reliable, stop and review the
integration design rather than silently moving the TLS symbolic files to
4.15.3.

Repository-wide migration to Z3 5.0 is a separate follow-up. It should migrate
the existing TLS proofs, the new symbolic proofs, and DY* together only after
the current two-solver build is stable. That migration requires clean-cache
verification, proof-query triage, and an atomic update of CI/toolchain
documentation; it is not a prerequisite for the initial symbolic proof.

No Comparse port is required for this project.

## 13. Incremental phases and review gates

Each phase ends in a reviewable commit. Do not combine dependency integration,
model design, and final security theorems into one change.

### Phase 0: Approve scope and plan

Purpose: agree on the exact claims and trust boundary before implementation.

- [x] Approve the server-authenticated RSA-PSS/X25519/ChaCha20 profile.
- [x] Approve the product-semantics architecture.
- [x] Approve the attacker and compromise model.
- [x] Approve the authentication and secrecy statements.
- [x] Approve the explicit bridge-assumption boundary.
- [x] Resolve the open decisions in Section 15.

Exit gate:

- [x] This plan is approved or updated from review feedback.

Commit boundary:

- `Plan the symbolic TLS security proof`

### Phase 1: Integrate the DY* core

Purpose: establish a reproducible dependency and build boundary without
protocol code.

- [x] Add the fork as a pinned recursive submodule under `third_party`.
- [x] Verify that the submodule commit is exactly the reviewed commit.
- [x] Add source/include lists for the DY* core only.
- [x] Add a separate DY* cache.
- [x] Add `verify-dy-core` using Z3 4.15.3.
- [x] Add an empty/minimal import smoke test for the TLS symbolic namespace.
- [x] Add `verify-symbolic` using Z3 4.13.3.
- [x] Wire both targets into CI.
- [x] Document how Z3 4.13.3 and 4.15.3 are located or installed.
- [x] Confirm clean recursive checkout works.
- [x] Confirm the existing non-symbolic verification and tests are unchanged.

Exit gate:

- [x] DY* core verifies from a clean checkout with F* `bfe600822` and Z3
      4.15.3.
- [x] The Z3 4.13.3 TLS build imports the Z3 4.15.3-checked DY* core without
      Comparse or DY* source re-verification.
- [x] Repository verification and tests pass with parallel Make.

Commit boundary:

- `Integrate the upgraded DY star core`

### Phase 2: Define the profile and symbolic vocabulary

Purpose: define the terms, usages, labels, events, and agreement context before
defining executions.

- [x] Define a decidable supported-profile predicate.
- [x] Define principal, role, direction, epoch, and session identifiers.
- [x] Define the canonical `session_context`.
- [x] Define TLS smart constructors over DY terms.
- [x] Reuse exact TLS key-schedule labels and encodings.
- [x] Define protocol-specific crypto usages.
- [x] Define corruption labels.
- [x] Define protocol event tags and payloads.
- [x] Prove constructor shape and discrimination lemmas.
- [x] Prove label and well-formedness lemmas.
- [x] Check whether any needed term cannot be represented soundly by the DY*
      core; do not add a constructor without a separate design review.

Exit gate:

- [x] Every value named in the target theorems has one documented symbolic
      representation.
- [x] No global concrete-byte-to-term function exists.
- [x] No cryptographic security claim is needed yet.

Commit boundary:

- `Define the symbolic TLS vocabulary`

### Phase 3: Define the abstraction and bridge interfaces

Purpose: make the trusted boundary explicit before it is used in proofs.

- [x] Define the execution-indexed `represents` relation.
- [x] Define representation rules for literals and exact concatenation.
- [x] Define transcript/serializer correspondence.
- [x] Add freshness bridge obligations.
- [x] Add X25519 bridge obligations.
- [x] Add hash/HKDF/HMAC bridge obligations.
- [x] Add RSA-PSS signature bridge obligations.
- [x] Add X.509 identity bridge obligations.
- [x] Add AEAD/canonical-record bridge obligations.
- [x] Add a machine-readable or source-adjacent assumption ledger.
- [x] Prove that the relation does not require global primitive injectivity.

Exit gate:

- [x] Every `assume`, abstract `val`, or interface-only security fact is listed
      in the assumption ledger with its consumers.
- [x] Concrete correctness lemmas are reused where they suffice.
- [x] Security properties are not derived from correctness-only lemmas.

Commit boundary:

- `Define the TLS symbolic abstraction boundary`

### Phase 4: Build product semantics and projection

Purpose: connect DY traces to real TLS state-machine executions.

- [x] Define endpoint symbolic shadows.
- [x] Define `endpoint_refines`.
- [x] Define the global multi-session product state.
- [x] Define session creation and honest local steps.
- [x] Define honest canonical send/receive steps.
- [x] Define attacker knowledge, injection, routing, drop, and replay steps.
- [x] Define corruption steps.
- [x] Prove refinement preservation for every honest TLS event.
- [x] Prove every honest state transition is a
      `legal_connection_delta`.
- [x] Prove every honest raw record transition is a
      `canonical_wire_step`.
- [x] Prove per-session projection to existing reachability.
- [x] Prove stepwise lifting from every symbolically realizable concrete
      transition.
- [x] Prove the concrete-to-product lifting theorem for complete executions.

Exit gate:

- [x] An active attacker can drive arbitrarily interleaved sessions.
- [x] No honest step bypasses the existing state machine.
- [x] Product reachability projects to ordinary TLS reachability.
- [x] Every concrete execution satisfying the bridge premises has a product
      execution with exactly that concrete projection.

Commit boundary:

- `Relate symbolic executions to the TLS state machine`

This is the first major theorem and a mandatory review point before security
properties.

### Phase 5: Instantiate and preserve the DY invariant

Purpose: prove the global invariant from which origin and secrecy results
follow.

- [x] Instantiate `crypto_invariants`.
- [x] Implement the signature predicate and monotonicity proof.
- [x] Implement the Finished MAC predicate and monotonicity proof.
- [x] Implement handshake/application AEAD predicates and monotonicity proofs.
- [x] Implement state predicates.
- [x] Implement event predicates.
- [x] Prove invariant preservation for each endpoint transition.
- [x] Prove invariant preservation for session creation.
- [x] Prove invariant preservation for corruption.
- [x] Reuse DY* attacker-preservation results for attacker steps.
- [x] Prove reachable product traces satisfy `trace_invariant`.
- [x] Prove local origin lemmas for signature, Finished, and AEAD terms.

Exit gate:

- [x] All secure product steps preserve the trace invariant.
- [x] `attacker_only_knows_publishable_values` applies to every reachable secure
      product trace.
- [x] There are no admitted lemmas or undocumented assumptions.

Commit boundary:

- `Prove the symbolic TLS trace invariant`

### Phase 6: Prove authentication and transcript agreement

Purpose: obtain the primary handshake authentication result.

- [x] Define client and server acceptance predicates from concrete TLS fields.
- [x] Prove server-signature origin.
- [x] Prove server-Finished origin.
- [x] Prove client server-aliveness.
- [x] Prove non-injective server agreement.
- [x] Prove injective server agreement from session freshness.
- [x] Prove exact transcript agreement through server Finished.
- [x] Prove client-Finished origin.
- [x] Prove anonymous client key confirmation.
- [x] Prove honest-client/full-session transcript agreement.
- [x] State all credential/trust compromise exceptions over the correct trace
      prefix.
- [x] Derive origin-event uniqueness from an origin-free initial trace and
      fresh honest event emission, rather than assuming uniqueness in product
      well-formedness.
- [x] Make concrete X.509, RSA-PSS, and HMAC bridge evidence load-bearing in
      the concrete authentication theorems.

Exit gate:

- [x] Client acceptance authenticates the configured server identity or reports
      the precise compromise exception.
- [x] Server acceptance claims only anonymous key confirmation.
- [x] Agreement covers exact serialized transcripts, not just key equality.

Commit boundary:

- `Prove TLS server authentication and agreement`

### Phase 7: Prove handshake and traffic-key secrecy

Purpose: show that established secrets are not DY-derivable without the stated
compromise.

- [x] Prove DH shared-secret label/origin lemmas.
- [x] Prove handshake-secret secrecy.
- [x] Prove both handshake traffic-secret secrecy results.
- [x] Prove Finished-key secrecy.
- [x] Prove master-secret secrecy.
- [x] Prove both generation-zero application traffic-secret secrecy results.
- [x] Prove record-key secrecy.
- [x] State the server-side honest-peer precondition explicitly.
- [x] Specialize general public-label results to corruption disjunctions for
      honest peers.
- [x] Prove symbolic key separation for all listed purposes/directions.
- [x] Document that symbolic separation is not concrete collision-freedom.

Exit gate:

- [x] Every target secret has a theorem with explicit, minimal compromise
      exceptions.
- [x] No theorem accidentally authenticates an unnamed client.

Commit boundary:

- `Prove TLS traffic-secret secrecy and separation`

### Phase 8: Prove protected-record and application-data security

Purpose: connect the key results to exact handshake and application records.

- [ ] Define structured symbolic plaintext for protected records.
- [ ] Prove key/direction/epoch/sequence correspondence.
- [ ] Prove per-key nonce non-reuse.
- [ ] Prove protected-handshake-record origin.
- [ ] Prove application-record origin and integrity.
- [ ] Prove cross-direction and cross-epoch substitution rejection.
- [ ] Prove replay rejection at an advanced sequence number.
- [ ] Prove application-plaintext secrecy under an uncompromised traffic key.
- [ ] Connect every theorem to `canonical_wire_step`.
- [ ] Reuse existing protected-wire and segmentation lemmas where applicable.

Exit gate:

- [ ] Claims apply to exact accepted raw records.
- [ ] Confidentiality and integrity exceptions mention the relevant live key,
      not an unrelated long-term key.

Commit boundary:

- `Prove TLS protected-record security`

### Phase 9: Harden, document, and complete CI

Purpose: make the proof maintainable and its claims auditable.

- [ ] Add a short security-model document linked from the repository README.
- [ ] Publish the final assumption ledger.
- [ ] Map each headline claim to its F* theorem name.
- [ ] Document excluded TLS features.
- [ ] Document the symbolic-versus-computational distinction.
- [ ] Add targeted verification targets per proof layer.
- [ ] Bound and document exceptional SMT resource settings.
- [ ] Run proof-stability repetitions from clean caches.
- [ ] Run the full repository verification and test targets.
- [ ] Confirm recursive-submodule CI from a clean checkout.
- [ ] Confirm no untracked local DY* clone is required.

Exit gate:

- [ ] All symbolic modules verify from a clean checkout.
- [ ] Full repository verification and tests pass.
- [ ] No admitted theorem, hidden assumption, or unreviewed dependency revision
      remains.

Commit boundary:

- `Document and stabilize the symbolic TLS proof`

## 14. Verification and proof-quality policy

For every phase:

- use the smallest target that verifies the changed modules;
- also run the dependency layer beneath it;
- use parallel Make (`-j$(nproc)`, or `-j128` on the current host);
- preserve a clean-cache command for CI reproduction;
- do not use `--admit_smt_queries`, `assume` in implementation modules, or
  blanket `--z3rlimit 0`;
- keep local SMT options near the theorem that needs them;
- prefer explicit intermediate lemmas to fragile assertion sequences;
- record any unavoidable high-resource query and why it is stable; and
- repeat the final symbolic verification from a clean cache enough times to
  detect solver instability.

Final completion commands must include the repository's ordinary verification
and test targets as well as the 4.15.3 DY* and 4.13.3 symbolic targets. The
exact commands will be fixed during Phase 1 after the two-solver cache strategy
is tested.

## 15. Approved design decisions

1. **X.509 compromise scope.**
   - Use a trusted registry that binds a server name to its leaf verification
     key.
   - Model server-credential corruption, but defer CA/trust-anchor compromise
     and detailed PKI compromise.

2. **Static IV classification.**
   - Conservatively classify record IVs/nonces as public while keeping traffic
     keys secret and proving nonce uniqueness.

3. **Application plaintext source.**
   - Honest application input is opaque and secret by default, under a
     session/application-specific label.
   - The initial model does not tag honest application data as public.
   - Attacker-known input is represented separately as attacker-controlled
     data and is excluded by the premise of the confidentiality theorem,
     rather than relabeling honest data as public.
   - Record-origin and integrity theorems remain independent of the
     plaintext-secrecy premise.

4. **DY* core extensions.**
   - Do not extend the core for TLS nonce XOR; use public concrete nonce
     literals plus a nonce-uniqueness invariant.
   - Any genuinely necessary new constructor must be implemented and reviewed
     in the fork first, then pinned by a separate submodule update.

## 16. Stretch goal: forward secrecy

Forward secrecy is not part of the initial proof, its completion criteria, or
its CI gate. If the core authentication, agreement, secrecy, and record
security results are complete and stable, a later workstream may add it.

That extension would require:

- explicit transitions for retiring handshake and application traffic keys;
- erasure events with precise trace positions;
- a proof that erased values are absent from later corruptible state;
- separate pre-erasure and post-erasure compromise cases; and
- a clear distinction between symbolic erasure and physical erasure in the
  extracted implementation.

The target stretch theorem would state that compromise of only the server's
long-term signing key after session-key erasure does not reveal past session
traffic secrets or application plaintext. It should be planned and reviewed
separately before adding lifecycle state to the core symbolic model.

## 17. Risks and mitigations

| Risk | Mitigation |
| --- | --- |
| The symbolic model drifts from the TLS state machine | Require every honest step to carry `legal_connection_delta` or `canonical_wire_step`; prove projection first. |
| The product model omits a relevant concrete execution | Prove conditional lifting for every concrete execution satisfying an independently defined realizability predicate. |
| Concrete bytes are globally identified with symbolic terms | Use execution-indexed relational witnesses; prohibit a total abstraction function. |
| X.509 validation is too weak for named-server authentication | Add a narrow, explicit registry/validation bridge and expose it in every affected theorem. |
| Caller-provided randomness is treated as fresh without justification | Require `RandGen` witnesses through a freshness bridge. |
| Server secrecy is overclaimed for attacker-initiated sessions | State an honest-peer or non-public-peer-DH condition and prove the general label theorem first. |
| Anonymous client confirmation is described as client authentication | Use separate event/theorem names and never attach a client identity to server acceptance. |
| AEAD correctness is mistaken for authenticity | Use DY AEAD origin predicates and label the ideal-AEAD bridge explicitly. |
| Record nonce modeling is unsound | Treat concrete nonces as public and prove exact computation plus per-key uniqueness. |
| Symbolic key separation is mistaken for concrete non-collision | Keep theorem statements in the symbolic domain and document the computational gap. |
| Multi-session proof causes SMT blowups | Use small transition lemmas, event summaries, opaque boundaries, and staged property modules. |
| Mixed Z3 caches cause accidental DY* re-verification | Keep DY* on an explicit 4.15.3 cache and require the 4.13.3 symbolic target to consume only its checked artifacts. |
| Repository-wide Z3 5.0 migration destabilizes proofs | Treat it as a separate atomic migration with clean-cache verification and query-by-query triage. |
| The fork's unported examples expand project scope | Depend only on the verified Comparse-independent core. |

## 18. Definition of done

The symbolic-security work is complete only when:

- [ ] the DY* core is pinned, reproducible, and license-preserving;
- [ ] every honest product execution projects to the existing TLS state
      machine and canonical wire semantics;
- [ ] every concrete execution satisfying the explicit bridge premises lifts
      to a product execution with the same concrete projection;
- [ ] the instantiated DY trace invariant is proved for all honest, attacker,
      and corruption steps;
- [ ] server authentication and transcript agreement are proved with exact
      compromise exceptions;
- [ ] anonymous client key confirmation is proved without overclaiming client
      identity;
- [ ] handshake/application secret secrecy and symbolic key separation are
      proved;
- [ ] protected-record authenticity/confidentiality is tied to exact raw
      records;
- [ ] every trusted bridge assumption is documented and narrowly scoped;
- [ ] no theorem depends on global injectivity of concrete cryptography;
- [ ] all proof modules verify reproducibly in CI; and
- [ ] the ordinary repository verification and tests still pass.
