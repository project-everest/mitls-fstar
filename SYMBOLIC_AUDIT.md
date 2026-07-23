# Audit guide for the TLS 1.3 symbolic proof

This document is a skeptical-reader's guide to the symbolic TLS proof under
`src/spec/symbolic`. It explains what is machine checked, what is supplied as a
realization or hygiene premise, what is trusted, and what is deliberately not
claimed.

The short model summary is
[`src/spec/symbolic/SECURITY_MODEL.md`](src/spec/symbolic/SECURITY_MODEL.md).
The phased design and approved scope are in
[`src/spec/symbolic/PLAN_SYMBOLIC.md`](src/spec/symbolic/PLAN_SYMBOLIC.md).
This document is intentionally more critical than either: it is organized
around the places where an apparently strong symbolic result can become weak,
vacuous, or easy to overstate.

## 1. Executive assessment

The proof establishes nontrivial, machine-checked symbolic implications for the
supported TLS 1.3 profile:

1. A product execution projects exactly to the existing concrete TLS state
   machine.
2. A concrete execution with explicit symbolic-realization witnesses lifts to a
   product execution whose concrete projection is exact.
3. A DY trace invariant is preserved across product steps whose newly appended
   entries satisfy the stated hygiene condition.
4. Signature, Finished, and AEAD verification yield matching honest origin
   events or explicit compromise alternatives.
5. Knowledge of covered key-schedule secrets implies corruption of one of the
   supplied labels attached to the two symbolic ephemeral terms. Interpreting
   those labels as endpoint ephemeral-state compromise requires a separate tie
   to the intended non-public principal-state labels.
6. Accepted records under a non-publishable live AEAD key have a matching sent
   origin fixing the accepted direction, epoch, sequence token, nonce,
   plaintext, AAD, and key.
7. Symbolic nonce freshness, replay rejection, direction/epoch substitution
   rejection, application-data labeling, and canonical record linkage are
   proved for the modeled record transitions.

These are **conditional symbolic-security theorems**. They are not a
computational reduction for HACL*, OpenSSL, or ChaCha20-Poly1305, and they are
not by themselves a refinement theorem from the extracted C program to the
symbolic model.

The most important qualification is concrete coverage:

```text
concrete_execution
/\ symbolically_realizable_execution
==>
exists product_execution with exact concrete projection
```

The proof does not derive `symbolically_realizable_execution` for every legal
concrete execution. That predicate contains product well-formedness, endpoint
refinement, representation extension, network/event realization, and exact
AEAD record witnesses where records are involved. It does **not** contain the
defined freshness, X25519, hash, or HKDF bridge predicates, and the
signature/HMAC/X.509 predicates are separate authentication premises. The
approved proof plan states the intended boundary at
`src/spec/symbolic/PLAN_SYMBOLIC.md:265-312`.

### Defensible one-sentence claim

> For the fixed TLS 1.3 profile, every concrete state-machine execution that
> supplies the explicit symbolic-realization and trace-hygiene evidence has an
> exact product execution; in secure reachable product executions, the proved
> authentication, secrecy, and record-security conclusions follow under the
> stated compromise alternatives and ideal-DY assumptions.

Any stronger sentence needs additional theorems identified in
[Section 16](#16-high-value-strengthening-work).

## 2. Claim taxonomy

Use this table before citing a theorem.

| Claim | Status | Load-bearing qualification |
| --- | --- | --- |
| Product steps are real TLS steps | Proved | Projection is to the existing concrete state-machine relation |
| Every concrete behavior is modeled | Conditional | Only executions satisfying `symbolically_realizable_execution` lift |
| The final DY trace is secure | Conditional | Initial invariant and per-step `trace_extension_hygienic` are required |
| Client authenticates a named server | Proved under premises | Requires concrete acceptance evidence, registry identity, signature bridge, Finished bridge, and trace invariant |
| Server authenticates a client identity | Not claimed | The client is anonymous; only client Finished key confirmation is proved |
| Full-session agreement | Proved under premises | The three origin contexts are existential; context equality is not concluded |
| Injective agreement | Event-level result | Uniqueness is for an exact origin event, not an injective map from acceptances to sessions |
| Traffic-secret secrecy | Symbolically proved | Requires complete symbolic lineage, caller-supplied term labels/usages, target matching, and trace invariant; endpoint-state labels are not forced |
| Key separation | Symbolically proved | Free-constructor disequality, not concrete HKDF non-collision |
| Accepted-record integrity | Symbolically proved | Requires exact realization, invariant evidence, usage match, and non-publishable key |
| Replay rejection | Symbolically proved after sequence advance | Sequence inequality is a premise |
| Application confidentiality | Label-based symbolic result | Knowledge implies corruption of the owning application-state label |
| Concrete cryptographic security | Not proved | AEAD is connected through record realization and signature/HMAC/X.509 through authentication premises; freshness, X25519, hash, and HKDF bridge predicates are defined but not consumed by the headline chain |
| Extracted-C symbolic security | Not proved here | Requires a separate implementation-refinement and computational argument |

## 3. Exact supported scope

The profile is fixed in `TLS13.Symbolic.Profile`:

- TLS 1.3 1-RTT;
- X25519;
- RSA-PSS-RSAE-SHA256 server authentication;
- SHA-256, HMAC-SHA256, and HKDF-SHA256;
- TLS_CHACHA20_POLY1305_SHA256;
- both client and server roles;
- protected handshake records;
- generation-zero application traffic;
- bidirectional and segmented application-data sends.

The profile recognizers and configuration-pair predicate are at
`src/spec/symbolic/TLS13.Symbolic.Profile.fst:6-67`. Product refinement applies
the individual client or server profile predicate through
`config_matches_role`; `config_pair_in_profile`, including its SNI-compatibility
clause, is defined but not consumed by the current product proof. The profile
module does not prove that an arbitrary configuration belongs to it.

The proof excludes:

- PSK, resumption, and 0-RTT;
- HelloRetryRequest;
- client certificates and post-handshake authentication;
- KeyUpdate and later traffic-secret generations;
- exporters and alternate algorithms;
- full certificate path construction, revocation, and WebPKI policy;
- forward secrecy and post-compromise security;
- liveness, availability, traffic analysis, timing, and side channels;
- probabilistic or computational reductions;
- a direct end-to-end theorem about extracted C.

These exclusions are semantic, not merely missing tests. A reviewer should
reject attempts to generalize a theorem beyond this profile.

## 4. Architecture and recommended reading order

The proof is extrinsic: it leaves the existing concrete TLS specification
authoritative and adds a symbolic execution alongside it.

```text
Concrete TLS state machine and canonical wire semantics
                         |
                         | execution-local Bridge predicates
                         v
Profile / Terms / Usages / Labels / Events / Lemmas
                         |
                         v
              Product transition system
      concrete state + symbolic shadow + DY trace
                         |
                         v
                  DY trace invariant
                         |
             +-----------+-----------+
             |           |           |
      Authentication   Secrecy   RecordSecurity
```

Read the modules in this order:

| Layer | File | Audit purpose |
| --- | --- | --- |
| Scope | `TLS13.Symbolic.Profile.fst` | Confirm the exact algorithm and configuration profile |
| Vocabulary | `TLS13.Symbolic.Terms.fst` | Check that TLS values have the intended DY shape |
| Domains | `TLS13.Symbolic.Usages.fst` | Check role, direction, epoch, and purpose separation |
| Compromise | `TLS13.Symbolic.Labels.fst` | Identify exactly which state corruption discharges secrecy |
| Events | `TLS13.Symbolic.Events.fst` | Check event payloads and tag separation |
| Structural facts | `TLS13.Symbolic.Lemmas.fst` | Separate constructor facts from protocol facts |
| Abstraction boundary | `TLS13.Symbolic.Bridge.fst` | Audit all concrete-to-symbolic assumptions |
| Execution model | `TLS13.Symbolic.Product.fst` | Audit projection, lifting, attacker actions, and event generation |
| Security invariant | `TLS13.Symbolic.Invariant.fst` | Audit origin predicates and preservation premises |
| Authentication | `TLS13.Symbolic.Authentication.fst` | Audit acceptance-to-origin and compromise alternatives |
| Secrecy | `TLS13.Symbolic.Secrecy.fst` | Audit key lineage, labels, and symbolic separation |
| Records | `TLS13.Symbolic.RecordSecurity.fst` | Audit nonce, AEAD origin, replay, and application-data claims |

`TLS13.Symbolic.Import.fst` imports the complete stack. The Makefile generates a
separate `.depend-symbolic` graph and makes `verify-symbolic` check every source
under `src/spec/symbolic` with the DY*/TLS symbolic toolchain.

## 5. Concrete specification crosswalk

The symbolic proof must be checked against the concrete definitions it claims
to model.

| Concrete source | Audit target |
| --- | --- |
| `src/spec/core/TLS13.Spec.StateMachine.fst` | Configurations, connection states, acceptance flags, key installation, verification steps, and `legal_connection_delta` |
| `src/spec/core/TLS13.Spec.StateMachine.Canonical.fst` | Exact send/open behavior and `canonical_wire_step` |
| `src/spec/core/TLS13.Record.Spec.fst` | TLS nonce computation, AEAD seal/open, and sequence update |
| `src/spec/core/TLS13.Keys.fst` | Key schedule, TLS labels, Finished data, record keys, and IVs |
| `src/spec/core/TLS13.Handshake.Spec.fst` | CertificateVerify and Finished input formats |
| `src/spec/core/TLS13.Wire.Semantics.fst` | CertificateVerify signature and Finished verify-data projections |
| `src/spec/core/TLS13.Wire.Spec.fst` | Record, inner-plaintext, and handshake-message parsers |
| `src/spec/assumptions/TLS13.Crypto.Spec.fsti` | Abstract concrete crypto interface |
| `src/spec/assumptions/TLS13.X509.Spec.fsti` | Abstract X.509 identity/leaf-key interface |

The canonical record path is particularly important:

- plaintext and five-byte AAD construction:
  `TLS13.Spec.StateMachine.Canonical.fst:32-46`;
- protected send:
  `TLS13.Spec.StateMachine.Canonical.fst:48-109`;
- receive, open, and parse:
  `TLS13.Spec.StateMachine.Canonical.fst:140-187`;
- canonical transition:
  `TLS13.Spec.StateMachine.Canonical.fst:189-212`;
- concrete nonce and record state:
  `TLS13.Record.Spec.fst:33-60`.

An audit should compare these definitions field by field with the realization
predicates discussed in [Section 8](#8-protected-record-security).

## 6. Symbolic vocabulary: what syntax proves and what it does not

### 6.1 Terms

`TLS13.Symbolic.Terms` defines:

- endpoint/session and in-profile context types at lines 11-41;
- freshness and X25519 terms at lines 43-56;
- transcript and CertificateVerify terms at lines 58-82;
- exact symbolic HKDF-label structure at lines 84-114;
- the TLS key schedule at lines 116-177;
- record sequence tokens and nonces at lines 179-226;
- AEAD records, AAD, and application plaintext at lines 228-255;
- public encodings and verification keys at lines 257-318.

Constructor equality is symbolic syntax. For example,
`client_application_traffic_secret inputs` and
`server_application_traffic_secret inputs` are distinct because their
constructor inputs differ. This is useful domain separation, but it is not a
claim that concrete HKDF outputs cannot collide.

### 6.2 Usages

`TLS13.Symbolic.Usages.fst:82-185` maps exact `HkdfLabel` shapes to
role-, direction-, epoch-, and purpose-specific usages and installs the
`DY.crypto_usages` instance.

Audit questions:

1. Does every security theorem use the intended usage, rather than only a term
   with the right byte length?
2. Are client/server and handshake/application purposes distinct?
3. Does usage equality merely identify a shape, or is the proof also showing
   ownership and correct installation?

The third question is essential: a usage shape is not an authentication result.

### 6.3 Labels

`TLS13.Symbolic.Labels.fst:6-53` defines intended principal-state labels for
credentials, ephemeral state, handshake/application state, and traffic
material. Shared-secret labels join the two intended ephemeral labels.

The headline secrecy contracts do not require the supplied `client_label` and
`server_label` to equal these intended label constructors. They require only
that the symbolic ephemeral terms have the supplied labels and expected usages.
Consequently, the formal conclusion is:

```text
supplied client label is corrupt
\/ supplied server label is corrupt
```

This can be interpreted as endpoint ephemeral-state compromise only after the
caller establishes that both supplied labels are the intended non-public
`Labels.ephemeral_key_label` values for the endpoint sessions. Without that
tie, the labels may be public or otherwise unrelated to endpoint state. Even
with it, the result does not establish forward secrecy after erasure, because
erasure and time-indexed compromise are not modeled.

### 6.4 Events and structural lemmas

Event kinds, distinct tags, record direction/epoch encodings, and event payloads
are defined in `TLS13.Symbolic.Events.fst:7-127`.

Structural lemmas in `TLS13.Symbolic.Lemmas.fst` prove facts such as:

- symbolic X25519 commutativity;
- constructor shape and well-formedness decomposition;
- label calculations;
- disjointness of AEAD and signature constructors;
- injectivity of event tags.

Do not confuse these with causal protocol results. An `Event` constructor is
not evidence that an event happened; occurrence requires a disciplined trace,
and origin requires the invariant.

## 7. The main audit boundary: `Bridge.represents`

### 7.1 Representation semantics

The representation state and relation are defined in
`TLS13.Symbolic.Bridge.fst:16-59`.

`represents execution concrete symbolic` has three cases:

1. `DY.Literal value` requires exact concrete equality:

   ```text
   concrete == value
   ```

2. `DY.Concat left right` requires a concrete split representing both parts.
3. Every other symbolic constructor requires an explicit execution-local
   `(concrete, symbolic)` binding.

This design avoids a global parser from concrete bytes to symbolic terms and
allows the same concrete bytes to have different symbolic meanings in different
executions or contexts.

It is also a major audit surface. The relation is not globally functional:

- one concrete value need not have one symbolic term;
- one symbolic term need not have one concrete value;
- additional bindings may give one concrete byte string multiple symbolic
  interpretations;
- an explicit binding alone does not prove a term's usage, label, or trace
  occurrence.

Review every consumer to ensure it carries the needed shape, usage, label, and
origin evidence in addition to `represents`.

### 7.2 Primitive bridge predicates

The concrete-to-symbolic predicates are:

| Boundary | Source |
| --- | --- |
| Honest fresh value and `RandGen` entry | `Bridge.fst:174-187` |
| X25519 public/shared computation | `Bridge.fst:189-215` |
| SHA-256 | `Bridge.fst:217-226` |
| HKDF-Extract and HKDF-Expand-Label | `Bridge.fst:228-268` |
| HMAC-SHA256 | `Bridge.fst:270-280` |
| RSA-PSS signature and concrete verification | `Bridge.fst:282-302` |
| Trusted server registry and leaf-key identity | `Bridge.fst:304-334` |
| AEAD seal/open | `Bridge.fst:336-379` |
| Packaged canonical record bridge | `Bridge.fst:381-393` |

The X.509 bridge is registry backed. It is not a proof of certificate path
building, revocation, name-policy completeness, or WebPKI.

Connectivity matters as much as definition:

- `aead_seal_bridge` and `aead_open_bridge` are consumed by Product record
  realization;
- `signature_bridge`, `hmac_bridge`, and `x509_identity_bridge` are consumed by
  the explicit authentication bridge premises;
- `fresh_value_bridge`, both X25519 bridges, `hash_bridge`, and both HKDF
  bridges currently have no consumer outside `Bridge.fst`.

The last group therefore documents an intended abstraction boundary but does
not currently connect concrete freshness, DH, transcript hashing, or HKDF
computations to the headline product/secrecy theorems.

### 7.3 Bridge audit checklist

For each use of a bridge predicate, check:

- the exact concrete input, not merely an equal-length value;
- the exact transcript checkpoint;
- the exact TLS HKDF label, context, and output length;
- role, session, direction, epoch, and generation;
- key usage and compromise label;
- concrete verification success where relevant;
- extension of existing bindings without losing old evidence;
- consistency if the same concrete bytes occur in multiple roles.

A skeptic should treat bridge predicates as the computational/abstraction
boundary, not as consequences of DY verification.

## 8. Product semantics and concrete coverage

### 8.1 State and refinement

`TLS13.Symbolic.Product` combines concrete states, symbolic endpoint shadows, a
DY trace, representation bindings, a symbolic network, and attacker/corruption
actions.

Key regions are:

| Area | Source |
| --- | --- |
| Concrete transitions and executions | `Product.fst:49-102` |
| Endpoint shadows and traffic material | `Product.fst:105-370` |
| Product/network state and well-formedness | `Product.fst:441-721` |
| Sent/accepted record witnesses | `Product.fst:758-1131` |
| Protocol-event realization | `Product.fst:1134-1438` |
| Honest network/trace delta | `Product.fst:1440-1483` |
| Actions and `product_step` | `Product.fst:1498-1704` |
| Event uniqueness | `Product.fst:1728-1989` |
| Projection and realization obligations | `Product.fst:1991-2178` |
| Realizable executions and lifting | `Product.fst:2180-2301` |
| Reachability projection | `Product.fst:2419-2440` |

`endpoint_refines` at `Product.fst:312-370` ties a shadow to:

- its concrete initial state and legal history;
- concrete reachability;
- represented transcript and traffic material;
- expected read/write direction;
- leaf-key representation;
- CertificateVerify and Finished flags;
- exclusion of KeyUpdate history.

### 8.2 Projection

`transition_projects_exactly` at `Product.fst:1991-2010` preserves the exact
concrete before/after states, semantic event, sent bytes, and received bytes of
one lifted transition. `execution_projects_exactly` lifts this pointwise
relation to lists at `Product.fst:2223-2232`.

`reachable_endpoint_projects_exactly` at `Product.fst:2419-2440` is therefore a
strong anti-fantasy result: a reachable symbolic endpoint cannot project to a
concrete behavior that the underlying TLS state machine did not take.

### 8.3 Conditional lifting

`complete_execution_lifts` at `Product.fst:2234-2252` and
`concrete_execution_has_product_lift` at `Product.fst:2277-2301` require
`symbolically_realizable_execution`.

The realization evidence supplies, per transition:

- exclusion of KeyUpdate and a local or canonical legal concrete transition;
- well-formed before/after product states;
- exact equality between shadow concrete states and transition endpoints;
- endpoint replacement and representation extension;
- exact reverse-history extension;
- honest network and trace delta;
- final endpoint refinement;
- event-specific symbolic origin, record, or application witnesses;
- exact AEAD seal/open bridge evidence for protected records.

It does not require the primitive freshness, X25519, hash, or HKDF bridge
predicates. It also does not require the concrete signature, HMAC, or X.509
authentication bridges; those are additional premises of the authentication
theorems.

This predicate is deliberately more informative than "there exists a product
execution", so the lifting theorem is not circular. But no theorem in this
layer constructs the witnesses for every legal concrete transition.

### 8.4 Inhabitation and vacuity

The empty base case of `symbolically_realizable_execution` at
`Product.fst:2180-2205` is easy to inhabit. The nonempty cases require all of
the bridge and event evidence above.

An audit must therefore ask:

1. Is there a constructed nonempty, completed-handshake realization?
2. Are realization premises consequences of the concrete transition, or
   caller-supplied idealization evidence?
3. Could a contradictory equality make a realization branch uninhabited?
4. Is a theorem proving a conclusion only for an impossible witness?

The corrected record nonce in [Section 9](#9-nonce-vacuity-case-study) is an
example of why this check matters.

### 8.5 Active attacker coverage

The modeled product actions at `Product.fst:1498-1704` include:

- honest canonical transitions;
- attacker injection;
- routing;
- dropping;
- replay;
- modeled state corruption.

Injection requires DY attacker knowledge plus a representation binding. Drop
removes a packet, replay duplicates a packet, and attacker actions do not append
honest protocol-origin events.

This is a symbolic attacker transition system. It is not a separate theorem
that every possible concrete network implementation behavior maps to one of
these actions.

### 8.6 Event-generation bypass check

CertificateVerify and Finished are classified as origin-bearing events around
`Product.fst:1159-1216`. `NoProtocolEvent` is restricted to semantic events that
are not origin events, and the generic record-only path excludes Finished.
Thus a sent Finished cannot be modeled solely as an ordinary protected-record
event while silently omitting its authentication event.

This does not remove the authentication bridge premise. Concrete acceptance
still needs the exact Finished MAC bridge described in
`TLS13.Symbolic.Authentication`; generic record acceptance does not derive that
bridge automatically.

## 9. Nonce-vacuity case study

This is the most useful example of an adversarial audit finding a formally
verified but vacuous theorem path.

### 9.1 The rejected representation

Suppose the symbolic nonce were:

```text
DY.Literal (Seq.create sequence_number 0uy)
```

Because the `Literal` case of `Bridge.represents` is exact equality, the record
bridge would require:

```text
tls13_record_nonce static_iv sequence_number
==
Seq.create sequence_number 0uy
```

The left side is the real fixed-size TLS nonce. The right side is a zero byte
sequence whose length is the numeric sequence number. Real protected-record
realizations could therefore be contradictory, making downstream implications
vacuously true.

### 9.2 Current representation

The current definitions at `TLS13.Symbolic.Terms.fst:179-226` are:

```text
sequence token = Literal (Seq.create sequence_number 0uy)
symbolic nonce = Hash sequence_token
```

`Hash` is neither `Literal` nor `Concat`, so representing the nonce requires an
execution-local binding instead of concrete byte equality. This `Hash` does
**not** claim that TLS hashes sequence numbers. It is an opaque, public,
injective symbolic namespace for nonce identities.

Regression lemmas in `TLS13.Symbolic.RecordSecurity.fst` establish:

- sequence change changes the symbolic nonce, lines 17-31;
- the nonce uses explicit bridge binding, lines 33-40;
- the nonce is public, lines 42-57.

The underlying token/nonce injectivity lemmas are at
`TLS13.Symbolic.Terms.fst:187-226`.

### 9.3 Exact concrete tie

The concrete nonce remains exact:

- sent record realization binds
  `tls13_record_nonce concrete_static_iv concrete_sequence` at
  `Product.fst:933-995`;
- accepted record realization binds the read-state IV and sequence at
  `Product.fst:1063-1131`;
- canonical send/open semantics independently fixes the raw record bytes in
  `TLS13.Spec.StateMachine.Canonical.fst:32-212`.

Residual limitation: the symbolic nonce constructor ignores the static IV.
Nonce freshness is consequently stated per `(symbolic key, symbolic nonce)`,
not as global nonce uniqueness across all keys and IVs.

## 10. Trace invariant and attacker knowledge

### 10.1 Installed predicates

`TLS13.Symbolic.Invariant` defines:

- signature origin content and predicate at lines 9-51;
- Finished origin predicate at lines 52-77;
- AEAD usage/direction mapping and origin predicate at lines 79-121;
- monotonicity and the crypto-invariant instance at lines 123-272;
- state, event, and protocol invariant instances at lines 274-325.

These predicates encode the origin-or-compromise rules consumed by the
authentication and record theorems.

### 10.2 Hygiene is load bearing

`trace_extension_hygienic` at `Invariant.fst:327-337` requires each appended
entry to satisfy `DY.trace_entry_invariant` at the appropriate prefix.

`secure_product_step_preserves_invariant` at `Invariant.fst:366-377` assumes:

```text
trace_invariant before.trace
/\ product_step before action after
/\ trace_extension_hygienic before.trace after.trace
```

and proves the invariant for `after.trace`.

This is sound invariant folding, but it is not an independent derivation of
entry hygiene from concrete TLS semantics. `securely_realizable_execution` adds
the hygiene evidence to realization; it remains part of the caller-supplied
symbolic boundary.

### 10.3 Headline consequences

- `secure_product_execution_preserves_invariant`,
  `Invariant.fst:486-505`, preserves the invariant over a secure execution.
- `securely_reachable_trace_invariant`, `Invariant.fst:507-515`, gives the
  invariant for securely reachable states.
- `attacker_only_knows_publishable`, `Invariant.fst:517-527`, proves:

  ```text
  trace_invariant trace
  /\ attacker_knows trace message
  ==> is_publishable trace message
  ```

- `signature_origin`, `finished_origin`, and `aead_origin`,
  `Invariant.fst:656-706`, project the installed origin predicates.

Origin projections unfold facts already present in the invariant. They do not
by themselves show that a concrete verification operation supplied the bridge
evidence.

## 11. Authentication audit

### 11.1 Acceptance and evidence

The main definitions are:

| Surface | Source |
| --- | --- |
| Client/server acceptance predicates | `Authentication.fst:17-41` |
| Trusted-server/name match | `Authentication.fst:43-55` |
| Context parameter agreement | `Authentication.fst:57-69` |
| Transcript checkpoints | `Authentication.fst:71-133` |
| Concrete signature bridge | `Authentication.fst:135-190` |
| Concrete Finished bridge | `Authentication.fst:192-225` |
| Symbolic verification bundles | `Authentication.fst:227-370` |
| Acceptance/state reflection | `Authentication.fst:372-412` |
| Origin theorems | `Authentication.fst:414-553` |
| Freshness/injectivity | `Authentication.fst:555-680` |
| Concrete acceptance theorems | `Authentication.fst:682-839` |
| Full-session agreement | `Authentication.fst:841-995` |

The transcript evidence distinguishes the pre-CertificateVerify,
pre-server-Finished, and pre-client-Finished checkpoints. A reviewer should
check that every bridge uses the intended checkpoint.

`context_parameters_agree` compares fields of caller-supplied symbolic contexts.
Product's `context_matches_endpoint` at `Product.fst:294-303` ties such a
context only to the endpoint session on the local role and to the symbolic
transcript. It does not derive equality between context randoms, key shares,
server name, or peer session and the corresponding concrete handshake fields.
Thus "context parameter agreement" is symbolic-context agreement, not yet a
concrete session-parameter correspondence theorem.

### 11.2 Named-server authentication

`concrete_client_acceptance_authenticates_named_server` at
`Authentication.fst:682-780` requires:

- product well-formedness and the trace invariant;
- concrete client acceptance;
- concrete transcript and wire evidence;
- the trusted registry/name/leaf-key match;
- the concrete RSA-PSS signature bridge;
- the concrete server-Finished bridge.

It concludes one of:

1. server credential-label compromise;
2. server handshake-traffic-label compromise;
3. both a matching named-server CertificateVerify origin and a
   same-transcript server-Finished origin.

The CertificateVerify origin authenticates the registered server identity.
Finished supplies key confirmation for the transcript; Finished alone does not
authenticate a hostname.

### 11.3 Anonymous-client confirmation

`concrete_server_acceptance_confirms_anonymous_client` at
`Authentication.fst:782-839` concludes client handshake-traffic-label
compromise or a matching client-Finished origin.

It intentionally does not identify the client.

### 11.4 Full-session agreement

`concrete_full_session_agreement` at `Authentication.fst:862-995` combines both
acceptances, full transcript evidence, one signature bridge, and both Finished
bridges. Its non-compromise branch contains all three origin events.

The origin contexts are separately existential. The theorem does not conclude
that all three context records are equal. Nor does it derive the symbolic
context parameters from concrete randoms and key shares. A claim of exact
concrete peer/session parameter agreement would need both context equality and
context-to-concrete correspondence theorems.

### 11.5 Injectivity nuance

`injective_server_agreement` at `Authentication.fst:597-680` uses freshness and
trace uniqueness to show that an exact `ServerFinishedSent` origin entry has one
trace position.

This is event-origin injectivity. It is not a theorem that every distinct client
acceptance maps injectively to a distinct server session; multiple acceptances
could refer to the same unique origin unless acceptance uniqueness is proved
separately.

### 11.6 Authentication bridge audit

The signature and Finished bridge predicates are premises of the concrete
acceptance theorems. They are not derived in this module solely from reachable
concrete acceptance flags.

Audit these questions:

1. Is the accepted leaf key exactly the registered server key?
2. Is the CertificateVerify input the exact context string plus the correct
   transcript hash?
3. Is the Finished key derived from the endpoint's installed traffic lineage?
4. Does the Finished MAC use the correct later transcript checkpoint?
5. Are the compromise labels attached to the exact keys being verified?
6. Can an accepted protected record be shown to supply these bridges, rather
   than merely an AEAD plaintext?

The current proof makes these execution-local obligations explicit. It should
not be summarized as unconditional authentication for every reachable concrete
acceptance.

## 12. Secrecy and key separation audit

### 12.1 Key lineage

`TLS13.Symbolic.Secrecy` defines:

- key-schedule inputs and derivations at lines 14-60;
- traffic-material matching and complete lineage at lines 62-95;
- ephemeral labels at lines 97-107;
- target selection at lines 109-222;
- label propagation at lines 224-457;
- knowledge-to-compromise lemmas at lines 459-529;
- headline secrecy theorems at lines 530-690;
- symbolic key separation at lines 692-861.

`complete_key_schedule_lineage` and `schedule_target_matches` are load-bearing
premises. "Established" means that the caller provides evidence that the
endpoint's represented fields are the exact symbolic derivations at the
relevant transcript checkpoints. The currently unused X25519/hash/HKDF primitive
bridges do not derive this lineage from concrete computations.

### 12.2 Secret-knowledge conclusion

`schedule_secret_secrecy` at `Secrecy.fst:530-553` proves:

```text
trace invariant
/\ attacker knows selected schedule-secret term
==>
supplied client label corrupt
\/ supplied server label corrupt
```

`established_schedule_secret_secrecy` at `Secrecy.fst:612-646` adds endpoint
membership, refinement, complete lineage, target matching, and correctly
used ephemeral terms. `ephemeral_pair_has_labels` at `Secrecy.fst:97-107`
requires the terms to have the supplied labels and expected ephemeral usages;
it does not require the labels to be the intended
`Labels.ephemeral_key_label` values.

This becomes an endpoint ephemeral-state secrecy result only after the supplied
labels are proved non-public and tied to the intended endpoint principal/state
identifiers. It still does not prove concrete entropy, X25519 computational
hardness, HKDF pseudorandomness, memory erasure, or forward secrecy.

### 12.3 Server-side honest-peer condition

Secrecy for a server receiving an attacker-chosen DH share is not automatic.
The relevant specialization requires evidence that the peer ephemeral belongs
to the intended honest matching session. This prevents a theorem from treating
an attacker-selected shared secret as confidential merely because it has a TLS
shape.

### 12.4 Separation

The separation lemmas prove symbolic disequality among:

- client/server handshake traffic secrets;
- handshake/application traffic secrets;
- client/server application traffic secrets;
- Finished keys and record keys;
- record keys and IVs.

These are constructor and label separation results. Audit reports must not
translate them into concrete "keys can never collide" claims.

## 13. Protected-record security

### 13.1 Exact send and receive realization

`sent_record_realizes` at `Product.fst:933-995` fixes:

- session context, sender role, direction, and epoch;
- concrete sequence number;
- canonical TLSInnerPlaintext;
- exact five-byte record-header AAD;
- concrete and symbolic key/IV;
- raw record parsing;
- concrete ciphertext from
  `chacha20_poly1305_seal(key, tls13_record_nonce(iv, seq), aad, plaintext)`;
- the symbolic `AeadEnc` binding.

`accepted_record_realizes` at `Product.fst:1063-1131` fixes:

- receiver context and accepted direction/epoch/sequence;
- read key and IV;
- header AAD and raw record parsing;
- successful concrete AEAD open;
- concrete plaintext parsing to the semantic TLS message;
- symbolic AEAD binding and raw-record representation.

Application-data sends recursively follow the same segmentation as the
canonical concrete send path. Review
`sent_application_record_contents_realize` and its use in protocol-event
realization around `Product.fst:995-1061,1289-1438`.

### 13.2 Origin and integrity

The central chain in `TLS13.Symbolic.RecordSecurity` is:

| Result | Source |
| --- | --- |
| Accepted record symbolically decrypts | `RecordSecurity.fst:162-186` |
| AEAD usage identifies direction/epoch | `RecordSecurity.fst:188-214` |
| Successful decrypt has AEAD origin | `RecordSecurity.fst:216-239` |
| Successful decrypt has sent event | `RecordSecurity.fst:241-275` |
| Accepted integrity condition bundle | `RecordSecurity.fst:277-310` |
| Accepted record has an origin | `RecordSecurity.fst:312-352` |
| Accepted record has exact matching origin | `RecordSecurity.fst:354-437` |

`accepted_record_has_matching_sent_origin` fixes in the sent event:

1. an existential in-profile sender context;
2. the accepted direction;
3. the accepted epoch;
4. the encoded accepted sequence number;
5. the accepted symbolic nonce;
6. the accepted symbolic plaintext;
7. the accepted concrete AAD's public symbolic encoding;
8. the accepted symbolic key.

This is substantially stronger than "some sent record existed".

It does not fix:

- equality between the origin context and the receiver's believed peer context;
- hostname or certificate identity;
- unique session ownership of the key;
- concrete static-IV identity in the event;
- uniqueness of the record-origin event.

Peer identity is handled only through the separate authentication argument, and
even there the full-session origin contexts remain existential.

### 13.3 Substitution and replay

- `protected_record_substitution_rejected`, lines 59-85, rejects a change to
  key, nonce, or AAD for a fixed ideal AEAD term.
- Cross-direction rejection, lines 87-106, requires distinct direction keys.
- Cross-epoch rejection, lines 108-126, requires distinct epoch keys.
- Replay rejection after sequence advance, lines 128-160, requires the old and
  current sequence numbers to differ.

The replay theorem proves symbolic nonce mismatch and ideal-decryption failure.
It does not itself prove sequence advancement; advancement comes from the
concrete record state transition.

### 13.4 Nonce freshness

Prior `(key, nonce)` use is detected in sent record events at
`Product.fst:1262-1272`. `sent_record_batch_fresh` at lines 1274-1287 checks
both the prior trace and earlier records in the same segmented send.

`generated_record_nonce_was_unused` at
`RecordSecurity.fst:439-454` projects this freshness condition.

Freshness is per key. Reuse of the same symbolic nonce under a different key is
permitted by the model.

### 13.5 Application plaintext

Honest application content has a session/application-state label and is wrapped
in a structured TLSInnerPlaintext term. It is not tagged public.

`honest_application_data_secrecy` at `RecordSecurity.fst:552-574` proves:

```text
attacker knows honest application content
==>
the owning application-state label is corrupt
```

This differs from record integrity:

- integrity requires the exact live AEAD key to be non-publishable;
- plaintext secrecy exposes compromise of the application state that owns the
  plaintext.

A live traffic key cannot preserve secrecy if the application supplied the same
plaintext through already-corrupt state. Conversely, the application label
theorem is not a computational IND-CPA/AEAD reduction.

## 14. Trusted computing base and proof obligations

Separate these categories in every audit report.

### 14.1 Mechanized proof TCB

- the F* parser, elaborator, typechecker, and trusted kernel;
- Z3 as used by F*;
- the pinned DY* core and its ideal attacker/cryptographic semantics;
- the concrete TLS specification definitions imported by the symbolic files.

DY* is a recursive Git submodule at
`third_party/dolev-yao-star-extrinsic`; verify its gitlink with:

```sh
git submodule status --recursive
git ls-tree HEAD third_party/dolev-yao-star-extrinsic
```

The reviewed pin is `b599e1fdca22a7fd97634320a7f882794fcbc28a`.

### 14.2 Abstract concrete interfaces

The symbolic argument trusts the abstract interfaces in:

- `src/spec/assumptions/TLS13.Crypto.Spec.fsti`;
- `src/spec/assumptions/TLS13.X509.Spec.fsti`.

These interfaces expose functional computations and limited correctness facts.
They do not supply computational collision resistance, PRF security, signature
unforgeability, AEAD unforgeability, or a complete X.509 proof.

### 14.3 Caller-supplied conditional evidence

These are premises, not hidden axioms:

- `symbolically_realizable_execution`;
- per-transition representation, event, and record witnesses;
- `trace_extension_hygienic`;
- concrete signature and Finished bridges;
- complete key-schedule lineage;
- installed-target matching;
- honest-peer ephemeral usages and caller-supplied labels;
- non-publishability of the accepted record key;
- trusted server registry/name/key correspondence.

Making these premises explicit is valuable: it makes the exact gap to a
computational or implementation-level theorem auditable.

In addition, the primitive freshness, X25519, hash, and HKDF bridge predicates
are currently definitions without consumers in the headline proof chain. They
must be wired into realization or lineage before they can discharge those
concrete-to-symbolic gaps.

### 14.4 Not in this proof's TCB because not claimed

The proof does not ask the reader to trust a hidden claim that:

- OpenSSL or HACL* realizes the ideal constructors computationally;
- extracted C refines every symbolic transition;
- the host RNG has a quantified entropy bound;
- certificate validation implements all WebPKI policy;
- the network eventually delivers messages.

Those results are absent rather than assumed.

## 15. Skeptical audit procedure

### Step 1: Freeze the dependency graph

```sh
git status --short
git submodule status --recursive
git ls-tree HEAD third_party/dolev-yao-star-extrinsic
```

Confirm that no untracked DY clone or modified submodule supplies checked files.
The submodule URL is declared in `.gitmodules:4-6`.

### Step 2: Check solver separation and flags

The root Makefile pins:

- TLS symbolic modules to Z3 4.13.3;
- DY* to Z3 4.15.3.

See `Makefile:30-34` and symbolic flags at `Makefile:94-109`.

Review for:

- `--admit_smt_queries`;
- `--lax`;
- unexpected `assume`;
- unbounded or exceptional local SMT options;
- stale checked files from a different solver.

The symbolic files currently set no exceptional local SMT resource options.

### Step 3: Scan for proof escapes

```sh
make admit-count
make check-admits
rg 'admit\s*\(|assume_|--admit_smt_queries|--lax' src/spec/symbolic
```

Also inspect reported assumptions. Abstract `.fsti` boundaries should be
expected and listed in [Section 14](#14-trusted-computing-base-and-proof-obligations);
an unexpected admitted implementation theorem should not be.

### Step 4: Verify by layer

```sh
make -j"$(nproc)" verify-symbolic-model
make -j"$(nproc)" verify-symbolic-invariant
make -j"$(nproc)" verify-symbolic-authentication
make -j"$(nproc)" verify-symbolic-secrecy
make -j"$(nproc)" verify-symbolic-records
make -j"$(nproc)" verify-symbolic
```

The targets and dependency closure are at `Makefile:317-408`.

### Step 5: Verify from fresh main and DY caches

```sh
make clean
make -j"$(nproc)" verify-symbolic
```

`make clean` removes the main `_cache` and DY* cache, but deliberately retains
the independently managed generated-wire verification cache and stamp. Thus
this checks the symbolic/TLS dependency closure from fresh main and DY caches,
not a fully cold generated-parser build. Use `make verify-generated` when the
generated wire sources or their verification cache also need revalidation.

Repeat the fresh-main/DY-cache run to detect stale symbolic artifacts and
solver-order instability. Then run:

```sh
make -j"$(nproc)" verify
make -j"$(nproc)" test
```

CI checks out recursive submodules and runs `verify-symbolic` in its own matrix
leg at `.github/workflows/ci.yml:95-120`.

### Step 6: Audit theorem contracts, not names

For each headline theorem:

1. Read every `requires` clause.
2. Classify each premise as derived, structural, trusted, or caller supplied.
3. Check that the conclusion fixes the intended context, transcript, identity,
   key, direction, epoch, and sequence.
4. Check every compromise disjunct names the exact live credential/state/key.
5. Search for a theorem that constructs the premise from reachable concrete
   state.
6. If no such theorem exists, describe the result as conditional.

Names such as "complete", "established", "authenticated", and "injective" do not
replace this exercise.

### Step 7: Run vacuity checks

For every realization predicate:

- look for literal/concrete length mismatches;
- look for equalities between independently derived values;
- find at least one intended constructor branch that can be inhabited;
- verify that the empty execution is not the only easy witness;
- inspect existential contexts for missing equality constraints;
- check that the antecedent does not simply restate the conclusion;
- verify that generic event branches cannot absorb security-sensitive events.

The nonce case in [Section 9](#9-nonce-vacuity-case-study) should be used as a
regression template.

### Step 8: Keep symbolic and concrete claims separate

Whenever the proof uses constructor injectivity, ask whether the report is
claiming:

- symbolic syntactic separation; or
- concrete collision impossibility.

Only the first is proved here.

Whenever the proof yields origin-or-compromise, ask whether the report is
claiming:

- an ideal-DY trace origin under bridge premises; or
- computational unforgeability of the concrete primitive.

Only the first is proved here.

## 16. High-value strengthening work

These additions would support stronger external claims without changing the
current theorems' validity:

1. Construct a nonempty, completed-handshake product realization.
2. Prove realization completeness for every canonical concrete transition in
   the supported profile.
3. Connect `fresh_value_bridge`, the X25519 bridges, and the hash/HKDF bridges
   to endpoint refinement, transition realization, and key-schedule lineage.
4. Derive signature and Finished bridge evidence from the actual concrete
   verification transitions and installed key lineage.
5. Add an explicit lemma reconciling handshake-traffic derivation checkpoints
   with the later Finished transcript checkpoints.
6. Require secrecy labels to equal the intended non-public endpoint
   principal-state labels.
7. Strengthen representation consistency where the same concrete bytes are
   reused across symbolic roles.
8. Tie symbolic contexts to concrete server names, randoms, key shares, peer
   sessions, and negotiated parameters.
9. Tie the symbolic interpretation of a received network packet directly to
   the accepted-record wire interpretation.
10. Strengthen protected-handshake plaintext realization so CertificateVerify
   and Finished record plaintext contains the exact symbolic signature/MAC
   terms, not only separate authentication evidence.
11. Prove equality of the relevant authentication origin contexts.
12. Prove acceptance-level injective agreement, distinct from uniqueness of an
   exact origin event.
13. Add implementation refinement and computational crypto arguments if the
    desired claim is about extracted C rather than the symbolic model.

These are not reasons to discard the current result. They identify precisely
which premises must be discharged to move from a conditional symbolic proof to
an unconditional concrete or computational security statement.

## 17. Final reviewer checklist

- [ ] The claimed execution is in the fixed profile.
- [ ] Any cross-endpoint configuration or SNI claim is proved separately from
      the individual role profile predicates.
- [ ] Concrete projection uses the exact state, event, sent bytes, and received
      bytes.
- [ ] Concrete lifting includes `symbolically_realizable_execution`.
- [ ] Defined primitive bridges are actually connected to the theorem chain
      being cited.
- [ ] Every bridge witness uses exact concrete operands and transcript stage.
- [ ] Representation aliasing cannot change the theorem being cited.
- [ ] Initial trace invariant and extension hygiene are present.
- [ ] CertificateVerify binds the requested name to the registered leaf key.
- [ ] Finished uses the intended role-specific traffic key and transcript.
- [ ] Compromise disjuncts refer to the exact credential or state label.
- [ ] Key-schedule lineage and installed-target matching are established.
- [ ] Supplied secrecy labels are the intended non-public endpoint-state labels.
- [ ] Symbolic context agreement is not presented as concrete parameter
      agreement without a context-to-concrete theorem.
- [ ] Record origin fixes direction, epoch, sequence, nonce, plaintext, AAD, and
      key.
- [ ] Nonce freshness covers both the prior trace and the current batch.
- [ ] Replay rejection is cited only after sequence advance.
- [ ] Application plaintext is honestly labelled and not attacker controlled.
- [ ] Symbolic constructor separation is not presented as concrete
      non-collision.
- [ ] Event uniqueness is not presented as acceptance/session injectivity.
- [ ] Record origin is not presented as peer identity without authentication.
- [ ] No excluded TLS feature is silently included in the claim.
- [ ] No computational, side-channel, liveness, or extracted-C claim is
      inferred from the DY theorem.
- [ ] Verification starts from fresh main/DY caches with pinned recursive
      submodules and solver versions; generated-wire cache reuse is stated.

If every checked claim survives this list, the result can be presented
confidently as a substantial, auditable symbolic-security proof with explicit
and reviewable abstraction boundaries.
