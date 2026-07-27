# DH Sample: Symbolic Proof Audit

This document is the top-level audit guide for the standalone three-message DH
sample. It evaluates the result using exactly three obligations:

1. every execution in the claimed concrete model lifts precisely to the
   symbolic product machine;
2. an explicit invariant is true initially and preserved by every product step;
3. that invariant implies authentication, key agreement, and attacker
   non-knowledge.

The development completes all three obligations for
`DH.Sample.System.system_state_machine`: a fixed, one-initiator/one-responder,
single-session composed machine with explicit ideal RNG, signature-origin, and
completion run-link boundaries. It does **not** prove that arbitrary raw-byte
executions of the Pulse endpoints refine that composed ideal machine.

The detailed companion guides are:

* [`SYMBOLIC_LIFTING.md`](SYMBOLIC_LIFTING.md): construction and exactness of
  the product lift;
* [`SYMBOLIC_INVARIANT.md`](SYMBOLIC_INVARIANT.md): installed DY predicates,
  initiality, and action-by-action induction;
* [`SYMBOLIC_SECURITY.md`](SYMBOLIC_SECURITY.md): authentication, agreement,
  secrecy, active-attacker witness, and explicit ideal boundaries.

## What changed: real dynamic compromise

This development no longer has a no-corruption profile.  `DH.Sample.System` has a
fifth action, `ActCorrupt who`, and two persistent per-role compromise flags; the
symbolic product performs genuine DY* core `set_state` / `corrupt` operations;
and every headline security statement is now MODULO the relevant role's
compromise.  In one table:

| aspect | how it is modelled |
|---|---|
| compromise action | `Sys.ActCorrupt who` — sets that role's persistent flag and **nothing else** (`lemma_corrupt_step_changes_only_compromise_metadata`) |
| DY* effect | `Product.corrupt_run sh.sh_state_pos` — one `Corrupt` entry pointing at the role's CURRENT `SetState` |
| stored state | `Terms.snapshot_term ltk pending scalar peer_share key` — the role's complete live material, refreshed after every state-changing action |
| current pointer | `endpoint_shadow.sh_state_pos`, pinned by `wf`'s `state_pos_coherent` |
| completion effect | the responder's Msg3 completion stores nothing (phase only); its key was already in the snapshot from its Msg1 delivery |
| erasure / PFS | none modelled, hence **no forward secrecy**, explicitly |
| labels | long-term key, scalar and signing nonces all carry `Terms.role_label who` = `principal_state_label` of that role's state — corrupt exactly when that role is compromised |
| flags vs DY* | `Invariant.corruption_coherent` + `lemma_corruption_coherence` (an **iff**, both directions) |
| completion boundary | honest origin AND run link required only **before** the relevant signer's compromise; afterwards a forged/replayed completion is accepted |
| authentication | exact peer authorization event (via signature `bytes_invariant` + `dh_sign_pred`) **OR** that peer's signing-state corruption |
| agreement | keys equal **OR** `sys_init_corrupt` **OR** `sys_resp_corrupt` (no matching premise) |
| secrecy | attacker knowledge of the key implies init-state or resp-state corruption, plus the uncorrupted non-knowledge corollaries |
| witnesses | honest run (no compromise); injected-Msg1 run; **forged completion after `ActCorrupt Resp`**, where the honest branch is false and the attacker provably knows the corrupted stored state |

## Result at a glance

The end-to-end theorem is
`DH.Sample.Symbolic.Security.theorem_concrete_execution_secure`:

```fstar
let theorem_concrete_execution_secure
  (a b:principal) (ct:list Sys.system_transition) (cfinal:system_state)
  : Lemma
    (requires
      SM.trace_reaches
        (Sys.system_state_machine a b)
        (Sys.system_state_machine a b).SM.sm_initial_state
        ct cfinal)
    (ensures (
      exists (pt:list product_transition) (pfinal:product_state).
        product_execution (product_sm a b) (product_initial a b) pt pfinal /\
        proj pfinal == cfinal /\
        security_invariant pfinal /\
        endpoint_security_consequences pfinal /\
        ...))
```

The caller supplies only a concrete execution of the composed machine. The
theorem constructs the product execution and final symbolic state, proves exact
projection, establishes the inductive security invariant, and exposes the
security consequences. No trace, shadow state, realization relation, hygiene
premise, matching-session witness, scalar witness, or desired security fact is
provided by the caller.

Here, "concrete" means the pure composed machine in `DH.Sample.System`, not an
arbitrary deployed Pulse execution. That distinction is the most important
scope boundary in this audit.

## Protocol and modeled attacker

The wire protocol is:

```text
A -> B : A, g^x
B -> A : B, g^y, Sign_B(A, g^x, g^y)
A -> B : Sign_A(B, g^x, g^y)
```

`DH.Sample.System` contains both endpoints, an append-only network, packet
origins, an ideal RNG registry, and two write-once Msg1 network indices:

```fstar
sys_init_msg1_idx : option nat  (* initiator's own Msg1 *)
sys_resp_msg1_idx : option nat  (* Msg1 consumed by responder *)
```

The attacker can append any concrete wire message with `ActInject`. Msg1
delivery is unrestricted: an injected Msg1 can move the responder to
`Resp_Wait3` and elicit an honest Msg2 over the attacker-selected share. The
proof deliberately makes no responder-key secrecy claim in that intermediate
state.

Completion has two explicit ideal boundaries:

* `deliver_origin_ok` admits completion Msg2/Msg3 only with the corresponding
  honest sender origin while that sender is uncompromised; after compromise it
  admits forged or replayed completion messages. This is the ideal
  signature-unforgeability boundary: `DH.Sample.Crypto.fsti` exposes only
  functional correctness, not a computational unforgeability theorem.
* `ideal_completion_link_ok` requires the responder's consumed-Msg1 index to
  equal the initiator's own-Msg1 index. It states only phase and index facts; it
  does not state identities, share equality, authentication events, agreement,
  or secrecy.

The second boundary models an ideal signature binding to this fixed session.
Because packets are immutable and the network is append-only, equal indices
select the same Msg1 packet. The security invariant then derives identity and
share agreement from that packet, rather than assuming those equalities in the
completion guard.

## Obligation 1: exact concrete-to-symbolic lifting

### Claimed source machine

The quantified source is precisely:

```fstar
Sys.system_state_machine a b
```

Its transition relation is `Sys.system_step`. It includes:

* honest, fresh, role-owned RNG actions;
* initiator start;
* delivery of an indexed immutable packet;
* unrestricted attacker injection;
* packet-origin restrictions for completion;
* the fixed-session completion run link.

This explicit source machine prevents the theorem from silently alternating
between a local endpoint semantics, a network semantics, and a stronger
security semantics.

### Product state and exact projection

`DH.Sample.Symbolic.Product.product_state` stores:

* the complete `Sys.system_state` verbatim;
* one shared DY trace;
* initiator and responder symbolic shadows;
* a shadow for every concrete RNG draw;
* a shadow for every concrete network packet.

Projection is not a reconstruction:

```fstar
let proj (p:product_state) : system_state = p.ps_sys
```

Therefore final-state equality is literal:

```fstar
proj pfinal == final
```

The product is a stuttering refinement only because one source transition can
append several DY trace entries. The source state, source event, successor
state, and output are preserved exactly.

### Total lift

The lifting functions are executable proof-level functions:

```fstar
lift_next
lift_transition
lift_execution
lift_final
```

The one-step theorem `lemma_lift_step` performs an exhaustive case split over
`ActRng`, `ActStart`, `ActDeliver`, `ActInject`, and `ActCorrupt`. It proves the
product step, exact frame projection, and preservation of product coherence
`wf`.

Execution induction yields:

```fstar
let lemma_lift_system_execution
  (a b:principal)
  (ct:list Sys.system_transition) (final:system_state)
  : Lemma
    (requires
      SM.trace_reaches
        (Sys.system_state_machine a b)
        (Sys.system_state_machine a b).SM.sm_initial_state
        ct final)
    (ensures (
      exists (pt:list product_transition) (pfinal:product_state).
        product_execution (product_sm a b) (product_initial a b) pt pfinal /\
        execution_projects_exactly ct pt /\
        execution_frames_project_exactly
          (proj (product_initial a b)) (product_initial a b) ct pt /\
        proj pfinal == final))
```

This closes the earlier vacuity problem in which a caller had to supply a
realization witness for every step. Here, the caller supplies no symbolic
witness at all.

### Network and term provenance

Honest packets retain their exact structured symbolic terms:

* Msg1 contains `share_term initiator_scalar`;
* Msg2 contains `share_term responder_scalar` and a genuine `sig_term` over the
  responder's exact symbolic transcript;
* Msg3 contains a genuine `sig_term` over the initiator's exact symbolic
  transcript.

Delivery reuses the stored symbolic message at the delivered packet's network
index. It does not re-embed honest fields as literals. Injected fields are
canonical public literals and assert no honest cryptographic origin.

`net_entry_coherent`, `lemma_sent_init_msg1_exact`,
`lemma_sent_resp_msg2_exact`, `lemma_sent_init_msg3_exact`, and
`lemma_coherent_delivery_reads_exact` are the main audit points.

### What obligation 1 does not establish

The Pulse module instantiates `protocol_implementation` for the two **local**
wire-format state machines. There is no theorem connecting arbitrary Pulse
network/RNG executions to `Sys.system_state_machine`. In particular, the Pulse
proof does not implement or refine:

* the ideal RNG registry;
* packet-origin metadata;
* the completion run link (and its compromise-dependent relaxation);
* dynamic compromise (`ActCorrupt`), which is environment metadata no endpoint
  machine observes;
* the composed network scheduler.

Thus obligation 1 is complete for the explicitly modeled ideal system and
incomplete for an arbitrary deployed byte-level environment. The theorem names
and this audit should always be read with that scope.

## Obligation 2: a non-vacuous inductive invariant

There are two layers.

### DY trace and product coherence

`DH.Sample.Symbolic.Invariant.product_invariant` is:

```fstar
let product_invariant (p:product_state) : prop =
  Product.wf p /\
  TI.trace_invariant #dh_sample_protocol_invariants p.ps_trace /\
  corruption_coherent p
```

`Product.wf` connects the concrete system to both endpoint shadows, every RNG
shadow, every packet shadow, long-term keys, pending ephemerals, peer shares,
derived keys, and each role's current `SetState` pointer.  The
`corruption_coherent` conjunct relates the persistent concrete flags to the
actual `Corrupt` entries and role-state-label corruption in both directions.

The installed signature predicate is exact:

```fstar
let dh_sign_pred_fun tr sk_usage vk msg =
  (vk == vkey_term (ltk_term (role_ltk_pos Init)) /\
   TB.event_triggered tr init_dy_principal tag_initiator_finish msg) \/
  (vk == vkey_term (ltk_term (role_ltk_pos Resp)) /\
   TB.event_triggered tr resp_dy_principal tag_responder_respond msg)
```

The key and message are not existentially weakened. Because
`trace_invariant` checks a `Snoc` entry against its strict prefix, the
authorization event must precede the `MsgSent` carrying the signature.

The event predicate is an exact disjunction over the five protocol event tags,
with each tag pinned to the correct role and content shape. Unsupported tags
are rejected, rather than accepted vacuously by a conjunction of implications.
The unused AEAD, PKE, and MAC predicates are inhabited, nontrivial predicates;
none is installed as `False`.  The state predicate is both nontrivial and
actively exercised by every `SetState`; it requires the exact snapshot content
to be knowable at the role's `principal_state_label`.

### Initiality

`lemma_product_initial_invariant` proves the canonical initial product state
satisfies `product_invariant`. Its trace is not invented by an existential:

1. initiator long-term key `RandGen`;
2. initiator key-registration event;
3. initiator initial `SetState`;
4. responder long-term key `RandGen`;
5. responder key-registration event;
6. responder initial `SetState`.

The proof starts from `lemma_trace_invariant_empty`, applies the exact setup
segment twice, and combines the result with `lemma_product_initial_wf` and
`lemma_product_initial_corruption_coherent`.

### Per-step preservation

The central theorem is:

```fstar
let product_step_preserves_invariant p0 ev p1 out
  : Lemma
    (requires product_invariant p0 /\ product_step p0 ev p1 out)
    (ensures product_invariant p1)
```

There is no hygiene predicate and no secure-step wrapper. The proof dispatches
on every action of `product_step` itself:

| Action | DY entries appended | Main reason the new entries satisfy the invariant |
|---|---|---|
| `ActRng` | `RandGen`, refreshed `SetState` | `RandGen` is allowed; exact snapshot satisfies `dh_state_pred_fun` |
| `ActStart` | initiate event, Msg1 send, refreshed `SetState` | event has exact role/shape; identity literal and DH public share are publishable; snapshot records the now-active scalar |
| deliver Msg1 to responder | responder authorization, signing nonce, Msg2 send, refreshed `SetState` | received share is publishable for both honest and injected Msg1; exact prior event authorizes the signature; snapshot records scalar, peer share, and key |
| deliver Msg2 to initiator | initiator authorization, signing nonce, Msg3 send, refreshed `SetState` | exact prior event authorizes the signature over the exact structured shares; snapshot records scalar, peer share, and key |
| deliver Msg3 to responder | responder completion event | event has exact role and completion-content shape |
| `ActInject` | injected `MsgSent` | every injected field is a public literal |
| `ActCorrupt who` | `Corrupt current_state_pos` | DY core `corrupt_invariant`; coherence proves that position is the role's exact current `SetState` and that its concrete flag is set |

The `MsgSent` obligations are discharged through DY `bytes_invariant` and
`is_publishable`, not by a caller premise.

Execution induction gives:

```fstar
product_reaches_invariant
```

for every product execution from `product_initial`, including executions with
arbitrarily timed `ActCorrupt` actions.

### Security-strengthening invariant

Security consequences need persistent links between a completion, the exact
packets it consumed, and the authorization event recovered from a signature.
`DH.Sample.Symbolic.Security.security_invariant` therefore conjoins the
compromise-aware `product_invariant` with:

* `id_link_invariant`;
* immutable initiator-Msg1, responder-consumed-Msg1, and responder-Msg2 packet
  invariants;
* exact symbolic send-authorization bindings;
* the responder's consumed-Msg1 shadow link;
* completion authentication facts.

The two critical properties are:

```fstar
let resp_shadow_link p =
  Resp_Wait3-or-Done ==>
    responder peer-share shadow =
      Msg1 shadow at sys_resp_msg1_idx

let responder_peer_share_invariant p =
  Resp_Done ==>
    sys_init_corrupt \/
      responder peer-share shadow =
        share_term initiator_scalar
```

The first permits an injected literal share in `Resp_Wait3`.  In the
uncompromised branch of the second, the completion run link selects the
initiator's honest Msg1 index; after initiator compromise, a forged Msg3 may
complete the responder and the agreement conclusion is deliberately dropped.
No secrecy claim is made merely because the responder computed a key for
attacker input.

`lemma_security_initial`, `lemma_security_step_preserves`, and
`product_reaches_security_invariant` prove this stronger invariant initially,
per step, and for every reachable product state.

### Non-vacuity of obligation 2

Three verified executions exercise the model:

* `lemma_secure_honest_run` reaches both completed endpoints, matching keys,
  both connected authorization events, and both attacker non-knowledge claims.
* `lemma_attacker_injected_msg1_nonvacuous` reaches `Resp_Wait3` by drawing a
  responder scalar, injecting an arbitrary Msg1, and delivering that injected
  packet. The responder's consumed index differs from the absent initiator
  index, and no completed-session secrecy claim applies.
* `lemma_compromised_completion_nonvacuous` performs a real
  `ActCorrupt Resp`, appends `Corrupt` pointing to the responder's current
  `SetState`, proves that snapshot publishable and attacker-known, then injects
  a locally verifying forged Msg2 that completes the initiator while the
  responder remains in `Resp_Start`.

The invariant therefore admits a full successful protocol run, pre-completion
attacker interference, and behavior that becomes possible only after dynamic
compromise.

## Obligation 3: security consequences

### Authentication extraction

The cryptographic core is `lemma_ltk_sig_authorized`.

1. `trace_invariant` makes every prior `MsgSent` publishable.
2. Publishability gives `bytes_invariant` for the exact structured packet.
3. Splitting Msg2 or Msg3 obtains `bytes_invariant` for its signature subterm.
4. The fixed long-term key is trace-recorded with the signer's
   compromise-sensitive role-state label.
5. `bytes_invariant_verify` yields either `dh_sign_pred_fun` OR the DY
   attacker-signing/public-flow branch.
6. `lemma_ltk_public_iff_corrupt` converts public flow into exact signer-state
   corruption.
7. In the honest branch, the exact role key selects the corresponding
   `dh_sign_pred_fun` disjunct and recovers the exact prior authorization event
   over the signed transcript.

`lemma_net_responder_authorized` and `lemma_net_initiator_authorized` apply this
argument to exact packet shadows. Packet origin identifies a genuine structured
signature but does not itself manufacture the authorization event.

The completion theorems are:

```fstar
theorem_initiator_authenticates_responder
theorem_responder_authenticates_initiator
```

Each requires only `security_invariant p` and the relevant completed endpoint
phase. Each concludes the relevant peer signing-state corruption OR concrete
identity/share agreement and a peer authorization event whose components are
connected to that completion.

The result is non-injective authentication. There is one session per role, and
the signed content contains no session identifier suitable for an injectivity
claim.

### Agreement

The narrow ideal completion guard supplies only:

```fstar
sys_resp_msg1_idx == sys_init_msg1_idx
```

In the uncorrupted branch, `lemma_runlink_concrete_match` combines this equality
with the two immutable packet invariants. The packet at the shared index must
simultaneously be:

```text
the initiator's honest Msg1 (initiator identity, initiator share)
the responder's consumed Msg1 (recorded peer, recorded peer share)
```

This derives the concrete peer identity and share equalities. The symbolic
shadow link and `lemma_sent_init_msg1_exact` derive the corresponding structured
`share_term`, without inferring symbolic equality from concrete byte equality.

Endpoint coherence then gives:

```text
initiator key = dh initiator_scalar (dh_pk responder_scalar)
responder key = dh responder_scalar (dh_pk initiator_scalar)
```

`lemma_dh_agreement` proves equality. The headline theorem
`theorem_completed_session_key_agreement` assumes only
`security_invariant` and both completed phases; the caller supplies no key
shape, scalar, share, or matching-session witness, and concludes key equality
OR initiator compromise OR responder compromise.  The parallel
`theorem_completed_concrete_agreement` concludes two-sided identity/share
agreement under the same compromise disjunction.

### Attacker non-knowledge, modulo compromise

For the two roles' trace-recorded ephemerals, `lemma_dh_key_label` proves the
session key's label is exactly

```fstar
L.join (role_label Init) (role_label Resp)
```

using `B.get_label_dh` + `B.get_dh_label_dh_pk` + the exact `RandGen` labels of
both scalars.  `lemma_dh_key_knowledge_implies_corruption` then chains
`AK.attacker_only_knows_publishable_values` (attacker-known implies publishable),
`L.flow_to_public_eq` (publishable iff label corrupt) and `L.is_corrupt_join`
(corrupt join iff one side corrupt) to give

```fstar
AK.attacker_knows tr (secret_term s_i (share_term s_r)) ==>
  L.is_corrupt tr (role_label Init) \/ L.is_corrupt tr (role_label Resp)
```

No custom attacker predicate is defined anywhere.  The endpoint theorems are

```fstar
theorem_initiator_key_secret                  (* Init_Done *)
theorem_responder_key_secret                  (* Resp_Done *)
theorem_initiator_key_secret_uncompromised    (* + both flags clear, so not attacker-known *)
theorem_responder_key_secret_uncompromised
```

The responder theorems intentionally do not apply at attacker-started
`Resp_Wait3`.  The uncompromised corollaries recover the classical unconditional
non-knowledge statement exactly when neither role has been compromised, via
`lemma_corruption_coherence`.

Because no erasure is modelled, a compromise AFTER a completed session still
reveals that session's key: this model has **no forward secrecy**, and says so.

### Arbitrary reachability, not only one honest trace

The direct theorems:

```fstar
theorem_reachable_initiator_secure
theorem_reachable_responder_secure
theorem_reachable_completed_session_secure
```

quantify over arbitrary product executions from `product_initial`. They derive
the security invariant internally and require only the corresponding completion
phase. The honest-run theorem is a non-vacuity witness, not the scope of the
headline result.

Finally, `theorem_concrete_execution_secure` composes all three obligations:

```text
concrete composed execution
  -> total exact product lift
  -> inductive security invariant
  -> authentication + agreement + attacker non-knowledge
```

## Trust and scope boundaries

| Boundary | Status | Why it exists |
|---|---|---|
| F* kernel, SMT encoding, and DY core library | trusted dependency | The development proves obligations relative to these definitions and lemmas |
| Ideal RNG action and registry | modeled assumption | Separates honest fresh secret generation from attacker input |
| Abstract `DH.Sample.Crypto.fsti` operations and correctness laws | trusted interface | No toy implementation or public-share inverse is defined; a real cryptographic library and computational refinement remain external |
| Honest origin for completion Msg2/Msg3, **while the signer is uncompromised** | modeled assumption | Represents computational unforgeability, which is not proved from the abstract interface; lifted once that role is compromised |
| Completion run-link equality, **while the signer is uncompromised** | modeled assumption | Replaces collision-resistant transcript/session binding for the fixed sample; lifted once that role is compromised |
| Dynamic compromise (`ActCorrupt`) | **modeled and reachable** | Real DY* `Corrupt` on the role's current `SetState`; drives the "modulo compromise" form of every security statement |
| No erasure of stored material | explicit model choice | Snapshots retain scalars and session keys, so **no forward secrecy** is claimed |
| Attacker Msg1 injection | modeled and reachable | Demonstrates active interference and responder DoS/intermediate key creation |
| Pulse local refinement | proved | Covers local wire-format endpoint machines |
| Pulse-to-composed-system refinement | **not proved** | RNG, network origin, and run-link services are outside the local implementation proof |
| Computational DH/signature security | **not claimed** | The abstract interface states correctness only; symbolic terms and labels provide an ideal DY result |

The completion run link is the main idealization that a future realistic version
should eliminate. Instantiating `DH.Sample.Crypto.fsti` with a real library and
proving a computational refinement should make session matching a consequence
of signature verification rather than a separate environment condition.

## Suggested audit procedure

1. Read `DH.Sample.System.system_step`, `deliver_origin_ok` and
   `ideal_completion_link_ok`. Confirm Msg1 delivery is unrestricted, the
   completion guard states no identity/share/security conclusion, and the
   honest-origin/run-link requirements are imposed only while the relevant
   signer role is uncompromised. Read `ActCorrupt`'s branch and
   `lemma_corrupt_step_changes_only_compromise_metadata`: corruption touches
   nothing but the flag.
2. Read `Product.wf`, `sym_extend`, and `product_step`. Confirm the source state
   is stored verbatim and each action produces the documented trace segment.
3. Read `Lifting.lift_next`, `lemma_lift_step`, and
   `lemma_lift_system_execution`. Confirm no caller-supplied symbolic witness
   appears in theorem premises.
4. Read `Invariant.dh_sign_pred_fun`, `dh_state_pred_fun`, `dh_event_pred_fun`,
   `corruption_coherent`, `lemma_product_initial_invariant`, and
   `product_step_preserves_invariant`. Confirm the state predicate is the
   canonical "knowable at the storing role's state label" rule and that it is
   discharged for every `SetState` the product writes
   (`lemma_snapshot_knowable`).
5. Check every branch of `product_step_preserves_invariant` against the action
   table above. Pay particular attention to the strict-prefix authorization
   requirement for signed `MsgSent` entries.
6. Read `Security.lemma_runlink_concrete_match`,
   `resp_shadow_link`, and `lemma_responder_peer_share_establish`. Confirm the
   symbolic equality comes from the indexed packet shadow, never concrete byte
   equality.
7. Read `lemma_ltk_sig_authorized` and both
   `lemma_net_*_authorized` proofs. Confirm authentication uses the DY trace
   invariant, and that the attacker-signing disjunct is NOT ruled out but
   converted, through `lemma_ltk_public_iff_corrupt`, into exactly that role's
   state-label corruption.
8. Read `lemma_dh_key_label`, `lemma_dh_key_knowledge_implies_corruption`, both
   endpoint secrecy theorems and their `_uncompromised` corollaries.
9. Read `lemma_attacker_injected_msg1_nonvacuous`, `lemma_secure_honest_run` and
   `lemma_compromised_completion_nonvacuous` to rule out a model that supports
   only inert injection, only vacuous completion implications, or a compromise
   disjunct that is never reachable.
10. Read `theorem_concrete_execution_secure` last and check that its premise is
    exactly the source machine whose assumptions were audited in step 1.

## Verification

From the repository root:

```sh
make -C dh-sample -j$(nproc) verify check-admits check-symbolic-forbidden
```

The build is dependency-driven, incremental, and parallel. It verifies the pure
specification, Pulse local implementation, lift, invariant, and security
modules; rejects `admit`, `assume`, and `assert_norm`; and rejects dependencies
on DY examples or non-core DY libraries.

The symbolic development imports DY core only and does not reuse
`examples/iso_dh`.
