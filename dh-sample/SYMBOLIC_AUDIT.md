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
  honest sender origin. This is the ideal signature-unforgeability boundary
  needed because the concrete sample uses a collision-prone toy digest.
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
`ActRng`, `ActStart`, `ActDeliver`, and `ActInject`. It proves the product step,
exact frame projection, and preservation of product coherence `wf`.

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
* the completion run link;
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
  TI.trace_invariant #dh_sample_protocol_invariants p.ps_trace
```

`Product.wf` connects the concrete system to both endpoint shadows, every RNG
shadow, every packet shadow, long-term keys, pending ephemerals, peer shares,
and derived keys.

The installed signature predicate is exact:

```fstar
let dh_sign_pred_fun tr sk_usage vk msg =
  (vk == vkey_term (ltk_term 0) /\
   TB.event_triggered tr init_dy_principal tag_initiator_finish msg) \/
  (vk == vkey_term (ltk_term 2) /\
   TB.event_triggered tr resp_dy_principal tag_responder_respond msg)
```

The key and message are not existentially weakened. Because
`trace_invariant` checks a `Snoc` entry against its strict prefix, the
authorization event must precede the `MsgSent` carrying the signature.

The event predicate is an exact disjunction over the five protocol event tags,
with each tag pinned to the correct role and content shape. Unsupported tags
are rejected, rather than accepted vacuously by a conjunction of implications.
The unused AEAD, PKE, MAC, and state predicates are inhabited, nontrivial
predicates; none is installed as `False`.

### Initiality

`lemma_product_initial_invariant` proves the canonical initial product state
satisfies `product_invariant`. Its trace is not invented by an existential:

1. initiator long-term key `RandGen`;
2. initiator key-registration event;
3. responder long-term key `RandGen`;
4. responder key-registration event.

The proof starts from `lemma_trace_invariant_empty`, applies the exact setup
segment twice, and combines the result with `lemma_product_initial_wf`.

`lemma_product_initial_ideal_invariant` additionally proves that the initial
trace contains no `Corrupt` entry.

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
| `ActRng` | `RandGen` | `RandGen` is allowed; coherence records exact usage, label, length, and position |
| `ActStart` | initiate event, Msg1 send | event has exact role/shape; identity literal and DH public share are publishable |
| deliver Msg1 to responder | responder authorization, signing nonce, Msg2 send | received share is publishable for both honest and injected Msg1; exact prior event authorizes the signature |
| deliver Msg2 to initiator | initiator authorization, signing nonce, Msg3 send | exact prior event authorizes the signature over the exact structured shares |
| deliver Msg3 to responder | responder completion event | event has exact role and completion-content shape |
| `ActInject` | injected `MsgSent` | every injected field is a public literal |

The `MsgSent` obligations are discharged through DY `bytes_invariant` and
`is_publishable`, not by a caller premise.

Execution induction gives:

```fstar
product_reaches_invariant
product_reaches_no_corruption
product_reaches_ideal_invariant
```

for every product execution from `product_initial`.

### Security-strengthening invariant

Security consequences need persistent links between a completion, the exact
packets it consumed, and the authorization event recovered from a signature.
`DH.Sample.Symbolic.Security.security_invariant` therefore conjoins the ideal
product invariant with:

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
    responder peer-share shadow =
      share_term initiator_scalar
```

The first permits an injected literal share in `Resp_Wait3`. The second is
proved only at `Resp_Done`, where the completion run link selects the
initiator's honest Msg1 index. No secrecy claim is made merely because the
responder computed a key for attacker input.

`lemma_security_initial`, `lemma_security_step_preserves`, and
`product_reaches_security_invariant` prove this stronger invariant initially,
per step, and for every reachable product state.

### Non-vacuity of obligation 2

Two verified executions exercise opposite sides of the model:

* `lemma_secure_honest_run` reaches both completed endpoints, matching keys,
  both connected authorization events, and both attacker non-knowledge claims.
* `lemma_attacker_injected_msg1_nonvacuous` reaches `Resp_Wait3` by drawing a
  responder scalar, injecting an arbitrary Msg1, and delivering that injected
  packet. The responder's consumed index differs from the absent initiator
  index, and no completed-session secrecy claim applies.

The invariant therefore admits both a full successful protocol run and genuine
attacker interference.

## Obligation 3: security consequences

### Authentication extraction

The cryptographic core is `lemma_ltk_sig_authorized`.

1. `trace_invariant` makes every prior `MsgSent` publishable.
2. Publishability gives `bytes_invariant` for the exact structured packet.
3. Splitting Msg2 or Msg3 obtains `bytes_invariant` for its signature subterm.
4. The fixed long-term key is trace-recorded with label `secret`.
5. A secret label cannot flow to `public`, ruling out DY's attacker-signing
   disjunct.
6. `bytes_invariant_verify` therefore yields `dh_sign_pred_fun`.
7. The exact role key selects the corresponding disjunct and recovers the exact
   prior authorization event over the signed transcript.

`lemma_net_responder_authorized` and `lemma_net_initiator_authorized` apply this
argument to exact packet shadows. Packet origin identifies a genuine structured
signature but does not itself manufacture the authorization event.

The completion theorems are:

```fstar
theorem_initiator_authenticates_responder
theorem_responder_authenticates_initiator
```

Each requires only `security_invariant p` and the relevant completed endpoint
phase. Each concludes concrete identity/share agreement and a peer
authorization event whose identity and both share components are connected to
that completion.

The result is non-injective authentication. There is one session per role, and
the signed content contains no session identifier suitable for an injectivity
claim.

### Agreement

The narrow ideal completion guard supplies only:

```fstar
sys_resp_msg1_idx == sys_init_msg1_idx
```

`lemma_runlink_concrete_match` combines this equality with the two immutable
packet invariants. The packet at the shared index must simultaneously be:

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
shape, scalar, share, or matching-session witness.

### Attacker non-knowledge

For two trace-recorded honest ephemerals, `lemma_dh_secret_not_public` proves:

```fstar
~B.is_publishable tr (secret_term s (share_term s'))
```

The proof uses:

* `B.get_label_dh`;
* `B.get_dh_label_dh_pk`;
* exact `RandGen` labels for both scalars;
* `L.is_corrupt_join`;
* `L.is_corrupt_secret`.

Thus the shared secret has label `secret join secret`, which cannot flow to
public in the no-corruption profile.

`AK.attacker_only_knows_publishable_values` says that on a
`trace_invariant` trace every attacker-known value is publishable.
Contradiction yields `lemma_dh_not_attacker_known`.

The endpoint theorems are:

```fstar
theorem_initiator_key_secret
theorem_responder_key_secret
```

The first requires `Init_Done`; the second requires `Resp_Done`. The responder
theorem intentionally does not apply at attacker-started `Resp_Wait3`, where the
peer share may be an injected literal and the attacker may know the
corresponding key.

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
| Honest origin for completion Msg2/Msg3 | modeled assumption | Replaces computational unforgeability for the toy signature digest |
| Completion run-link equality | modeled assumption | Replaces collision-resistant transcript/session binding for the fixed sample |
| No `Corrupt` action | explicit model restriction, proved structurally | This sample studies a two-party no-corruption profile |
| Attacker Msg1 injection | modeled and reachable | Demonstrates active interference and responder DoS/intermediate key creation |
| Pulse local refinement | proved | Covers local wire-format endpoint machines |
| Pulse-to-composed-system refinement | **not proved** | RNG, network origin, and run-link services are outside the local implementation proof |
| Computational DH/signature security | **not claimed** | Symbolic terms and labels provide an ideal DY result |

The completion run link is the main idealization that a future realistic version
should eliminate. Replacing the toy digest with a collision-resistant symbolic
transcript/signature abstraction should make session matching a consequence of
signature verification rather than a separate environment condition.

## Suggested audit procedure

1. Read `DH.Sample.System.system_step` and
   `ideal_completion_link_ok`. Confirm Msg1 delivery is unrestricted and the
   completion guard states no identity/share/security conclusion.
2. Read `Product.wf`, `sym_extend`, and `product_step`. Confirm the source state
   is stored verbatim and each action produces the documented trace segment.
3. Read `Lifting.lift_next`, `lemma_lift_step`, and
   `lemma_lift_system_execution`. Confirm no caller-supplied symbolic witness
   appears in theorem premises.
4. Read `Invariant.dh_sign_pred_fun`, `dh_event_pred_fun`,
   `lemma_product_initial_invariant`, and
   `product_step_preserves_invariant`.
5. Check every branch of `product_step_preserves_invariant` against the action
   table above. Pay particular attention to the strict-prefix authorization
   requirement for signed `MsgSent` entries.
6. Read `Security.lemma_runlink_concrete_match`,
   `resp_shadow_link`, and `lemma_responder_peer_share_establish`. Confirm the
   symbolic equality comes from the indexed packet shadow, never concrete byte
   equality.
7. Read `lemma_ltk_sig_authorized` and both
   `lemma_net_*_authorized` proofs. Confirm authentication uses the DY trace
   invariant and rules out the attacker-signing disjunct through the secret key
   label.
8. Read `lemma_dh_secret_not_public`,
   `lemma_dh_not_attacker_known`, and both endpoint secrecy theorems.
9. Read `lemma_attacker_injected_msg1_nonvacuous` and
   `lemma_secure_honest_run` to rule out a model that supports only inert
   injection or only vacuous completion implications.
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

