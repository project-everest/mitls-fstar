# DH Sample — Symbolic Security Consequences

`spec/symbolic/DH.Sample.Symbolic.Security.fst` proves authentication, session-key
secrecy, and session-key agreement for the fixed two-party DH sample.  The
development uses DY* **core only**, has no `admit`, `assume`, or `assert_norm`,
and keeps every `--z3rlimit` at 10 or below.

The canonical check is:

```sh
make -C dh-sample -j$(nproc) verify check-admits check-symbolic-forbidden
```

## 0. Dynamic compromise: `SetState` / `Corrupt`, and what it buys the attacker

This development models **real Dolev–Yao dynamic compromise** with the DY* core
state/corruption machinery.  There is **no no-corruption profile** any more.

### 0.1 Role states, snapshots and the current-state pointer

Each role owns exactly one DY* state identifier
(`Terms.role_state_id who`, under `Terms.role_dy_principal who`).  The content it
stores is its **complete live secret material**, in a fixed layout:

```fstar
let snapshot_term (ltk:BT.bytes) (pending scalar peer_share key:option BT.bytes) : BT.bytes =
  B.concat ltk (B.concat (opt_material pending)
    (B.concat (opt_material scalar)
      (B.concat (opt_material peer_share) (opt_material key))))
```

* `ltk` — the role's long-term signing key (always present);
* `pending` — the ephemeral it has drawn but not yet adopted;
* `scalar` — its adopted ephemeral DH scalar;
* `peer_share` — the peer share it accepted;
* `key` — the derived session key.

An absent field is rendered as the **public** empty literal (`no_material`), so
the layout is total.  `Product.shadow_snapshot sh` is that term for a role
shadow, and the shadow additionally records `sh_state_pos`: the **trace position
of the role's most recent `SetState`**, i.e. its *current-state pointer*.
`Product.wf` pins it:

```fstar
let state_pos_coherent (who:endpoint_id) (sh:endpoint_shadow) (tr:TB.trace) : prop =
  sh.sh_state_pos < TB.trace_length tr /\
  TB.entry_at tr sh.sh_state_pos
    (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh))
```

### 0.2 Timing: when the snapshot is (re)written

Every segment that changes a role's live material ends with a genuine
`DY.Core.Trace.Manipulation.set_state`:

| action | role | entries appended (in order) | new pointer |
|---|---|---|---|
| setup (initial) | both | `RandGen ltk`, `Event keygen`, **`SetState`** | 2 (Init), 5 (Resp) |
| `ActRng owner` | owner | `RandGen eph`, **`SetState`** | n+1 |
| `ActStart` | Init | `Event initiate`, `MsgSent Msg1`, **`SetState`** | n+2 |
| `ActDeliver _ Resp` (Msg1) | Resp | `Event respond`, `RandGen nonce`, `MsgSent Msg2`, **`SetState`** | n+3 |
| `ActDeliver _ Init` (Msg2) | Init | `Event finish`, `RandGen nonce`, `MsgSent Msg3`, **`SetState`** | n+3 |
| `ActDeliver _ Resp` (Msg3) | Resp | `Event responder_finish` | *unchanged* |
| `ActInject` | – | `MsgSent` | *unchanged* |
| `ActCorrupt who` | who | **`Corrupt sh_state_pos`** | *unchanged* |

**Completion effect.** The responder's Msg3 completion writes **no** new state
and does **not** move its pointer: completion changes its *phase*, not its key
material — its session key was already retained in the snapshot written at its
Msg1 delivery.  So a compromise before *or* after completion reveals exactly the
same responder material.

### 0.3 Persistence, no erasure, no PFS

Snapshots are **monotone in content**: once a role has drawn its scalar or
derived its session key, that material appears in every later snapshot of that
role.  **No erasure is modelled.**  Therefore this model deliberately provides
**no forward secrecy**: `ActCorrupt` at *any* time — including long after a
session completed — hands the attacker the role's long-term key *and* its
current ephemeral/session material.  `Part 8` of `Symbolic.Security` proves the
attacker genuinely `attacker_knows` the corrupted stored snapshot.

### 0.4 Compromise-sensitive labels

`Terms.role_label who = L.principal_state_label (role_dy_principal who)
(role_state_id who)`.  The role's long-term signing key, its DH scalar and every
signing nonce carry that label (`ltk_label`, `eph_label`, `signonce_label` are
all `role_label`).  DY* makes such a label corrupt **exactly** when a `Corrupt`
entry points at one of that role's `SetState` entries.  The former unconditional
`L.secret` labelling — which asserted role secrets can never leak — is gone.

Because key, scalar and nonce share one label, DY*'s `Sign` side-condition "the
signing key is at most as secret as the nonce" holds reflexively.

### 0.5 Flag / label coherence

`DH.Sample.System` records compromise as two persistent booleans
(`sys_init_corrupt`, `sys_resp_corrupt`); DY* records it as `Corrupt` entries.
`Invariant.corruption_coherent` (a conjunct of `product_invariant`) keeps the two
in exact agreement, and

```fstar
let lemma_corruption_coherence (p:product_state)
  : Lemma (requires product_invariant p)
          (ensures (p.ps_sys.sys_init_corrupt <==> role_state_corrupt p Init) /\
                   (p.ps_sys.sys_resp_corrupt <==> role_state_corrupt p Resp))
```

proves the **iff** in both directions (the ⟸ direction uses that a trace position
holds one entry and the two role principals are distinct).

## 1. Model and invariant

The chain is:

1. `DH.Sample.System` defines the concrete composed system and its explicit ideal
   environment.
2. `Symbolic.Product` adds one DY trace and exact symbolic endpoint/network
   shadows.
3. `Symbolic.Lifting` totally lifts every concrete execution, without
   caller-supplied symbolic witnesses.
4. `Symbolic.Invariant` proves the compromise-aware DY trace/coherence invariant
   reachable.
5. `Symbolic.Security` proves and uses this stronger inductive invariant:

```fstar
let security_invariant (p:product_state) : prop =
  product_invariant p /\               // wf + DY trace_invariant + corruption_coherent
  id_link_invariant p /\            // C1: initiator targets the responder (frozen)
  init_msg1_pkt_invariant p /\      // C2: initiator's own Msg1 packet at sys_init_msg1_idx
  resp_msg1_pkt_invariant p /\      // C3: responder's consumed Msg1 packet at sys_resp_msg1_idx
  resp_msg2_pkt_invariant p /\      // C4: every honest Msg2 carries the responder's own share
  init_msg1_send_authbind p /\
  resp_shadow_link p /\             // responder peer-share shadow = shadow at sys_resp_msg1_idx
  responder_peer_share_invariant p /\
  resp_send_authbind p /\
  init_send_authbind p /\
  init_completed_auth p /\
  resp_completed_auth p
```

The concrete run/session-link invariants (C1–C4) are DY-free facts about the
composed system state.  At a completion delivery the guard supplies the index
EQUALITY `sys_resp_msg1_idx == sys_init_msg1_idx`; combined with the immutable
Msg1 packet invariants (C2, C3) this DERIVES the concrete identity/share
agreement — the guard never states it.  The responder peer-share fact is now
claimed only at `Resp_Done`:

```fstar
let responder_peer_share_invariant (p:product_state) : prop =
  (p.ps_sys.sys_resp.ep_phase == Resp_Done) ==>       // NOT Resp_Wait3
    p.ps_sys.sys_init_corrupt \/                      // MODULO initiator compromise
    (Some? p.ps_init.sh_scalar /\
     scalar_recorded_for Init p.ps_trace (Some?.v p.ps_init.sh_scalar) /\
     p.ps_resp.sh_peer_share ==
       Some (share_term (Some?.v p.ps_init.sh_scalar)))
```

It is DERIVED at responder completion (the Msg3 delivery, `Resp_Wait3 ->
Resp_Done`): the run link selects the initiator's exact honest Msg1 shadow (via
`resp_shadow_link` + `init_msg1_pkt_invariant` + `net_entry_coherent` +
`init_msg1_send_authbind`), with NO concrete-byte-to-symbolic inference.  An
attacker-started `Resp_Wait3` (answering an injected Msg1) does NOT satisfy it.

`lemma_security_initial`, `lemma_security_step_preserves`, and
`product_reaches_security_invariant` prove the combined invariant initially,
step-by-step, and for every product execution.

## 2. Named environment boundaries (all modulo compromise)

These are model assumptions, not implementation or computational claims.  Each is
imposed only while the relevant SIGNING role is uncompromised.

### Msg1 delivery is UNRESTRICTED (active attacker)

There is NO Msg1-delivery guard.  The attacker may inject a Msg1 (`ActInject`)
and route it to the responder, which leaves `Resp_Start` for `Resp_Wait3` and
answers with an honest Msg2 over the attacker-chosen share.  No secrecy or
honest-peer agreement is claimed for that attacker-selected intermediate
responder key.

### `deliver_origin_ok` and `ideal_completion_link_ok`

Completion delivery requires the honest-sender origin **unless the role that
signs that message is already compromised** — a compromised role's signing key is
the attacker's, so it can forge (or replay) that role's completion message:

```fstar
let deliver_origin_ok (st0:system_state) (dst:endpoint_id) (m:dh_message) (o:pkt_origin) : prop =
  match dst, m with
  | Init, Msg2 _ _ _ -> o == Sent Resp \/ st0.sys_resp_corrupt
  | Resp, Msg3 _     -> o == Sent Init \/ st0.sys_init_corrupt
  | _, _             -> True
```

`ideal_completion_link_ok` (marked `opaque_to_smt`) ADDS the RUN/SESSION LINK
plus the minimum genuine phase facts — again **only before the relevant signer is
compromised** — and NOTHING that names an identity or a share the completion later
concludes:

```fstar
let ideal_completion_link_ok (st0:system_state) (dst:endpoint_id) (m:dh_message) : prop =
  match dst, m with
  | Init, Msg2 _ _ _ ->
    st0.sys_resp_corrupt \/
    ((st0.sys_resp.ep_phase == Resp_Wait3 \/ st0.sys_resp.ep_phase == Resp_Done) /\
     Some? st0.sys_resp_msg1_idx /\
     st0.sys_resp_msg1_idx == st0.sys_init_msg1_idx)
  | Resp, Msg3 _ ->
    st0.sys_init_corrupt \/
    (st0.sys_init.ep_phase == Init_Done /\
     Some? st0.sys_resp_msg1_idx /\
     st0.sys_resp_msg1_idx == st0.sys_init_msg1_idx)
  | _, _ -> True
```

So after `ActCorrupt Resp`, a **forged or replayed** Msg2 with `Injected` origin
and no run link at all completes the initiator; symmetrically after
`ActCorrupt Init` for the responder.  `ActCorrupt` itself only updates the
compromise flag — `Sys.lemma_corrupt_step_changes_only_compromise_metadata`
proves both endpoint states, the network, the RNG registry, both pending draws,
both run-link indices and the output are literally unchanged.

The concrete agreement is DERIVED from that index equality
(`lemma_runlink_concrete_match`: the two Msg1 packet invariants force the packet
at the shared index to be BOTH the initiator's honest `Msg1 ini.ep_me
ini.ep_my_share` and the responder's consumed `Msg1 res.ep_peer
res.ep_peer_share`; immutability yields `res.ep_peer == Some ini.ep_me` and
`res.ep_peer_share == ini.ep_my_share`).  This is a FIXED one-session,
NON-injective ideal signature model: the signed content carries no per-session
index.

### Other model assumptions

* `product_invariant` includes `Product.wf`, `TI.trace_invariant`, and
  `corruption_coherent`.  It does **not** exclude `Corrupt` entries.
* Honest RNG transitions create trace-recorded ephemerals labelled with the
  drawing role's compromise-sensitive `role_label`.
* A role label is corrupt **iff** that role has been dynamically compromised
  (`lemma_corruption_coherence`); nothing is unconditionally non-corrupt.

### Pulse boundary

Pulse refines only the **local initiator and responder endpoint machines**.  It
does not refine or implement `DH.Sample.System`'s RNG, routing/origin,
run-link/completion, or network environment.  No claim is made that an arbitrary
raw-byte Pulse deployment refines this ideal composed system.

## 3. Authentication remains cryptographic

Packet provenance is connective tissue only; it does not manufacture an
authorization event.

For an honest Msg2/Msg3 shadow, the proof:

1. obtains `bytes_invariant` from `TI.trace_invariant` and the prior `MsgSent`;
2. extracts the signature subterm;
3. applies DY* `bytes_invariant_verify`, preserving BOTH possible outcomes:
   honest signing through `dh_sign_pred`, or attacker signing because the
   compromise-sensitive signing-key label flows to `public`;
4. turns the public-flow branch into exact role-state corruption with
   `flow_to_public_eq` and `lemma_ltk_public_iff_corrupt`;
5. in the honest branch, unfolds `dh_sign_pred` and recovers the signer's exact
   prior authorization `Event`.

Thus `lemma_ltk_sig_authorized`, `lemma_net_responder_authorized`, and
`lemma_net_initiator_authorized` derive authorization OR signer-state
corruption from
`TI.trace_invariant` + signature `bytes_invariant` + `dh_sign_pred`.
`resp_send_authbind`, `init_send_authbind`, and the run link only connect
that recovered event's transcript to this completion.

The completion theorems have exactly these premises:

```fstar
let theorem_initiator_authenticates_responder (p:product_state)
  : Lemma
    (requires security_invariant p /\
              p.ps_sys.sys_init.ep_phase == Init_Done)
    (ensures (
      let ini = p.ps_sys.sys_init in
      let res = p.ps_sys.sys_resp in
      (p.ps_sys.sys_resp_corrupt /\ role_state_corrupt p Resp) \/
      ((res.ep_phase == Resp_Wait3 \/ res.ep_phase == Resp_Done) /\
       res.ep_peer == Some ini.ep_me /\
       res.ep_peer_share == ini.ep_my_share /\
       res.ep_my_share == ini.ep_peer_share /\
       Some? p.ps_init.sh_peer_share /\
       Some? p.ps_resp.sh_peer_share /\
       Some? p.ps_resp.sh_scalar /\
       Some?.v p.ps_init.sh_peer_share ==
         share_term (Some?.v p.ps_resp.sh_scalar) /\
       (exists (s:BT.bytes).
         Some?.v p.ps_init.sh_peer_share == share_term s /\
         scalar_recorded_for Resp p.ps_trace s) /\
       TB.event_triggered p.ps_trace resp_dy_principal
         tag_responder_respond
         (transcript_term (term_of_principal ini.ep_me)
                          (Some?.v p.ps_resp.sh_peer_share)
                          (Some?.v p.ps_init.sh_peer_share)))))

let theorem_responder_authenticates_initiator (p:product_state)
  : Lemma
    (requires security_invariant p /\
              p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures (
      let ini = p.ps_sys.sys_init in
      let res = p.ps_sys.sys_resp in
      (p.ps_sys.sys_init_corrupt /\ role_state_corrupt p Init) \/
      (ini.ep_phase == Init_Done /\
       ini.ep_peer == Some res.ep_me /\
       ini.ep_my_share == res.ep_peer_share /\
       Some? p.ps_init.sh_scalar /\
       Some? p.ps_init.sh_peer_share /\
       Some? p.ps_resp.sh_scalar /\
       p.ps_resp.sh_peer_share ==
         Some (share_term (Some?.v p.ps_init.sh_scalar)) /\
       TB.event_triggered p.ps_trace init_dy_principal
         tag_initiator_finish
         (transcript_term (term_of_principal res.ep_me)
                          (share_term (Some?.v p.ps_init.sh_scalar))
                          (Some?.v p.ps_init.sh_peer_share)))))
```

`init_completed_auth` and `resp_completed_auth` contain the full concrete
agreement available from each endpoint view and the exact connected event
terms, each modulo the relevant peer signing-state compromise; no event or
matching-session premise is supplied by callers.

Two-sided concrete identity/share agreement is exposed separately, with no
matching premise:

```fstar
let theorem_completed_concrete_agreement (p:product_state)
  : Lemma
    (requires security_invariant p /\
              p.ps_sys.sys_init.ep_phase == Init_Done /\
              p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      concrete_session_agreement p \/
      p.ps_sys.sys_init_corrupt \/
      p.ps_sys.sys_resp_corrupt)
```

## 4. Exact secrecy and agreement theorems, MODULO COMPROMISE

### Initiator secrecy

```fstar
let theorem_initiator_key_secret (p:product_state)
  : Lemma
    (requires
      security_invariant p /\
      p.ps_sys.sys_init.ep_phase == Init_Done)
    (ensures
      Some? p.ps_init.sh_key /\
      (AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key) ==>
         role_state_corrupt p Init \/ role_state_corrupt p Resp))
```

### Responder secrecy

```fstar
let theorem_responder_key_secret (p:product_state)
  : Lemma
    (requires
      security_invariant p /\
      p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      Some? p.ps_resp.sh_key /\
      (AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key) ==>
         role_state_corrupt p Init \/ role_state_corrupt p Resp))
```

Both are proved **only** from the library API: the session key is
`dh s_i (dh_pk s_r)` for the two roles' trace-recorded ephemerals, so
`get_label_dh` + `get_dh_label_dh_pk` give its label
`join (role_label Init) (role_label Resp)`;
`AK.attacker_only_knows_publishable_values` turns attacker knowledge into
publishability, `flow_to_public_eq` turns that into corruption of the join, and
`is_corrupt_join` splits it into the two role corruptions.  There is **no custom
attacker predicate**, and no caller-supplied key shape, share, scalar, or
`scalar_recorded` premise.

### Uncorrupted corollaries (classical non-knowledge)

```fstar
let theorem_initiator_key_secret_uncompromised (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_init.ep_phase == Init_Done /\
              p.ps_sys.sys_init_corrupt == false /\ p.ps_sys.sys_resp_corrupt == false)
    (ensures Some? p.ps_init.sh_key /\
             ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key)))

let theorem_responder_key_secret_uncompromised (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_resp.ep_phase == Resp_Done /\
              p.ps_sys.sys_init_corrupt == false /\ p.ps_sys.sys_resp_corrupt == false)
    (ensures Some? p.ps_resp.sh_key /\
             ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key)))
```

(The concrete flags are converted to "neither role label is DY*-corrupt" by
`lemma_corruption_coherence`.)

### Completed-session agreement

```fstar
let theorem_completed_session_key_agreement (p:product_state)
  : Lemma
    (requires
      security_invariant p /\
      p.ps_sys.sys_init.ep_phase == Init_Done /\
      p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      Some? p.ps_init.sh_key /\
      Some? p.ps_resp.sh_key /\
      (p.ps_init.sh_key == p.ps_resp.sh_key \/
       p.ps_sys.sys_init_corrupt \/ p.ps_sys.sys_resp_corrupt))
```

**agreement OR init-compromise OR resp-compromise**, with no matching premise:
both key structures are DERIVED (`init_completed_auth` gives the initiator peer
share from the responder scalar, `responder_peer_share_invariant` gives the
responder peer share from the initiator scalar) and `Terms.lemma_dh_agreement`
proves term equality.

`theorem_matching_key_agreement p s_i s_r` remains only a lower-level algebraic
helper.  It is not a headline assumption-bearing session theorem.

### Completion authentication, MODULO COMPROMISE

```fstar
let theorem_initiator_authenticates_responder (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_init.ep_phase == Init_Done)
    (ensures
      (p.ps_sys.sys_resp_corrupt /\ role_state_corrupt p Resp) \/
      ( (* full concrete agreement + the responder's EXACT authorization event *)
        res.ep_peer == Some ini.ep_me /\
        res.ep_peer_share == ini.ep_my_share /\
        res.ep_my_share == ini.ep_peer_share /\
        Some?.v p.ps_init.sh_peer_share == share_term (Some?.v p.ps_resp.sh_scalar) /\
        TB.event_triggered p.ps_trace resp_dy_principal tag_responder_respond
          (transcript_term (term_of_principal ini.ep_me)
                           (Some?.v p.ps_resp.sh_peer_share)
                           (Some?.v p.ps_init.sh_peer_share)) ))

let theorem_responder_authenticates_initiator (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      (p.ps_sys.sys_init_corrupt /\ role_state_corrupt p Init) \/
      ( ini.ep_phase == Init_Done /\
        ini.ep_peer == Some res.ep_me /\
        ini.ep_my_share == res.ep_peer_share /\
        p.ps_resp.sh_peer_share == Some (share_term (Some?.v p.ps_init.sh_scalar)) /\
        TB.event_triggered p.ps_trace init_dy_principal tag_initiator_finish
          (transcript_term (term_of_principal res.ep_me)
                           (share_term (Some?.v p.ps_init.sh_scalar))
                           (Some?.v p.ps_init.sh_peer_share)) ))
```

The compromised disjunct gives BOTH the concrete flag and the genuine DY* label
corruption.  The honest disjunct's event is extracted through the signature
`bytes_invariant` + `dh_sign_pred` (`lemma_ltk_sig_authorized`), never from the
origin metadata.

Note the deliberate asymmetry: the responder's completion does **not** claim
`ini.ep_peer_share == res.ep_my_share`.  That single conjunct is the peer's-view
fact a **compromised responder** can break (it can forge a Msg2 feeding the
initiator an attacker share and still let the responder accept the initiator's
genuine Msg3), so it is claimed only by `init_completed_auth`, which is itself
modulo responder compromise.

## 5. Direct arbitrary-reachability theorems

Callers need not invoke invariant reachability first:

```fstar
let theorem_reachable_initiator_secure
  (a b:principal) (pt:list product_transition) (p:product_state)
  : Lemma
    (requires
      product_execution (product_sm a b) (product_initial a b) pt p /\
      p.ps_sys.sys_init.ep_phase == Init_Done)
    (ensures
      security_invariant p /\
      init_completed_auth p /\
      Some? p.ps_init.sh_key /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key)))

let theorem_reachable_responder_secure
  (a b:principal) (pt:list product_transition) (p:product_state)
  : Lemma
    (requires
      product_execution (product_sm a b) (product_initial a b) pt p /\
      p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      security_invariant p /\
      resp_completed_auth p /\
      Some? p.ps_resp.sh_key /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key)))

let theorem_reachable_completed_session_secure
  (a b:principal) (pt:list product_transition) (p:product_state)
  : Lemma
    (requires
      product_execution (product_sm a b) (product_initial a b) pt p /\
      p.ps_sys.sys_init.ep_phase == Init_Done /\
      p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      security_invariant p /\
      init_completed_auth p /\
      resp_completed_auth p /\
      Some? p.ps_init.sh_key /\
      Some? p.ps_resp.sh_key /\
      p.ps_init.sh_key == p.ps_resp.sh_key /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key)) /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key)))
```

These are literally product-execution-plus-completion theorems.

## 6. No-witness concrete theorem

The only premise of `theorem_concrete_execution_secure` is:

```fstar
SM.trace_reaches
  (Sys.system_state_machine a b)
  (Sys.system_state_machine a b).SM.sm_initial_state
  ct cfinal
```

The caller supplies no product transition list, DY trace, shadow state, scalar,
or provenance witness.  The postcondition existentially returns the canonical
lifted `pt`/`pfinal` and proves:

```fstar
product_execution (product_sm a b) (product_initial a b) pt pfinal /\
proj pfinal == cfinal /\
security_invariant pfinal /\
endpoint_security_consequences pfinal
```

The remaining exact postcondition conjuncts are:

```fstar
(cfinal.sys_init.ep_phase == Init_Done ==>
   cfinal.sys_resp.ep_peer == Some cfinal.sys_init.ep_me /\
   cfinal.sys_resp.ep_peer_share == cfinal.sys_init.ep_my_share /\
   cfinal.sys_resp.ep_my_share == cfinal.sys_init.ep_peer_share) /\
(cfinal.sys_resp.ep_phase == Resp_Done ==>
   cfinal.sys_init.ep_phase == Init_Done /\
   cfinal.sys_init.ep_peer == Some cfinal.sys_resp.ep_me /\
   cfinal.sys_init.ep_my_share == cfinal.sys_resp.ep_peer_share /\
   cfinal.sys_init.ep_peer_share == cfinal.sys_resp.ep_my_share)
```

`endpoint_security_consequences` states directly that:

* initiator completion implies `init_completed_auth` and initiator key secrecy;
* responder completion implies `resp_completed_auth` and responder key secrecy;
* completion of both endpoints implies both keys exist and are equal.

## 7. Non-vacuity

Three witnesses, all machine-checked:

1. **Honest run, NO compromise** — `lemma_secure_honest_run a b x y` (premise
   `x =!= y`) constructs the full six-transition run.  Its final lifted state has
   both endpoints complete, both exact connected authorization events, the
   responder Msg1 share equality, both symbolic keys present and **equal**, both
   keys **attacker-unknown**, the concrete equality `Sys.hikey x y == Sys.hrkey x
   y`, **both compromise flags clear** and **neither role label corrupt**.  So
   the compromise disjuncts do not swallow the honest statements.

2. **Injected Msg1 (availability, not authentication)** —
   `lemma_attacker_injected_msg1_nonvacuous a b am ash y`: `Sys.attacker_run`
   lifts to a genuine product execution that STILL satisfies
   `security_invariant`, with the responder in `Resp_Wait3` (never `Resp_Done`),
   the initiator in `Init_Start`, a broken run link, an `Injected` consumed
   packet, and **no role compromised**.

3. **Forged completion AFTER compromise** —
   `lemma_compromised_completion_nonvacuous a b x agy`: `Sys.corrupt_run`
   (draw `x`; `ActStart`; **`ActCorrupt Resp`**; inject a forged
   `Msg2 b agy (sign b (transcript a g^x agy))`; deliver that **injected** packet
   to the initiator) lifts to a product execution whose final state satisfies
   `security_invariant` and where:

   * `sys_resp_corrupt == true`, `role_state_corrupt pfinal Resp` (the responder's
     DY* state label IS corrupt), and there is a real corrupted stored state:
     `TB.state_was_corrupt pfinal.ps_trace (role_dy_principal Resp)
     (role_state_id Resp) content`, which is `is_publishable` and which
     `AK.attacker_knows` — the attacker literally holds the responder's stored
     snapshot;
   * the initiator has **completed** (`Init_Done`) with the attacker's share as
     its peer share;
   * the responder is still in **`Resp_Start`** — it never responded — so the
     HONEST branch of `init_completed_auth` (whose first conjunct demands
     `Resp_Wait3`/`Resp_Done`) is **false** at this state.  The compromised
     disjunct is therefore genuinely load-bearing: this is a real forgery, not a
     relabelled honest run.
   * the initiator itself was never compromised (`sys_init_corrupt == false`).

## 8. Limitations

* **Active attacker on Msg1; candid DoS story.** Msg1 delivery is
  UNRESTRICTED: an attacker-injected Msg1 drives the responder to `Resp_Wait3`
  and elicits an honest Msg2 over the attacker-chosen share.  No secrecy or
  honest-peer agreement is claimed there.
* **Signatures / run link, modulo compromise.** The honest-origin restriction on
  the two completion messages plus the run/session-index link compensate for the
  deliberately weak toy digest — but only while the signing role is honest.  A
  compromised role's completion messages are attacker-forgeable by construction.
  No computational unforgeability theorem is claimed.
* **NO FORWARD SECRECY, by design.** No erasure is modelled: a role's snapshot
  retains its ephemeral scalar and session key for ever, so `ActCorrupt` after a
  completed session reveals that session's key.  Every secrecy statement is
  therefore of the form "attacker knowledge ⟹ some role was compromised", and its
  unconditional form holds only when both flags are clear.
* **Ideal DY secrecy.** Non-knowledge relies on the DY* label/attacker model, not
  a computational DH reduction.
* **Fixed, non-injective sessions.** One initiator and one responder session; the
  signed content has no session index, so injective agreement is not claimed.
* **Pulse scope.** Pulse proves local endpoint refinement only, not the
  environment described above; and `ActCorrupt` is environment metadata that no
  endpoint machine observes.

## 9. Build configuration and dependencies

The unnecessary `spec/symbolic/.fst.config.json` was removed.  The Makefile is
the single auditable source of include paths, cache selection, warning policy,
and verifier options.

Symbolic source imports only `DY.Core.*`; `check-symbolic-forbidden` rejects
`DY.Lib`, `DY.Example`, `iso_dh`, and example paths.
