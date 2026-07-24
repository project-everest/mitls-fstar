# DH Sample — Symbolic Security Consequences

`spec/symbolic/DH.Sample.Symbolic.Security.fst` proves authentication, session-key
secrecy, and session-key agreement for the fixed two-party DH sample.  The
development uses DY* **core only**, has no `admit`, `assume`, or `assert_norm`,
and keeps every `--z3rlimit` at 10 or below.

The canonical check is:

```sh
make -C dh-sample -j$(nproc) verify check-admits check-symbolic-forbidden
```

## 1. Model and invariant

The chain is:

1. `DH.Sample.System` defines the concrete composed system and its explicit ideal
   environment.
2. `Symbolic.Product` adds one DY trace and exact symbolic endpoint/network
   shadows.
3. `Symbolic.Lifting` totally lifts every concrete execution, without
   caller-supplied symbolic witnesses.
4. `Symbolic.Invariant` proves the DY trace/coherence ideal profile reachable.
5. `Symbolic.Security` proves and uses this stronger inductive invariant:

```fstar
let security_invariant (p:product_state) : prop =
  ideal_product_invariant p /\
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
    Some? p.ps_init.sh_scalar /\
    scalar_recorded p.ps_trace (Some?.v p.ps_init.sh_scalar) /\
    p.ps_resp.sh_peer_share ==
      Some (share_term (Some?.v p.ps_init.sh_scalar))
```

It is DERIVED at responder completion (the Msg3 delivery, `Resp_Wait3 ->
Resp_Done`): the run link selects the initiator's exact honest Msg1 shadow (via
`resp_shadow_link` + `init_msg1_pkt_invariant` + `net_entry_coherent` +
`init_msg1_send_authbind`), with NO concrete-byte-to-symbolic inference.  An
attacker-started `Resp_Wait3` (answering an injected Msg1) does NOT satisfy it.

`lemma_security_initial`, `lemma_security_step_preserves`, and
`product_reaches_security_invariant` prove the combined invariant initially,
step-by-step, and for every product execution.

## 2. Named ideal-environment boundaries

These are model assumptions, not implementation or computational claims.

### Msg1 delivery is UNRESTRICTED (active attacker)

There is NO Msg1-delivery guard.  The attacker may inject a Msg1 (`ActInject`)
and route it to the responder, which leaves `Resp_Start` for `Resp_Wait3` and
answers with an honest Msg2 over the attacker-chosen share.  No secrecy or
honest-peer agreement is claimed for that attacker-selected intermediate
responder key.

### `deliver_origin_ok` and `ideal_completion_link_ok`

Completion delivery requires the honest-sender origin (the permitted ideal
unforgeability boundary), so an injected Msg2/Msg3 can never complete a peer:

* initiator acceptance of Msg2: `Sent Resp`;
* responder acceptance of Msg3: `Sent Init`.

`ideal_completion_link_ok` (marked `opaque_to_smt`) ADDS the RUN/SESSION LINK
plus the minimum genuine phase facts — and NOTHING that names an identity or a
share the completion later concludes:

```fstar
let ideal_completion_link_ok (st0:system_state) (dst:endpoint_id) (m:dh_message) : prop =
  match dst, m with
  | Init, Msg2 _ _ _ ->
    (st0.sys_resp.ep_phase == Resp_Wait3 \/ st0.sys_resp.ep_phase == Resp_Done) /\
    Some? st0.sys_resp_msg1_idx /\
    st0.sys_resp_msg1_idx == st0.sys_init_msg1_idx
  | Resp, Msg3 _ ->
    st0.sys_init.ep_phase == Init_Done /\
    Some? st0.sys_resp_msg1_idx /\
    st0.sys_resp_msg1_idx == st0.sys_init_msg1_idx
  | _, _ -> True
```

The concrete agreement is DERIVED from that index equality
(`lemma_runlink_concrete_match`: the two Msg1 packet invariants force the packet
at the shared index to be BOTH the initiator's honest `Msg1 ini.ep_me
ini.ep_my_share` and the responder's consumed `Msg1 res.ep_peer
res.ep_peer_share`; immutability yields `res.ep_peer == Some ini.ep_me` and
`res.ep_peer_share == ini.ep_my_share`).  This is a FIXED one-session,
NON-injective ideal signature model: the signed content carries no per-session
index.

### Other ideal assumptions

* `ideal_product_invariant` includes `Product.wf`,
  `TI.trace_invariant`, and no `Corrupt` entry.
* Honest RNG transitions create trace-recorded, `secret`-labelled ephemerals.
* DY `secret` is unconditionally non-corrupt in this profile.

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
3. uses the secret-labelled fixed role signing key to rule out the attacker
   disjunct of DY* `bytes_invariant_verify`;
4. unfolds the installed exact `dh_sign_pred`;
5. recovers the signer's exact prior authorization `Event`.

Thus `lemma_ltk_sig_authorized`, `lemma_net_responder_authorized`, and
`lemma_net_initiator_authorized` derive authorization from
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
      (res.ep_phase == Resp_Wait3 \/ res.ep_phase == Resp_Done) /\
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
        scalar_recorded p.ps_trace s) /\
      TB.event_triggered p.ps_trace resp_dy_principal
        tag_responder_respond
        (transcript_term (term_of_principal ini.ep_me)
                         (Some?.v p.ps_resp.sh_peer_share)
                         (Some?.v p.ps_init.sh_peer_share))))

let theorem_responder_authenticates_initiator (p:product_state)
  : Lemma
    (requires security_invariant p /\
              p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures (
      let ini = p.ps_sys.sys_init in
      let res = p.ps_sys.sys_resp in
      ini.ep_phase == Init_Done /\
      ini.ep_peer == Some res.ep_me /\
      ini.ep_my_share == res.ep_peer_share /\
      ini.ep_peer_share == res.ep_my_share /\
      Some? p.ps_init.sh_scalar /\
      Some? p.ps_init.sh_peer_share /\
      Some? p.ps_resp.sh_scalar /\
      p.ps_resp.sh_peer_share ==
        Some (share_term (Some?.v p.ps_init.sh_scalar)) /\
      TB.event_triggered p.ps_trace init_dy_principal
        tag_initiator_finish
        (transcript_term (term_of_principal res.ep_me)
                         (share_term (Some?.v p.ps_init.sh_scalar))
                         (Some?.v p.ps_init.sh_peer_share))))
```

`init_completed_auth` and `resp_completed_auth` contain the full concrete
identity/share agreement and the exact connected event terms; no event or
matching-session premise is supplied by callers.

## 4. Exact secrecy and agreement theorem premises

### Initiator secrecy

```fstar
let theorem_initiator_key_secret (p:product_state)
  : Lemma
    (requires
      security_invariant p /\
      p.ps_sys.sys_init.ep_phase == Init_Done)
    (ensures
      Some? p.ps_init.sh_key /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key)))
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
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key)))
```

There is no caller-supplied key shape, share, scalar, or `scalar_recorded`
premise.  Responder secrecy requires `Resp_Done` (a completed responder), NOT
merely `Resp_Wait3`: it uses `responder_peer_share_invariant`, which is claimed
only at `Resp_Done`; endpoint coherence supplies the responder's own recorded
scalar and exact key structure.  An attacker-started `Resp_Wait3` holding an
attacker-chosen peer share is deliberately outside this theorem's scope.

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
      p.ps_init.sh_key == p.ps_resp.sh_key)
```

There is no matching-share/key/scalar premise.  `init_completed_auth` derives
the initiator peer share from the responder scalar;
`responder_peer_share_invariant` derives the responder peer share from the
initiator scalar; `Terms.lemma_dh_agreement` then proves term equality.

`theorem_matching_key_agreement p s_i s_r` remains only a lower-level algebraic
helper.  It is not a headline assumption-bearing session theorem.

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

`lemma_secure_honest_run a b x y` (premise `x =!= y`) constructs the full
six-transition run.  Its final lifted state has both endpoints complete, both
exact connected authorization events, the responder Msg1 share equality, both
symbolic keys present and equal, both keys attacker-unknown, and the concrete
equality `Sys.hikey x y == Sys.hrkey x y`.

`lemma_attacker_injected_msg1_nonvacuous a b am ash y` shows the injected-Msg1
attack is a genuine reachable product execution (`Sys.attacker_run`: draw
responder scalar, inject `Msg1 am ash`, deliver it) whose lifted final state
STILL satisfies `security_invariant`, has the responder in `Resp_Wait3` (never
`Resp_Done`), the initiator in `Init_Start`, a broken run link
(`sys_resp_msg1_idx = Some 0`, `sys_init_msg1_idx = None`), and an `Injected`
consumed packet.  `theorem_responder_key_secret` (which requires `Resp_Done`)
therefore does not apply: the attacker started / DoS'd the responder but cannot
complete it.

## 8. Limitations

* **Active attacker on Msg1; candid DoS story.** Msg1 delivery is
  UNRESTRICTED: an attacker-injected Msg1 drives the responder to `Resp_Wait3`
  and elicits an honest Msg2 over the attacker-chosen share.  No secrecy or
  honest-peer agreement is claimed there.  Completion requires a genuine peer
  signature (recovered from the trace invariant + `dh_sign_pred`) AND a matching
  run link; the responder can be started but not completed by the network.
* **Ideal signatures / run link.** The honest-origin restriction on the two
  completion messages (`deliver_origin_ok`) plus `ideal_completion_link_ok` (the
  run/session-index link) compensate for the deliberately weak, collision-prone
  toy digest.  No computational unforgeability theorem is claimed.
* **Ideal DY secrecy.** Non-knowledge relies on secret-labelled ephemerals and
  the DY* ideal label/attacker model, not a computational DH reduction.
* **Fixed, non-injective sessions.** There is one initiator and one responder
  session; the signed content has no session index, so injective agreement is
  not claimed.  The run link binds the two flights of THIS single session.
* **Pulse scope.** Pulse proves local endpoint refinement only, not the ideal
  environment described above.

## 9. Build configuration and dependencies

The unnecessary `spec/symbolic/.fst.config.json` was removed.  The Makefile is
the single auditable source of include paths, cache selection, warning policy,
and verifier options.

Symbolic source imports only `DY.Core.*`; `check-symbolic-forbidden` rejects
`DY.Lib`, `DY.Example`, `iso_dh`, and example paths.
