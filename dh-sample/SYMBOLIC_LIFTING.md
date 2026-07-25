# DH Sample: Composed-System Symbolic Lifting

This is the audit guide for `DH.Sample.System` and
`DH.Sample.Symbolic.{Terms,Product,Lifting,Provenance}`.  The development uses
the DY* core library only.  All stated facts are checked by F* without admits,
assumes, or `assert_norm`.

## 1. Result

`DH.Sample.System` composes one initiator, one responder, an explicit network,
and an explicit ideal RNG environment.  `DH.Sample.Symbolic.Product` pairs that
whole state with one shared DY trace and symbolic shadows for both endpoints,
every network packet, and every concrete RNG draw.

The no-witness simulation theorem remains:

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

The caller supplies only concrete reachability data.  Total functions
`lift_next`, `lift_execution`, and `lift_final` construct the symbolic
execution; no symbolic realization, provenance witness, binding table, or
symbolic final state is supplied by the caller.

## 2. Explicit ideal RNG boundary

The composed concrete state contains:

```fstar
noeq type rng_draw = {
  rd_owner  : endpoint_id;
  rd_scalar : dh_scalar;
}

noeq type system_state = {
  sys_init          : endpoint_state;
  sys_resp          : endpoint_state;
  sys_net           : list packet;
  sys_rng           : list rng_draw;
  sys_init_pending  : option dh_scalar;
  sys_resp_pending  : option dh_scalar;
  sys_init_msg1_idx : option nat;
  sys_resp_msg1_idx : option nat;
}
```

The two indices are write-once run-link provenance: the first records the
initiator's own Msg1 packet and the second records the Msg1 actually consumed by
the responder, including an injected packet. They are irrelevant to RNG
coherence but become load-bearing at authenticated completion; see
`SYMBOLIC_SECURITY.md`.

Its actions distinguish honest/internal RNG from attacker control:

```fstar
noeq type sys_action =
  | ActRng     : owner:endpoint_id -> scalar:dh_scalar -> sys_action
  | ActStart
  | ActDeliver : idx:nat -> dst:endpoint_id -> sys_action
  | ActInject  : m:dh_message -> sys_action
```

`ActRng owner x` is an **honest/internal ideal-environment transition**.  The
concrete `x` is allowed in the semantic action frame so the relational model
can choose bytes; this is not a wire input or an attacker disclosure.  The
transition requires `rng_scalar_fresh x st0.sys_rng`, records an
honest-origin `rng_draw`, and reserves it for the named role.  There is no
attacker-origin RNG constructor and no action that places a scalar on the
network.

`ActStart` has no scalar argument.  It can invoke
`initiator_step ... (StartInitiator x)` only by consuming
`sys_init_pending = Some x`.  A responder delivery of Msg1 can invoke
`responder_step` only by consuming `sys_resp_pending = Some y` and forcing the
local after-state's scalar to be exactly `y`.  Thus the responder local
relation may remain nondeterministic in isolation, while the composed system
removes that nondeterminism at the ideal RNG boundary.

`system_rng_wf` requires:

* `rng_no_reuse sys_rng`;
* every pending initiator/responder scalar has a matching honest registry draw;
* every scalar already consumed into either endpoint state has a matching
  role-correct registry draw.

`system_step` requires `system_rng_wf` of both its before- and after-state.  In
particular, legal composed executions cannot reuse a concrete scalar.
`lemma_rng_step_records_fresh` exposes the fresh registry extension as a
machine-checked fact.

The symbolic product mirrors this state with `ps_rng : list rng_shadow` and
`sh_pending` fields.  `rng_coherent` pairs every concrete registry draw with
the exact `eph_term rs_pos` whose trace entry is
`RandGen eph_usage eph_label eph_len`; `rng_option_binding` ties pending and
consumed concrete scalars to their corresponding symbolic terms.  Only
`ActRng` runs `rng_run`/`mk_rand`.  Start and responder-response transitions
consume an already generated term and never invent a symbolic representative.

`eph_label who = role_label who`, where `role_label` is the role's
`principal_state_label`.  The scalar is private while that role remains
uncorrupted and becomes compromise-exposed through the role's current
`SetState`; only `share_term scalar = dh_pk scalar` is sent directly.  This is
the precise ideal claim: generation is fresh, role-owned, non-reusing, and
private modulo state compromise.  It is not a computational claim about an
external RNG.

## 3. Fixed role identities

This is a fixed two-party sample.  DY key/event attribution uses:

```fstar
let init_dy_principal = "DH.Sample.Initiator"
let resp_dy_principal = "DH.Sample.Responder"

let lemma_role_principals_distinct ()
  : Lemma (init_dy_principal =!= resp_dy_principal)
```

All initiator setup/start/finish events use `init_dy_principal`; all responder
setup/respond/finish events use `resp_dy_principal`.  No injectivity property of
a concrete-principal-to-string encoding is needed or assumed.

Concrete four-byte principals are still load-bearing protocol data:
`term_of_principal` embeds them in symbolic messages, partner identities remain
in `transcript_term`, and the concrete signed transcript remains unchanged.
Role attribution and transcript bytes are intentionally separate.

## 4. Exact honest network provenance

Each concrete packet records `Sent Init`, `Sent Resp`, or `Injected`.  Each
symbolic `net_entry` records the exact `sym_msg`, its `MsgSent` position, and an
exact authentication context:

```fstar
type net_auth =
  | NoAuth
  | RespAuth : partner:bytes -> peer_share:bytes -> net_auth
  | InitAuth : partner:bytes -> my_share:bytes -> peer_share:bytes -> net_auth
```

For a `Sent Resp` Msg2, `smsg_provenance` requires the signature field to be
exactly:

```fstar
sig_term responder_shadow.sh_ltk
  (signonce_term (auth_nonce_pos ne.ne_pos))
  (transcript_term partner exact_received_gx exact_sent_gy)
```

For a `Sent Init` Msg3, it requires exactly:

```fstar
sig_term initiator_shadow.sh_ltk
  (signonce_term (auth_nonce_pos ne.ne_pos))
  (transcript_term partner exact_initiator_gx exact_received_gy)
```

There is no existential “some signing key / nonce / transcript” authentication
fact.  The key is the exact role shadow key, the nonce is fixed by the send
position, and the transcript is built from the exact structured shares stored
when the honest send occurred.  `lemma_sent_resp_msg2_exact` and
`lemma_sent_init_msg3_exact` expose these equations.

For a `Sent Init` Msg1, `lemma_sent_init_msg1_exact` exposes the exact
`SMsg1` identity and a `share_term` of a trace-recorded scalar.  Msg1 delivery is
UNRESTRICTED — an injected Msg1 (all fields public literals) can drive the
responder to `Resp_Wait3`.  The honest initiator's Msg1 packet is instead
selected at COMPLETION, by the run link (`sys_resp_msg1_idx == sys_init_msg1_idx`
records the responder consumed the initiator's own `Sent Init` packet); the
Security module then applies `lemma_sent_init_msg1_exact` to that packet.

An injected packet is exactly `inject_smsg m`, with all fields public literals.
It cannot satisfy an honest authentication constructor.  Delivery indexes the
immutable network shadow and passes its `ne_smsg` to the receiver.
`lemma_coherent_delivery_reads_exact` proves that `recv_msg ne.ne_pos` returns
exactly `flatten ne.ne_smsg`; no delivery re-embeds or substitutes terms.

The concrete toy digest is forgeable.  Consequently, a completion additionally
requires honest peer packet origin (`deliver_origin_ok`) AND the run/session
link (`ideal_completion_link_ok`).  This is an ideal signature-unforgeability
boundary, not a computational theorem about the toy digest.

## 5. Local-machine projection and the Pulse boundary

The composition contains the unchanged role relations literally.  The explicit
facts are:

```fstar
let lemma_start_projects_local ... :
  Lemma
    (requires system_step st0 (LocalEvent ActStart) st1 out)
    (ensures exists x.
      st0.sys_init_pending == Some x /\
      initiator_step st0.sys_init
        (LocalEvent (StartInitiator x)) st1.sys_init out)

let lemma_delivery_projects_local ... :
  Lemma
    (requires system_step st0 (LocalEvent (ActDeliver idx dst)) st1 out)
    (ensures
      idx < length st0.sys_net /\
      match dst with
      | Init -> initiator_step ... (WireEvent delivered.pk_msg) ...
      | Resp -> responder_step ... (WireEvent delivered.pk_msg) ...)
```

Therefore every composed start/delivery transition has the corresponding local
projection.  Conversely, not every arbitrary local transition is a composed transition:
composition also enforces private RNG provenance, concrete no-reuse, and the
`ideal_completion_link_ok` run/session-link completion boundary (Msg1 delivery
itself is unrestricted).

The Pulse `Common.ProtocolImplementation.protocol_implementation` instance in
`DH.Sample.Impl.Endpoint` refines the **local** initiator/responder wire-format
state machines.  The ideal RNG, run-link/completion boundary, and
network composition are environment assumptions supplied by `DH.Sample.System`
and the symbolic product.  Pulse refines **only the local endpoint machines**;
it does not refine or implement this environment.  We do **not** claim that an
arbitrary raw-byte Pulse network or arbitrary scalar-producing runtime refines
this ideal composed system.

## 6. Full honest run

For distinct concrete scalars (`x =!= y`), the honest schedule is:

```text
ActRng Init x
ActStart
ActRng Resp y
ActDeliver 0 Resp
ActDeliver 1 Init
ActDeliver 2 Resp
```

`lemma_honest_run_reaches` proves both endpoints finish, the concrete keys
agree, both scalars have role-correct registry provenance, and the final
registry is no-reuse.  `lemma_honest_system_run` additionally lifts that full
run to a product execution with exact projection.  Both completion deliveries
route the actual prior honest packet.

## 7. Ideal versus computational claims

Established here:

* concrete scalar freshness/no-reuse and role provenance in every legal
  composed step;
* one role-state-labelled DY `RandGen` for each concrete ideal RNG draw;
* fixed distinct role principals for DY key/event attribution;
* exact role-key, nonce-position, transcript, share, and delivery provenance
  for honest signature-bearing packets;
* a total, no-symbolic-witness lift of every composed execution;
* a complete non-vacuous honest run.

Not claimed here:

* computational security of the toy DH/signature functions;
* refinement from an arbitrary raw-byte network/RNG runtime to the ideal
  composed environment;
* a final authentication or session-key-secrecy theorem under corruption.

## 7b. Dynamic compromise in the lift

`Sys.sys_action` has a fifth constructor, `ActCorrupt who`, and `sym_extend` has
a matching seventh case.  The lift handles it like any other action:

```fstar
| SM.LocalEvent (ActCorrupt who) ->
  let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
  let (_, tr') = corrupt_run sh.sh_state_pos p0.ps_trace in
  Some (tr', p0.ps_init, p0.ps_resp, p0.ps_net, p0.ps_rng)
```

* **Deterministic**: the corrupted position is READ OFF the target role's own
  shadow (`sh_state_pos`, its current-state pointer), never supplied by a caller.
* **Shadow-preserving**: no key material, packet or RNG entry changes; only the
  trace records the compromise (`lemma_lift_step_corrupt` therefore discharges
  every `wf` component by pure trace growth).
* **State-changing actions now also write a `SetState`.**  Setup, `ActRng`,
  `ActStart`, the responder's Msg1 delivery and the initiator's Msg2 delivery
  each end with `set_state` storing the acting role's refreshed snapshot, and the
  lift moves that role's pointer to the new entry (positions n+1 / n+2 / n+3 as
  listed in `SYMBOLIC_SECURITY.md` §0.2).  The responder's Msg3 completion writes
  none: it changes its phase, not its key material.
* **Fixed setup positions** are named, not hard-coded numerals:
  `role_ltk_pos Init = 0`, `role_setup_state_pos Init = 2`,
  `role_ltk_pos Resp = 3`, `role_setup_state_pos Resp = 5`.
* `wf` gained one conjunct, `state_state_coherent`, pinning each role's pointer
  to a `SetState` of that role holding EXACTLY its current snapshot — this is
  what makes `ActCorrupt` hand the attacker exactly the live material.

The one-step lift `lemma_lift_step` and the whole-execution lift are otherwise
unchanged, and still take **no caller-provided symbolic witness**.

## 8. Verification

From the repository root, the required from-scratch check is:

```sh
make -C dh-sample clean && make -C dh-sample -j$(nproc) verify check-admits check-symbolic-forbidden
```

It verifies the DY-free spec, Pulse local implementation, and all symbolic
modules; rejects admits/assumes/`assert_norm`; and checks that symbolic sources
use no DY example module.
