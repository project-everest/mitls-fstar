# DH Sample: Protocol Invariant (`DH.Sample.Symbolic.Invariant`)

This is the audit guide for `DH.Sample.Symbolic.Invariant`, the module that
installs the DY* CORE `protocol_invariants` instance for the DH sample and
proves the case-exhaustive one-step preservation and reachability theorems
over the COMBINED coherence + trace invariant

```fstar
let product_invariant (p:product_state) : prop =
  wf p /\
  TI.trace_invariant #dh_sample_protocol_invariants p.ps_trace /\
  corruption_coherent p
```

The third conjunct is what makes this a **dynamic-compromise** model: the
product genuinely performs DY* `set_state` and `corrupt` operations, and
`corruption_coherent` reconciles the concrete per-role compromise flags of
`DH.Sample.System` with real `Corrupt` entries and with corruption of the roles'
state labels (§3.2).  There is **no** no-corruption profile here any more.

It depends ONLY on the DY* CORE library and on
`DH.Sample.Symbolic.{Terms,Product,Lifting,Provenance}` (all DY*-core-only —
see `SYMBOLIC_LIFTING.md`).  It never imports, opens or reuses any DY*
example, and never references an example module.

**Every installed predicate/profile field is a genuinely INHABITED `prop`.**
None of `dh_aead_pred`, `dh_pke_pred`, `dh_mac_pred`, `dh_sign_pred`,
`dh_state_pred`, `dh_event_pred_fun` is `False` or the library's
`False`-valued `default_*_predicate`; no comment in this file or in the code
endorses a `False` profile.  `False` appears in this module ONLY where it is
unavoidable inside a proof that pattern-matches an impossible
constructor/step (e.g. a `None` branch of `sym_extend` a hypothesis already
rules out) — never as an installed predicate or a vacuous precondition.

## 1. The `protocol_invariants` instance

```fstar
instance dh_sample_crypto_usages     : B.crypto_usages     = B.default_crypto_usages
let      dh_aead_pred                : B.aead_crypto_predicate #dh_sample_crypto_usages = { pred = dh_aead_pred_fun; pred_later = dh_aead_pred_later }
let      dh_pke_pred                 : B.pke_crypto_predicate  #dh_sample_crypto_usages = { pred = dh_pke_pred_fun;  pred_later = dh_pke_pred_later  }
let      dh_mac_pred                 : B.mac_crypto_predicate  #dh_sample_crypto_usages = { pred = dh_mac_pred_fun;  pred_later = dh_mac_pred_later  }
let      dh_sign_pred                : B.sign_crypto_predicate #dh_sample_crypto_usages = { pred = dh_sign_pred_fun; pred_later = dh_sign_pred_later }
let      dh_sample_crypto_predicates : B.crypto_predicates #dh_sample_crypto_usages = {
           aead_pred = dh_aead_pred;  pke_pred = dh_pke_pred;
           sign_pred = dh_sign_pred;  mac_pred = dh_mac_pred }
instance dh_sample_crypto_invariants : B.crypto_invariants  = { usages = dh_sample_crypto_usages; preds = dh_sample_crypto_predicates }
let      dh_state_pred               : TI.state_predicate #dh_sample_crypto_invariants = { pred = dh_state_pred_fun; pred_later = dh_state_pred_later; pred_knowable = dh_state_pred_knowable }
let      dh_event_pred_fun           : TB.trace -> T.principal -> string -> BT.bytes -> prop  (* exact-disjunction, role-pinned + shape predicate, §4 *)
let      dh_sample_trace_invariants  : TI.trace_invariants #dh_sample_crypto_invariants = { state_pred = dh_state_pred; event_pred = dh_event_pred_fun }
instance dh_sample_protocol_invariants : TI.protocol_invariants = { crypto_invs = dh_sample_crypto_invariants; trace_invs = dh_sample_trace_invariants }
```

* **AEAD / PKE / MAC predicates** (`dh_aead_pred` / `dh_pke_pred` /
  `dh_mac_pred`, §1.1 below): this sample never forms an AEAD ciphertext, a
  PKE ciphertext, or a MAC — grep `DH.Sample.Symbolic.Terms`/`Product`: there
  is no `aead_enc`, `pke_enc`, or `mac` call anywhere — so these predicates
  are never invoked on a reachable trace, but they are installed as
  genuinely INHABITED, real, harmless predicates, never the library's
  `False`-valued `default_*_predicate`.

* **Signature predicate** (`dh_sign_pred`, the one the audit scrutinises
  exactly — see §2 below).  Unchanged from before: already exact and
  inhabited, never `True`, never `False`.

* **State predicate** (`dh_state_pred`, §3 below): genuinely inhabited,
  never `False`.

* **Event predicate** (`dh_event_pred_fun`, §4 below): an EXACT DISJUNCTION
  over the five reserved tags, role-pinned AND shape-exact per tag, genuinely
  inhabited, never `True`, never `False` — and, unlike a conjunction of
  implications, genuinely rejects any event tagged outside that vocabulary.

### 1.1 The AEAD / PKE / MAC predicates — genuinely inhabited, never `False`

AEAD, PKE and MAC are never used by this sample, so their exact content
cannot affect `product_invariant` — but they still must be REAL, INHABITED
predicates, never the library's `default_*_predicate` (`fun ... -> False`).
The predicate installed for all three is:

```fstar
let dh_aead_pred_fun tr key_usage key nonce msg ad : prop =
  B.get_label #dh_sample_crypto_usages tr msg == L.public
(* dh_pke_pred_fun / dh_mac_pred_fun: the same condition on the message/plaintext *)
```

i.e. "honest use (were it ever to occur) is restricted to
encrypting/MACing an ALREADY-PUBLIC payload" — phrased with `B.get_label`
(needing only the `crypto_usages` instance already in scope at this point of
the file) rather than `B.is_publishable`/`B.is_knowable_by` (which need the
FULL `crypto_invariants` instance being assembled here — using it in one of
its own fields would be circular).

* Genuinely INHABITED: `B.get_label` is UNCONDITIONALLY `L.public` for a
  `Literal` term (`DY.Core.Bytes.get_label`'s very first case, no
  `bytes_well_formed` side condition needed), so e.g. `msg = B.literal_to_bytes
  lit` satisfies it on EVERY trace.
* NOT `True`: a bare secret-labelled term — e.g. the raw `Rand eph_len time`
  ephemeral scalar underlying a `share_term` — has `get_label = eph_label =
  role_label who`, which is NOT `L.public` (`DH.Sample.Symbolic.Terms.eph_label`),
  so it genuinely rejects a real, non-degenerate case.
* `pred_later` holds by `B.get_label_later`, using exactly the
  `bytes_well_formed` hypothesis each predicate's own `pred_later` obligation
  already supplies — no extra premise invented.

## 2. The signature authorization predicate — exact, no weakening

```fstar
let dh_sign_pred_fun
  (tr:TB.trace) (sk_usage:BT.usage{BT.SigKey? sk_usage}) (vk:BT.bytes) (msg:BT.bytes)
  : prop =
  (vk == vkey_term (ltk_term (role_ltk_pos Init)) /\
     TB.event_triggered tr init_dy_principal tag_initiator_finish msg) \/
  (vk == vkey_term (ltk_term (role_ltk_pos Resp)) /\
     TB.event_triggered tr resp_dy_principal tag_responder_respond msg)
```

Read against `DY.Core.Bytes.bytes_invariant`'s `Sign` case, this says: a
signature `Sign sk nonce msg` is honestly well-formed ONLY IF EITHER

* `Vk sk` is EXACTLY the initiator's fixed verification key
  (`vkey_term (ltk_term (role_ltk_pos Init))`, where `role_ltk_pos Init = 0`)
  AND the INITIATOR role principal
  (`init_dy_principal`) has `event_triggered` `tag_initiator_finish` with
  content EXACTLY `msg` (the very message parameter, not a separately
  quantified "some transcript"),

* OR `Vk sk` is EXACTLY the responder's fixed verification key
  (`vkey_term (ltk_term (role_ltk_pos Resp))`, where
  `role_ltk_pos Resp = 3`) AND the RESPONDER role principal
  (`resp_dy_principal`) has `event_triggered` `tag_responder_respond` with
  content EXACTLY `msg`.

There is **no `True` disjunct** (never inhabited by a vacuous case), **no
existential over "some key"** (the key is compared by `==` to one of exactly
two literal terms), and **no existential over "some event"**
(`event_triggered` is checked for the fixed role principal and fixed tag
with content equal to `msg` itself).  It is genuinely inhabited (every
honest signature this product model creates satisfies it — §5) and genuinely
NOT `True` (a signature by either fixed key over any OTHER content, or by any
OTHER key, violates it).

**Authorization precedes the signature — enforced by `trace_invariant`
itself, not assumed.**  `DY.Core.Trace.Invariant.trace_invariant` is defined
by recursion on `Snoc`:

```fstar
let rec trace_invariant tr =
  match tr with
  | Nil -> True
  | Snoc tr_init entry -> trace_entry_invariant tr_init entry /\ trace_invariant tr_init
```

so a `MsgSent` entry carrying a `Sign` term is checked against
`tr_init` — the trace **strictly before** that entry — via
`is_publishable tr_init msg` (`DY.Core.Bytes.bytes_invariant`'s `Sign` case
calls `sign_pred.pred tr_init sk_usg (Vk sk) inner_msg`).  Consequently
`dh_sign_pred` being satisfiable for a signature carried at trace position
`pos` REQUIRES the authorizing `Event` to be `event_triggered` on a trace of
length `< pos`, i.e. on a **STRICT PRIOR PREFIX**.  `Product.respond_run` /
`Product.ifinish_run` trigger the authorization event, THEN draw the signing
nonce, THEN send — so the ordering `dh_sign_pred` requires is EXACTLY the
ordering the product already produces (`DH.Sample.Symbolic.Provenance`'s
`lemma_respond_authorizes_before_sign` / `lemma_ifinish_authorizes_before_sign`
independently exhibit this same "authorization strictly before the `MsgSent`
carrying the signature" fact from the genuine trace-monad segments).  There
is no circularity: the event's content is fixed BEFORE the signature exists
(the transcript, not the signature, is the event content), and the signature
predicate is checked against the PREFIX before its own entry, never against
itself.

## 3. The state predicate — real, EXERCISED, and genuinely inhabited

`Product.setup_run`, `rng_run`, `start_run`, `respond_run` and `ifinish_run` ALL
call `DY.Core.Trace.Manipulation.set_state`; `Product.corrupt_run` calls DY*
core's `corrupt`.  So `SetState` and `Corrupt` entries are genuinely produced by
this development, and the state predicate is exercised on **every** trace it
reaches.  It is the canonical DY* rule:

```fstar
let dh_state_pred_fun tr prin sess_id content : prop =
  B.is_knowable_by #dh_sample_crypto_invariants
    (L.principal_state_label prin sess_id) tr content
```

i.e. "a principal only ever stores material that is **knowable at its own state
label**".  This is exactly what makes a later `Corrupt` of that state sound: DY*'s
attacker theorem turns a corrupted state into publishable content, and the label
discipline guarantees the leaked material was already accounted for by that
role's compromise-sensitive `Terms.role_label`.

* **Genuinely inhabited**: any public literal is knowable at any label
  (`lemma_state_pred_inhabited`); and — the case that matters — every snapshot
  this product stores satisfies it (`lemma_snapshot_knowable`, used at all five
  `SetState` sites).
* **NOT `True`**: a `Rand` term that was never generated on the trace is not even
  `bytes_invariant`, hence not storable (`lemma_state_pred_not_trivial`).
* **`pred_later`** is `bytes_invariant_later` + `get_label_later` +
  `can_flow_later`.
* **`pred_knowable` is discharged from the GENUINE label lattice**, never from a
  `False` hypothesis: a role's state label flows to the state-CONTENT label of
  anything it stores (`L.state_pred_label_can_flow_state_pred_label`), so
  knowability at the former transitively gives knowability at the latter.

### 3.1 What a snapshot contains, and when it is written

The stored content is `Terms.snapshot_term ltk pending scalar peer_share key`
(absent fields rendered as the public empty literal), i.e. the role's **complete
live secret material**.  `Product.wf` pins the role shadow's `sh_state_pos` — its
*current-state pointer* — to a `SetState` holding exactly that snapshot
(`state_pos_coherent`).  Snapshots are refreshed after every state-changing role
action (setup, `ActRng`, `ActStart`, the responder's Msg1 delivery, the
initiator's Msg2 delivery); the responder's **Msg3 completion writes nothing**
because it changes only its phase, not its key material.  Nothing is ever erased,
so there is **no forward secrecy** (see `SYMBOLIC_SECURITY.md` §0).

### 3.2 Compromise coherence

`corruption_coherent` (a conjunct of `product_invariant`, marked
`opaque_to_smt` so its `forall` does not pollute unrelated queries) states:

```fstar
(p.ps_sys.sys_init_corrupt ==> role_state_corrupt p Init) /\
(p.ps_sys.sys_resp_corrupt ==> role_state_corrupt p Resp) /\
(forall (time:nat). TB.entry_exists p.ps_trace (T.Corrupt time) ==>
   corrupt_entry_authorized p time)
```

where `corrupt_entry_authorized p time` says the `Corrupt` entry points at a
`SetState` of a role whose compromise flag is set.  It is inductive: no
non-`ActCorrupt` step adds a `Corrupt` entry (`product_step_no_new_corrupt`,
proved case by case exactly like the trace-invariant family), and `ActCorrupt who`
adds exactly one, at that role's current pointer, while setting that role's flag
(`lemma_corruption_coherent_corrupt`).  `lemma_corruption_coherence` then derives
the **iff** between flags and DY* label corruption.

## 4. The event predicate — EXACT disjunction over the five reserved tags

```fstar
let dh_event_pred_fun tr p tag content : prop =
  (tag == tag_keygen /\
     (p == init_dy_principal \/ p == resp_dy_principal) /\
     (exists me vk.        content == keygen_content me vk))            \/
  (tag == tag_initiate /\
     p == init_dy_principal /\
     (exists me peer share. content == initiate_content me peer share))  \/
  (tag == tag_initiator_finish /\
     p == init_dy_principal /\
     (exists partner gx gy. content == auth_content partner gx gy))       \/
  (tag == tag_responder_respond /\
     p == resp_dy_principal /\
     (exists partner gx gy. content == auth_content partner gx gy))      \/
  (tag == tag_responder_finish /\
     p == resp_dy_principal /\
     (exists peer key.      content == session_content peer key))
```

**This is an EXACT DISJUNCTION, not a conjunction of implications.** A
conjunction of implications (`tag == t1 ==> P1 /\ tag == t2 ==> P2 /\ ...`) is
satisfied VACUOUSLY by any `Event` whose tag is none of the reserved tags:
every implication's antecedent is false, so the conjunction holds trivially
for that tag, for ANY principal and ANY content — that is not a "strong"
predicate. The disjunction above instead genuinely REJECTS an event tagged
outside the five-tag vocabulary: none of the five disjuncts' leading `tag ==
t_i` conjunct can hold, so the whole disjunction is false.

Beyond the shape obligation, each disjunct PINS the exact triggering
principal per tag: `Product.setup_run`'s two call sites in
`Product.product_initial` pass literally `init_dy_principal` and
`resp_dy_principal`; `start_run` / `ifinish_run`'s only call sites pass
literally `init_dy_principal`; `respond_run` / `rfinish_run`'s only call
sites pass literally `resp_dy_principal` (grep
`DH.Sample.Symbolic.Product` — every one is a fixed literal, never a free
variable).  So `dh_event_pred_fun` requires `tag_initiate` /
`tag_initiator_finish` events to be triggered ONLY by `init_dy_principal`,
`tag_responder_respond` / `tag_responder_finish` events ONLY by
`resp_dy_principal`, and `tag_keygen` events by EITHER (both roles set up a
long-term key).

**Why the strengthening is sound, not merely convenient.** The ONLY place any
`Event` trace entry is ever appended by this product is inside one of
`Product.setup_run` / `start_run` / `respond_run` / `ifinish_run` /
`rfinish_run`. `Product.sys_action` — `ActRng | ActStart | ActDeliver |
ActInject` — has no constructor that lets ANY other code path (in particular,
no constructor that lets the attacker) trigger an `Event` with an arbitrary
tag; `ActInject` only ever appends a `MsgSent`, never an `Event`. So every
`Event` entry this product's step relation can EVER append already has one of
the five exact shapes above, and rejecting every other tag costs nothing this
development's proofs need — DY* CORE's `trace_entry_invariant` (§0 recap: `|
Event prin tag content -> event_pred tr prin tag content`) checks
`dh_event_pred_fun` against every `Event` entry unconditionally, regardless of
who or what triggered it, so this is not a premise smuggled past the check —
it is exactly what the check enforces, made stronger.

It is inhabited (every event this product model ever triggers satisfies
exactly one of these five disjuncts, with exactly the role principal pinned
above — discharged by the `lemma_*_event_pred` lemmas with an explicit
witness, never by an unassisted existential search) and it is NOT `True`: an
event using one of the five reserved tags with the WRONG principal, or with
content that is not of the corresponding shape, OR an event using ANY OTHER
tag whatsoever, violates it.  This is the structural fact the proofs in `DH.Sample.Symbolic.Security` use to recover the
exact partner / share / key fields — AND the exact role that produced them —
out of a trace-recorded event uniformly, without guessing, AND to rule out any
event outside the five-tag vocabulary altogether.

## 5. Per-action mapping: entries appended, predicates discharged

`Product.sym_extend`'s seven shapes, the trace entries each appends, and the
lemma that discharges `trace_entry_invariant` for every one of them:

| Action (event) | Entries appended | `trace_entry_invariant` obligation(s) | Discharged by |
|---|---|---|---|
| `ActRng owner x` | `RandGen eph_usage (eph_label owner) eph_len`, `SetState` (owner's refreshed snapshot) | `RandGen` ⟹ `True`; the `SetState` needs the state predicate | `lemma_step_trace_invariant_rng` → `lemma_rng_trace_invariant` (`lemma_ltk_knowable` + `lemma_scalar_knowable` + `lemma_snapshot_knowable`) |
| `ActStart` (initiator sends Msg1) | `Event tag_initiate`, `MsgSent (SMsg1 me share)`, refreshed `SetState` | event shape + `p == init_dy_principal`; `is_publishable` of `concat me (dh_pk scalar)`; snapshot state predicate | `lemma_step_trace_invariant_start`: `lemma_initiate_event_pred` (called with `mep = init_dy_principal`); `literal_to_bytes_is_publishable` (identity) + `lemma_share_publishable` (share, from `rng_state_coherent`'s recorded pending scalar) + `concat_preserves_publishability`; `lemma_snapshot_knowable` |
| `ActDeliver idx Resp` on Msg1 (responder sends Msg2) | `Event tag_responder_respond`, `RandGen` (nonce), `MsgSent (SMsg2 me share sig)`, refreshed `SetState` | event shape + `p == resp_dy_principal`; `is_publishable` of the SIGNATURE, hence `dh_sign_pred`'s responder disjunct; snapshot state predicate | `lemma_step_trace_invariant_resp_msg1` → `lemma_respond_trace_invariant`: Msg1 delivery is UNRESTRICTED (any origin, including an injected packet, can drive it); `lemma_responder_respond_event_pred` fixes `mep = resp_dy_principal`; the origin-generic helper `lemma_net_entry_share_publishable` proves publishability for honest AND injected shares, and `lemma_share_publishable` handles the responder share; `lemma_sig_term_publishable` discharges the signature from the JUST-triggered `tag_responder_respond` event over that EXACT transcript; `lemma_snapshot_knowable` |
| `ActDeliver idx Resp` on Msg3 (responder completes) | `Event tag_responder_finish` | event shape + `p == resp_dy_principal` | `lemma_step_trace_invariant_resp_msg3` → `lemma_rfinish_trace_invariant`: `lemma_responder_finish_event_pred` (called with `mep = resp_dy_principal`) |
| `ActDeliver idx Init` on Msg2 (initiator sends Msg3) | `Event tag_initiator_finish`, `RandGen` (nonce), `MsgSent (SMsg3 sig)`, refreshed `SetState` | event shape + `p == init_dy_principal`; `is_publishable` of the bare SIGNATURE, hence `dh_sign_pred`'s initiator disjunct; snapshot state predicate | `lemma_step_trace_invariant_init_msg2` → `lemma_ifinish_trace_invariant`: `lemma_initiator_finish_event_pred` (called with `mep = init_dy_principal`); `lemma_net_entry_share_publishable` (received Msg2 share) + `lemma_share_publishable` (own share) build the transcript; `lemma_sig_term_publishable` discharges the signature from the JUST-triggered `tag_initiator_finish` event; `lemma_snapshot_knowable` |
| `ActInject m` (attacker injection) | `MsgSent (inject_smsg m)` | `is_publishable` of the all-literal term | `lemma_step_trace_invariant_inject` → `lemma_inject_trace_invariant`: `DH.Sample.Symbolic.Provenance.lemma_inject_publishable` (publishable on ANY trace under ANY crypto invariants) |
| `ActCorrupt who` | `Corrupt sh_state_pos` | no new `trace_entry_invariant` premise; DY* validates compromise through the previously checked state predicate | `lemma_step_trace_invariant_corrupt` uses core `corrupt_invariant`; `lemma_corruption_coherent_corrupt` ties the entry to the target role's flag and exact current `SetState` |

`Common.StateMachine`'s non-transition shapes (a `WireEvent`, or a delivery
whose `(destination, message)` pair fires no endpoint step) make
`Sys.system_step` — hence `product_step` (which conjoins it) — `False` (the
one place this development ever has `False` at all, and only as a
pattern-matched hypothesis that is already ruled out, never as an installed
predicate), so every remaining case of `product_step_preserves_invariant`'s
dispatch is vacuously discharged, exactly mirroring
`DH.Sample.Symbolic.Lifting.lemma_lift_step`'s own exhaustive dispatch.

**`SetState` and `Corrupt` are real actions here.**  Every state-changing row
above additionally appends the acting role's refreshed `SetState`, whose state
predicate is discharged by `lemma_snapshot_knowable` (long-term key and ephemeral
knowable at the role's own label by reflexivity; peer share publishable hence
knowable; session key `dh scalar peer_share` knowable because
`join (role_label who) _` flows to `role_label who`).  The seventh action,
`ActCorrupt who`, appends exactly one `Corrupt sh_state_pos` entry, which carries
**no** `trace_entry_invariant` obligation — precisely DY* core's own
`corrupt_invariant` — because the burden was already discharged by the state
predicate when that snapshot was stored.

**Honest `MsgSent` publishable from bytes invariants / crypto predicates.**
Every honest send above is discharged from `DY.Core.Bytes.bytes_invariant`'s
OWN structural cases (`Rand`, `Concat`, `DhPub`, `Sign`) plus `dh_sign_pred`
— never from an ad-hoc assumption.  **Injected `MsgSent` publishable** is
`Provenance.lemma_inject_publishable`, itself proved from the all-literal
structure of `inject_smsg`.

## 6. Theorem signatures

```fstar
(* the combined invariant *)
let product_invariant (p:product_state) : prop =
  wf p /\
  TI.trace_invariant #dh_sample_protocol_invariants p.ps_trace /\
  corruption_coherent p

(* compromise coherence, in BOTH directions *)
let lemma_corruption_coherence (p:product_state)
  : Lemma (requires product_invariant p)
          (ensures (p.ps_sys.sys_init_corrupt <==> role_state_corrupt p Init) /\
                   (p.ps_sys.sys_resp_corrupt <==> role_state_corrupt p Resp))

(* the case-exhaustive one-step preservation theorem *)
let product_step_preserves_invariant
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_invariant p0 /\ product_step p0 ev p1 out)
    (ensures product_invariant p1)

(* the initial state satisfies the invariant *)
let lemma_product_initial_invariant (a b:principal)
  : Lemma (ensures product_invariant (product_initial a b))

(* execution induction over Common.StateMachine.trace_reaches *)
let rec product_trace_reaches_preserves_invariant
  (a b:principal) (p0:product_state) (pt:list product_transition) (p1:product_state)
  : Lemma
    (requires product_invariant p0 /\ SM.trace_reaches (product_sm a b) p0 pt p1)
    (ensures product_invariant p1)
    (decreases pt)

(* the headline reachable-state theorem *)
let product_reaches_invariant
  (a b:principal) (pt:list product_transition) (pfinal:product_state)
  : Lemma
    (requires product_execution (product_sm a b) (product_initial a b) pt pfinal)
    (ensures product_invariant pfinal)

(* the explicit, named corollary surfacing the exact DH / random-generation
   ingredients product_invariant already guarantees: for the long-term keys
   and for every currently-recorded ephemeral scalar, the exact usage/label/
   length and RandGen provenance (proved by () alone — plain unfolding of the
   non-opaque wf conjunction; see §2 below) *)
let lemma_product_invariant_key_provenance (p:product_state)
  : Lemma
    (requires product_invariant p)
    (ensures (
      let c = p.ps_sys in
      ltk_coherent_at init_dy_principal (term_of_principal c.sys_init.ep_me)
        p.ps_trace p.ps_init.sh_ltk (role_ltk_pos Init) /\
      ltk_coherent_at resp_dy_principal (term_of_principal c.sys_resp.ep_me)
        p.ps_trace p.ps_resp.sh_ltk (role_ltk_pos Resp) /\
      (match p.ps_init.sh_scalar with
       | None -> True | Some s -> scalar_recorded_for Init p.ps_trace s) /\
      (match p.ps_resp.sh_scalar with
       | None -> True | Some s -> scalar_recorded_for Resp p.ps_trace s) /\
      state_pos_coherent Init p.ps_init p.ps_trace /\
      state_pos_coherent Resp p.ps_resp p.ps_trace))

(* COMPROMISE COHERENCE — replaces the former no-corruption profile entirely *)
let corruption_coherent (p:product_state) : prop =        (* opaque_to_smt *)
  (p.ps_sys.sys_init_corrupt ==> role_state_corrupt p Init) /\
  (p.ps_sys.sys_resp_corrupt ==> role_state_corrupt p Resp) /\
  (forall (time:nat). TB.entry_exists p.ps_trace (T.Corrupt time) ==>
     corrupt_entry_authorized p time)

(* no step except ActCorrupt introduces a Corrupt entry — the structural fact
   that makes corruption_coherent inductive (case-exhaustive, same dispatch as
   the trace-invariant family) *)
let product_step_no_new_corrupt
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\ product_step p0 ev p1 out /\
      (forall (who:endpoint_id). ev =!= SM.LocalEvent (Sys.ActCorrupt who)))
    (ensures no_new_corrupt p0.ps_trace p1.ps_trace)

let product_step_preserves_corruption_coherent
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires wf p0 /\ corruption_coherent p0 /\ product_step p0 ev p1 out)
    (ensures corruption_coherent p1)

(* the iff between the concrete compromise flags and DY* label corruption *)
let lemma_corruption_coherence (p:product_state)
  : Lemma
    (requires product_invariant p)
    (ensures
      (p.ps_sys.sys_init_corrupt <==> role_state_corrupt p Init) /\
      (p.ps_sys.sys_resp_corrupt <==> role_state_corrupt p Resp))

let lemma_uncorrupt_role_label (p:product_state) (who:endpoint_id)
  : Lemma
    (requires product_invariant p /\ Sys.corrupt_flag p.ps_sys who == false)
    (ensures ~(role_state_corrupt p who))

(* the non-vacuous two-party honest-run witness: reachable, invariant-satisfying,
   with BOTH compromise flags clear and NEITHER role label corrupt *)
let lemma_honest_run_invariant_reachable (a b:principal) (x y:dh_scalar)
  : Lemma
    (requires x =!= y)
    (ensures (
      exists (pt:list product_transition) (pfinal:product_state).
        product_execution (product_sm a b) (product_initial a b) pt pfinal /\
        execution_projects_exactly (Sys.honest_run a b x y) pt /\
        proj pfinal == Sys.h_s4 a b x y /\
        product_invariant pfinal /\
        pfinal.ps_sys.sys_init_corrupt == false /\
        pfinal.ps_sys.sys_resp_corrupt == false /\
        ~(role_state_corrupt pfinal Init) /\
        ~(role_state_corrupt pfinal Resp)))
```

### 6.1 Proof structure

`product_step_preserves_invariant` proceeds by: (1) packaging `(ev, p1.ps_sys,
out)` into a `Sys.system_transition ctr` and showing `lift_next p0 ctr == p1`
(`lemma_product_step_is_lift_next` — both `product_step` and `lift_next` dispatch
through the SAME deterministic `sym_extend p0 ev`); (2) reusing
`DH.Sample.Symbolic.Lifting.lemma_lift_step` for the `wf` half; (3) dispatching
on `ev`'s shape, EXACTLY as `sym_extend` and `lemma_lift_step` do, to one of the
**seven** per-action lemmas (§5) for the `trace_invariant` half; (4) calling
`product_step_preserves_corruption_coherent` for the compromise-coherence half.

That last one splits into: the `ActCorrupt` case
(`lemma_corruption_coherent_corrupt`, which uses `Product.lemma_corrupt_step_effect`
— "the step appends exactly `Corrupt sh_state_pos`, and `wf` says that position
holds this role's current `SetState`" — plus `Terms.lemma_state_corrupt_implies_label_corrupt`),
and every other case (`product_step_no_new_corrupt` + `lemma_corruption_coherent_frame`,
using `is_corrupt`'s monotonicity and the persistence of `entry_at`).

It does NOT claim `trace_invariant` excludes `Corrupt`
(`DY.Core.Trace.Manipulation.corrupt_invariant` shows a `Corrupt` entry is ALWAYS
`trace_invariant`-compatible, for any protocol); it tracks *which* corruptions
happened and reconciles them with the concrete flags.

`lemma_product_invariant_key_provenance` is proved by `()` alone: neither
`product_invariant` nor `wf` nor `key_state_coherent`/`rng_state_coherent` is
marked `opaque_to_smt`, so the SMT solver unfolds the conjunction on its own.

## 7. Engineering note: keeping rlimits low

Every per-action "heavy" fact (transcript / signature publishability across
three appended entries) is proved by a STANDALONE, generic lemma
(`lemma_respond_trace_invariant`, `lemma_ifinish_trace_invariant`) that takes
ONLY plain `bytes` / `trace` parameters — no `product_state`, `system_step`,
or `sym_extend` in scope.  The "wiring" lemma that DOES need the full
product/system context (to identify which concrete call `sym_extend`
performed) then reuses that standalone fact as a black box.  The
"no new corruption" per-action lemmas (`lemma_step_no_new_corrupt_*`) mirror the
SAME wiring case-by-case, but their own concluding fact
(`no_new_corrupt_snoc`/`_snoc2`/`_snoc3`/`_snoc4`) is a one-line structural
unfolding, so they add negligible extra rlimit cost on top of the wiring they
share.  Two predicates are `opaque_to_smt` purely for cost: `no_new_corrupt` and
`corruption_coherent` (both carry a `forall (time:nat)` that must not be
instantiated in the many queries that only carry them in the context), as is
`Product.shadow_snapshot` (a five-way nested concatenation that per-step queries
only ever need as an atom). This
keeps every individual SMT query's context small; `--query_stats` over the
whole module shows a maximum observed `rlimit` usage well under the
`--z3rlimit 10` budget used throughout (no query anywhere needs more).
`is_publishable`'s persistence across a growing trace is likewise NOT left to
the library's `bytes_invariant_later` / `get_label_later` SMTPats to chain
unassisted through a compound (`Concat`/`DhPub`) term (this was empirically
expensive); `is_publishable_grows` calls those three lemmas explicitly
instead, and is defined immediately after `dh_sample_crypto_invariants` so
the (equally lightweight) state-predicate proofs in §3 can reuse it directly.

## 8. Verification

From the repository root:

```sh
make -C dh-sample clean && make -C dh-sample -j$(nproc) verify-symbolic-invariant check-admits check-symbolic-forbidden
make -C dh-sample -j$(nproc) verify
```

`verify-symbolic-invariant` verifies `DH.Sample.Symbolic.Invariant` (and,
incrementally, everything it depends on: the DY-free spec, `Terms`,
`Product`, `Lifting`, `Provenance`); `check-admits` rejects
admits/assumes/`assert_norm` anywhere in `spec/`, `impl/`;
`check-symbolic-forbidden` rejects any reference to a DY* example anywhere in
`spec/symbolic/`.  `verify` additionally re-verifies the DY-free spec and the
Pulse implementation.

## 9. What is — and is not — claimed

Established here, on top of `SYMBOLIC_LIFTING.md`'s claims:

* a genuine DY* CORE `protocol_invariants` instance where EVERY predicate
  field (AEAD, PKE, MAC, signature, state, event) is a genuinely INHABITED
  `prop` — none is `False`, none is the library's `False`-valued
  `default_*_predicate` — with an EXACT signature authorization predicate
  (pinned key, pinned principal/tag, exact message — no `True`, no
  existential weakening) and an EXACT DISJUNCTION event predicate, role-pinned
  and shape-exact PER TAG, that genuinely REJECTS any event tagged outside the
  five reserved protocol tags (not merely a conjunction of implications that
  an unrecognised tag would satisfy vacuously);
* `trace_invariant` is preserved by EVERY `product_step`, case-exhaustively,
  discharging `trace_entry_invariant` for every appended entry from
  `is_publishable` / `dh_sign_pred` / `Provenance.lemma_inject_publishable`;
* the combined `product_invariant` holds at `product_initial` and is
  therefore an invariant of every `product_execution`;
* `lemma_product_invariant_key_provenance`: an explicitly-named corollary
  surfacing the EXACT usage/label/length and RandGen provenance
  `product_invariant` already guarantees for both long-term signing keys and
  every currently-recorded ephemeral DH scalar — cited alongside the
  already-named signing-nonce (`lemma_sig_term_publishable`) and DH
  share/secret (`lemma_share_publishable`, `lemma_dh_agreement`) facts as the
  ingredients a later mutual-authentication / session-key-secrecy proof would
  consume;
* REAL DYNAMIC COMPROMISE: `Sys.ActCorrupt who` and the DY* core
  `SetState`/`Corrupt` machinery, with `corruption_coherent` proved inductive and
  `lemma_corruption_coherence` proving the **iff** between the concrete
  per-role compromise flags and DY* corruption of the roles' state labels — the
  former `product_no_corruption` / `ideal_product_invariant` "no-corruption ideal
  profile" is GONE, and no headline result assumes a `Corrupt`-free trace;
* a concrete, non-vacuous two-party honest run reaching a state satisfying
  `product_invariant` with BOTH compromise flags clear and NEITHER role label
  corrupt (so the compromise machinery does not secretly force corruption).

Not claimed by this module itself: computational security of the toy
DH/signature functions or refinement from an arbitrary raw-byte network/RNG
runtime to the ideal composed environment.  The authentication, agreement, and
session-key secrecy theorems modulo compromise are stated and proved by
`DH.Sample.Symbolic.Security`, using this module's invariant and provenance
lemmas.
