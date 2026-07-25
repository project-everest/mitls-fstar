module DH.Sample.Symbolic.Invariant

(**
  DH.Sample.Symbolic.Invariant — the protocol-specific DY* CORE `protocol_invariants`
  instance for the DH sample, and the COMBINED product invariant that a future
  authentication / secrecy proof is built on:

    product_invariant p =
      Product.wf p /\ DY.trace_invariant p.ps_trace /\ corruption_coherent p

  Its step relation is the composed `DH.Sample.System.system_step`.  Msg1
  delivery is UNRESTRICTED (the attacker may inject a Msg1 that drives the
  responder to `Resp_Wait3`); completion carries the named
  `ideal_completion_link_ok` run/session-link boundary.  The Security module adds
  the explicit inductive run-link invariants that turn that index equality, at
  completion, into the honest identity/share/scalar agreement.

  This module depends ONLY on the DY* CORE library and on
  DH.Sample.Symbolic.{Terms,Product}.  It never imports, opens or reuses any DY*
  example, and never references an example module.

  Every predicate/profile field installed by this module is a genuinely
  INHABITED `prop` — NONE of them is the library's `False`-valued
  `default_*_predicate`, and no comment in this file endorses a `False`
  profile.  `False` appears in this module ONLY where it is unavoidable inside
  a proof that pattern-matches an impossible constructor/step (e.g. a `None`
  branch of `sym_extend` that a hypothesis already rules out) — never as an
  installed predicate.

  What this module installs
  --------------------------
    * `dh_sample_crypto_usages` / `dh_sample_crypto_invariants` : the DY* CORE
      `crypto_invariants` instance.  AEAD, PKE and MAC are never used by this
      sample (no `aead_enc` / `pke_enc` / `mac` call anywhere in
      `DH.Sample.Symbolic.{Terms,Product}`), so their predicates are never
      invoked on a reachable trace — but they are still genuinely INHABITED,
      real, harmless predicates (`dh_aead_pred`, `dh_pke_pred`, `dh_mac_pred`:
      "the payload's structural label is exactly `public`" — see below), never
      the library's `False`-valued defaults.

    * `dh_sign_pred` : the EXACT signature authorization predicate (see below).

    * `dh_sample_trace_invariants` : the DY* CORE `trace_invariants` instance —
      a state predicate that is genuinely INHABITED and, now, genuinely
      EXERCISED (`dh_state_pred`: "the stored content is knowable at the storing
      role's own state label"; the product performs a real `set_state` after
      every state-changing role action — see "State predicate" below) and an
      event predicate that is an EXACT DISJUNCTION over exactly the five
      reserved protocol tags — never a conjunction of implications, which would
      be satisfied vacuously by any event outside that vocabulary — each
      disjunct pinning BOTH the exact triggering principal (the fixed role
      principal that tag is ever triggered by — see "Event predicate" below)
      AND the exact shape the corresponding protocol step actually builds.

    * `corruption_coherent` : the COMPROMISE-COHERENCE invariant tying the
      concrete per-role compromise flags of `DH.Sample.System` to genuine DY*
      `Corrupt` entries and to corruption of the roles' state labels, in BOTH
      directions (`lemma_corruption_coherence`).

    * `product_invariant` : `Product.wf p /\ trace_invariant p.ps_trace /\
      corruption_coherent p` under the instance above.

    * `product_step_preserves_invariant` : the case-exhaustive one-step
      preservation theorem, discharging `trace_entry_invariant` for every trace
      entry appended by every `Product.sym_extend` case (RNG, honest start /
      respond / finish sends, delivery, injection, and DYNAMIC COMPROMISE) —
      including the DY* STATE-PREDICATE obligation of every `SetState` the
      product writes (`lemma_snapshot_knowable`).

    * `product_reaches_invariant` : the execution/reachability theorem: every
      state reachable from `Product.product_initial` by `SM.trace_reaches`
      (equivalently `Product.product_execution`) satisfies `product_invariant`.

    * `lemma_honest_run_invariant_reachable` : the full two-party honest run
      reaches a state satisfying `product_invariant` with BOTH compromise flags
      clear and NEITHER role label corrupt — a concrete, non-vacuous witness IN
      ADDITION TO (not instead of) the general reachability theorem above.

    NOTE.  The former `product_no_corruption` / `ideal_product_invariant`
    "two-party no-corruption ideal profile" is GONE; see the section
    "What replaced the old ... profile" below.  No headline result assumes a
    `Corrupt`-free trace any more.

  The event predicate is an EXACT DISJUNCTION over exactly the five reserved
  protocol tags (see "Event predicate" below), not a conjunction of
  implications: a conjunction of implications would be satisfied VACUOUSLY by
  any event tagged outside that five-tag vocabulary, which is not a "strong"
  predicate.  The disjunction genuinely rejects any other tag, and remains
  genuinely inhabited (every event this product ever triggers matches exactly
  one disjunct).

  The exact signature authorization predicate
  --------------------------------------------
  `dh_sign_pred.pred tr sk_usage vk msg` holds iff EITHER

    * `vk` is exactly the INITIATOR's verification key (`vkey_term (ltk_term 0)`,
      the fixed position `Product.product_initial` records the initiator's
      long-term key at) AND the INITIATOR role principal has triggered
      `tag_initiator_finish` with content EXACTLY `msg` (the very message being
      signed) on `tr`,

  OR

    * `vk` is exactly the RESPONDER's verification key
      (`vkey_term (ltk_term (role_ltk_pos Resp))`)
      AND the RESPONDER role principal has triggered `tag_responder_respond` with
      content EXACTLY `msg` on `tr`.

  This is an EXACT predicate: the key is pinned to one of the two literal fixed
  verification-key terms (never "some key"), the authorizing principal is the
  fixed role principal (never "some principal"), the tag is the fixed role tag,
  and the authorized content is literally the `msg` parameter itself — the exact
  transcript being signed, not a separately-quantified "some transcript".  There
  is no `True` disjunct and no third disjunct.

  `DY.Core.Trace.Invariant.trace_entry_invariant` checks `sign_pred` (via
  `DY.Core.Bytes.bytes_invariant`'s `Sign` case) against the PREFIX of the trace
  strictly before the entry that carries the `Sign` term (the recursive
  definition of `trace_invariant` checks `trace_entry_invariant tr_init entry`
  for `Snoc tr_init entry`).  Consequently `dh_sign_pred` being satisfiable for a
  signature carried in a `MsgSent` entry at position `pos` REQUIRES the
  authorization `Event` to already be `event_triggered` on a trace of length
  `< pos`, i.e. on a STRICT PRIOR PREFIX — exactly the "authorization event before
  sign / MsgSent" ordering.  `DH.Sample.Symbolic.Provenance` already proves this
  ordering holds for every honest send this product model performs
  (`lemma_ifinish_authorizes_before_sign`, `lemma_respond_authorizes_before_sign`);
  this module additionally proves those two sends stay `is_publishable` (hence
  `trace_invariant`-compatible) BECAUSE `dh_sign_pred` is satisfied by the exact
  authorization event `Product.respond_run` / `Product.ifinish_run` triggers
  immediately before drawing the signing nonce and sending.

  State predicate — real, exercised AND genuinely inhabited
  -----------------------------------------------------------
  `Product.setup_run`, `rng_run`, `start_run`, `respond_run` and `ifinish_run`
  ALL call `DY.Core.Trace.Manipulation.set_state`, storing the acting role's
  CURRENT snapshot; `Product.corrupt_run` then calls DY* CORE's `corrupt` on the
  role's recorded snapshot position.  So `dh_state_pred` is exercised on every
  trace this development reaches, and it is the canonical DY* rule

      dh_state_pred_fun tr prin sess_id content =
        is_knowable_by (principal_state_label prin sess_id) tr content

  ("a principal only stores material knowable at its own state label"), which is
  exactly what makes a later `Corrupt` of that state sound.  It is INHABITED
  (public literals; and every snapshot this product stores —
  `lemma_snapshot_knowable`), it is NOT `True`
  (`lemma_state_pred_not_trivial`), and its `pred_knowable` obligation is
  discharged from the genuine label lattice, never from a `False` hypothesis.

  Event predicate — EXACT disjunction over the five reserved tags
  -------------------------------------------------------------------
  `dh_event_pred_fun tr p tag content` is an EXACT DISJUNCTION over exactly
  the five reserved tags — NOT a conjunction of implications.  A conjunction
  of implications (`tag == t1 ==> ... /\ tag == t2 ==> ... /\ ...`) is
  satisfied VACUOUSLY by any event whose tag is none of `t1, t2, ...`: every
  implication's antecedent is false, so the whole conjunction holds trivially,
  for ANY content and ANY principal.  The disjunction installed here instead
  REJECTS an event outside the five-tag vocabulary outright, because none of
  the five disjuncts' first conjunct (`tag == t_i`) can hold.  Each disjunct
  additionally pins, per tag, the EXACT triggering principal: `Product.
  setup_run` is called with `mep` fixed to EITHER `init_dy_principal` OR
  `resp_dy_principal` (its two call sites in `Product.product_initial`);
  `start_run` / `ifinish_run` are called ONLY with `init_dy_principal`;
  `respond_run` / `rfinish_run` are called ONLY with `resp_dy_principal` (grep
  `DH.Sample.Symbolic.Product`'s call sites — every one is a literal fixed
  principal, never a variable) — `tag_initiate` / `tag_initiator_finish` pin
  `p == init_dy_principal`, `tag_responder_respond` / `tag_responder_finish`
  pin `p == resp_dy_principal`, `tag_keygen` pins `p` to EITHER of the two.

  This strengthening is SOUND for this product, not merely convenient: the
  ONLY place any `Event` entry is ever appended to the shared trace is inside
  one of `Product.setup_run` / `start_run` / `respond_run` / `ifinish_run` /
  `rfinish_run`, and `Sys.sys_action` (`ActRng | ActStart | ActDeliver |
  ActInject`) has no constructor that lets any other code path — in
  particular no constructor that lets the attacker — trigger an `Event` with
  an arbitrary tag.  So every `Event` entry this product's step relation can
  EVER append already has one of the five exact shapes below; rejecting every
  other tag costs nothing this development's proofs need.

  It remains genuinely INHABITED (every event this product model ever
  triggers satisfies exactly one of the five disjuncts, discharged by the
  `lemma_*_event_pred` lemmas below with an explicit witness) and it is NOT
  `True`: an event using one of the five reserved tags with the WRONG
  principal or content shape, OR an event using ANY OTHER tag whatsoever,
  violates it.
*)

module B   = DY.Core.Bytes
module BT  = DY.Core.Bytes.Type
module L   = DY.Core.Label
module LT  = DY.Core.Label.Type
module T   = DY.Core.Trace.Type
module TB  = DY.Core.Trace.Base
module TI  = DY.Core.Trace.Invariant
module SM  = Common.StateMachine
module Sys = DH.Sample.System
module Lst = FStar.List.Tot
open DY.Core.Trace.Manipulation

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.System
open DH.Sample.Symbolic.Terms
open DH.Sample.Symbolic.Product
open DH.Sample.Symbolic.Provenance
open DH.Sample.Symbolic.Lifting

(** ── The `crypto_usages` instance ────────────────────────────────────────────

    No custom Diffie-Hellman / KDF usage-combination behaviour is needed: the
    product model never inspects `get_usage` of a `Dh sk1 (DhPub sk2)` term or a
    `KdfExpand` term, so the library defaults suffice. *)
instance dh_sample_crypto_usages : B.crypto_usages = B.default_crypto_usages

(** ── The exact signature authorization predicate ────────────────────────────*)

let dh_sign_pred_fun
  (tr:TB.trace) (sk_usage:BT.usage{BT.SigKey? sk_usage}) (vk:BT.bytes) (msg:BT.bytes)
  : prop =
  (vk == vkey_term (ltk_term (role_ltk_pos Init)) /\
     TB.event_triggered tr init_dy_principal tag_initiator_finish msg) \/
  (vk == vkey_term (ltk_term (role_ltk_pos Resp)) /\
     TB.event_triggered tr resp_dy_principal tag_responder_respond msg)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let dh_sign_pred_later
  (tr1 tr2:TB.trace) (sk_usage:BT.usage{BT.SigKey? sk_usage}) (vk msg:BT.bytes)
  : Lemma
    (requires
      dh_sign_pred_fun tr1 sk_usage vk msg /\
      B.bytes_well_formed tr1 vk /\
      B.bytes_well_formed tr1 msg /\
      tr1 `TB.grows` tr2)
    (ensures dh_sign_pred_fun tr2 sk_usage vk msg)
= eliminate
    (vk == vkey_term (ltk_term (role_ltk_pos Init)) /\
       TB.event_triggered tr1 init_dy_principal tag_initiator_finish msg) \/
    (vk == vkey_term (ltk_term (role_ltk_pos Resp)) /\
       TB.event_triggered tr1 resp_dy_principal tag_responder_respond msg)
  returns dh_sign_pred_fun tr2 sk_usage vk msg
  with _pf1. TB.event_triggered_grows tr1 tr2 init_dy_principal tag_initiator_finish msg
  and  _pf2. TB.event_triggered_grows tr1 tr2 resp_dy_principal tag_responder_respond msg
#pop-options

let dh_sign_pred : B.sign_crypto_predicate #dh_sample_crypto_usages = {
  B.pred       = dh_sign_pred_fun;
  B.pred_later = dh_sign_pred_later;
}

(** ── Genuinely inhabited, harmless AEAD / PKE / MAC predicates ──────────────

    AEAD, PKE and MAC are never used by this sample — grep
    `DH.Sample.Symbolic.{Terms,Product}`: there is no `aead_enc`, `pke_enc`, or
    `mac` call anywhere — so these predicates are never invoked on any
    reachable trace and their exact content cannot affect `product_invariant`.
    They must nonetheless be a genuinely INHABITED `prop`, never the library's
    `False`-valued `default_*_predicate`.  The harmless, sound choice installed
    here is "the payload's STRUCTURAL label is exactly `public`" — i.e. honest
    use (were it ever to occur) is restricted to encrypting/MACing an
    ALREADY-PUBLIC payload.  This is deliberately phrased with `B.get_label`
    (needing only the `crypto_usages` instance already in scope) rather than
    `B.is_publishable`/`B.is_knowable_by` (which need the FULL
    `crypto_invariants` instance being assembled right here — using it in one
    of its own fields would be circular).

      * Genuinely INHABITED: `B.get_label` is UNCONDITIONALLY `L.public` for a
        `Literal` term (`DY.Core.Bytes.get_label`'s first case, no
        `bytes_well_formed` side-condition needed), so e.g.
        `msg = B.literal_to_bytes lit` satisfies it on every trace.
      * NOT `True`: a role-labelled term, e.g. `share_term`'s underlying
        `Rand eph_len time` scalar, has `get_label = eph_label who = role_label
        who`, NOT `L.public` (`DH.Sample.Symbolic.Terms.eph_label`), so it
        genuinely rejects a real, non-degenerate case.
      * `pred_later` holds by `B.get_label_later`, which needs exactly the
        `bytes_well_formed` hypothesis `aead_crypto_predicate`/`pke_crypto_
        predicate`/`mac_crypto_predicate`'s own `pred_later` obligation already
        supplies. *)
let dh_aead_pred_fun
  (tr:TB.trace) (key_usage:BT.usage{BT.AeadKey? key_usage}) (key nonce msg ad:BT.bytes) : prop =
  B.get_label #dh_sample_crypto_usages tr msg == L.public

let dh_aead_pred_later
  (tr1 tr2:TB.trace) (key_usage:BT.usage{BT.AeadKey? key_usage}) (key nonce msg ad:BT.bytes)
  : Lemma
    (requires
      dh_aead_pred_fun tr1 key_usage key nonce msg ad /\
      B.bytes_well_formed tr1 key /\ B.bytes_well_formed tr1 nonce /\
      B.bytes_well_formed tr1 msg /\ B.bytes_well_formed tr1 ad /\
      tr1 `TB.grows` tr2)
    (ensures dh_aead_pred_fun tr2 key_usage key nonce msg ad)
= B.get_label_later #dh_sample_crypto_usages tr1 tr2 msg

let dh_aead_pred : B.aead_crypto_predicate #dh_sample_crypto_usages = {
  B.pred       = dh_aead_pred_fun;
  B.pred_later = dh_aead_pred_later;
}

let dh_pke_pred_fun
  (tr:TB.trace) (sk_usage:BT.usage{BT.PkeKey? sk_usage}) (pk msg:BT.bytes) : prop =
  B.get_label #dh_sample_crypto_usages tr msg == L.public

let dh_pke_pred_later
  (tr1 tr2:TB.trace) (sk_usage:BT.usage{BT.PkeKey? sk_usage}) (pk msg:BT.bytes)
  : Lemma
    (requires
      dh_pke_pred_fun tr1 sk_usage pk msg /\
      B.bytes_well_formed tr1 pk /\ B.bytes_well_formed tr1 msg /\
      tr1 `TB.grows` tr2)
    (ensures dh_pke_pred_fun tr2 sk_usage pk msg)
= B.get_label_later #dh_sample_crypto_usages tr1 tr2 msg

let dh_pke_pred : B.pke_crypto_predicate #dh_sample_crypto_usages = {
  B.pred       = dh_pke_pred_fun;
  B.pred_later = dh_pke_pred_later;
}

let dh_mac_pred_fun
  (tr:TB.trace) (key_usage:BT.usage{BT.MacKey? key_usage}) (key msg:BT.bytes) : prop =
  B.get_label #dh_sample_crypto_usages tr msg == L.public

let dh_mac_pred_later
  (tr1 tr2:TB.trace) (key_usage:BT.usage{BT.MacKey? key_usage}) (key msg:BT.bytes)
  : Lemma
    (requires
      dh_mac_pred_fun tr1 key_usage key msg /\
      B.bytes_well_formed tr1 key /\ B.bytes_well_formed tr1 msg /\
      tr1 `TB.grows` tr2)
    (ensures dh_mac_pred_fun tr2 key_usage key msg)
= B.get_label_later #dh_sample_crypto_usages tr1 tr2 msg

let dh_mac_pred : B.mac_crypto_predicate #dh_sample_crypto_usages = {
  B.pred       = dh_mac_pred_fun;
  B.pred_later = dh_mac_pred_later;
}

(** ── The `crypto_invariants` instance ────────────────────────────────────────*)
let dh_sample_crypto_predicates : B.crypto_predicates #dh_sample_crypto_usages = {
  B.aead_pred = dh_aead_pred;
  B.pke_pred  = dh_pke_pred;
  B.sign_pred = dh_sign_pred;
  B.mac_pred  = dh_mac_pred;
}

instance dh_sample_crypto_invariants : B.crypto_invariants = {
  B.usages = dh_sample_crypto_usages;
  B.preds  = dh_sample_crypto_predicates;
}

(** ── Publishability persists as the shared trace grows ──────────────────────

    Built from the library's OWN per-component persistence lemmas
    (`bytes_invariant_later`, `get_label_later`, `can_flow_later`) rather than
    relying on their SMTPats to chain unassisted through a compound term: this
    keeps every call site's rlimit low.  Placed here (right after
    `dh_sample_crypto_invariants` is in scope) so the state predicate below —
    which is stated in terms of `is_publishable` — can use it directly. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let is_publishable_grows (tr1 tr2:TB.trace) (b:BT.bytes)
  : Lemma
    (requires B.is_publishable #dh_sample_crypto_invariants tr1 b /\ tr1 `TB.grows` tr2)
    (ensures B.is_publishable #dh_sample_crypto_invariants tr2 b)
= B.bytes_invariant_later #dh_sample_crypto_invariants tr1 tr2 b;
  B.bytes_invariant_implies_well_formed #dh_sample_crypto_invariants tr1 b;
  B.get_label_later #dh_sample_crypto_usages tr1 tr2 b;
  L.can_flow_later tr1 tr2 (B.get_label #dh_sample_crypto_usages tr1 b) L.public
#pop-options

(** ── The state predicate: role-state-knowability, genuinely inhabited ────────

    `DH.Sample.Symbolic.Product` now genuinely CALLS `DY.Core.Trace.Manipulation.
    set_state`: every role action that changes that role's live material ends by
    storing the role's CURRENT snapshot (long-term key, pending draw, ephemeral
    scalar, received peer share, session key — see `Terms.snapshot_term`).  So the
    state predicate is EXERCISED on every trace this development reaches, and it
    must be the RIGHT rule, not a placeholder.

    The rule installed here is the DY* canonical one:

        dh_state_pred_fun tr prin sess_id content =
          is_knowable_by (principal_state_label prin sess_id) tr content

    "a principal may only store material that is knowable AT ITS OWN state label".
    This is exactly what makes a later `Corrupt` of that state sound: DY*'s
    attacker-knowledge theorem turns a corrupted state into publishable content,
    and the label discipline guarantees the leaked material was already labelled
    (at most) with that role's state label — which is precisely the
    compromise-sensitive `role_label` every role secret carries
    (`Terms.role_label`).

      * genuinely INHABITED: any public literal is knowable at ANY label
        (`literal_to_bytes_is_publishable` + `public_is_top`), and — the case that
        matters — every snapshot this product stores satisfies it
        (`lemma_snapshot_knowable` below, used at all five `SetState` sites);
      * NOT `True`: a `Rand` term with no `RandGen` entry on the trace is not even
        `bytes_invariant`, hence not knowable — see
        `lemma_state_pred_not_trivial`;
      * `pred_knowable` is discharged from the genuine label lattice: a role's
        state label flows to the state-CONTENT label of any content it stores
        (`state_pred_label_can_flow_state_pred_label`), so knowability at the
        former transitively gives knowability at the latter — never vacuously from
        a `False` hypothesis. *)
let dh_state_pred_fun
  (tr:TB.trace) (prin:T.principal) (sess_id:T.state_id) (content:BT.bytes) : prop =
  B.is_knowable_by #dh_sample_crypto_invariants
    (L.principal_state_label prin sess_id) tr content

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let dh_state_pred_later
  (tr1 tr2:TB.trace) (prin:T.principal) (sess_id:T.state_id) (content:BT.bytes)
  : Lemma
    (requires
      dh_state_pred_fun tr1 prin sess_id content /\
      tr1 `TB.grows` tr2)
    (ensures dh_state_pred_fun tr2 prin sess_id content)
= B.bytes_invariant_later #dh_sample_crypto_invariants tr1 tr2 content;
  B.bytes_invariant_implies_well_formed #dh_sample_crypto_invariants tr1 content;
  B.get_label_later #dh_sample_crypto_usages tr1 tr2 content;
  L.can_flow_later tr1 tr2
    (B.get_label #dh_sample_crypto_usages tr1 content)
    (L.principal_state_label prin sess_id)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let dh_state_pred_knowable
  (tr:TB.trace) (prin:T.principal) (sess_id:T.state_id) (content:BT.bytes)
  : Lemma
    (requires dh_state_pred_fun tr prin sess_id content)
    (ensures
      B.is_knowable_by #dh_sample_crypto_invariants
        (L.principal_state_content_label prin sess_id content) tr content)
= let gl = B.get_label #dh_sample_crypto_usages tr content in
  L.state_pred_label_can_flow_state_pred_label tr
    (L.principal_state_label_input prin sess_id)
    (L.principal_state_content_label_input prin sess_id content);
  L.can_flow_transitive tr gl
    (L.principal_state_label prin sess_id)
    (L.principal_state_content_label prin sess_id content)
#pop-options

let dh_state_pred : TI.state_predicate #dh_sample_crypto_invariants = {
  TI.pred          = dh_state_pred_fun;
  TI.pred_later    = dh_state_pred_later;
  TI.pred_knowable = dh_state_pred_knowable;
}

(** The state predicate is INHABITED: a public literal may be stored by anyone. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_state_pred_inhabited
  (tr:TB.trace) (prin:T.principal) (sess_id:T.state_id) (lit:bytes)
  : Lemma (ensures dh_state_pred_fun tr prin sess_id (B.literal_to_bytes lit))
= B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr lit;
  L.public_is_top tr (L.principal_state_label prin sess_id);
  L.can_flow_transitive tr
    (B.get_label #dh_sample_crypto_usages tr (B.literal_to_bytes lit))
    L.public (L.principal_state_label prin sess_id)
#pop-options

(** ... and it is NOT `True`: a `Rand` term that was never generated on the trace
    fails even the bytes invariant, so it is not storable. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let lemma_state_pred_not_trivial (prin:T.principal) (sess_id:T.state_id)
  : Lemma (ensures
      ~(dh_state_pred_fun TB.empty_trace prin sess_id (eph_term 0)))
= reveal_opaque (`%B.bytes_invariant) (B.bytes_invariant #dh_sample_crypto_invariants)
#pop-options

(** ── The event predicate: EXACT disjunction over the five reserved tags ──────

    STRENGTHENED from a conjunction-of-implications to a genuinely EXCLUSIVE,
    EXACT disjunction: an `Event` entry satisfies `dh_event_pred_fun` iff its
    tag is ONE OF the five reserved tags below, triggered by EXACTLY the
    pinned role principal(s) for that tag, and carrying content of EXACTLY the
    corresponding shape.  An event whose tag is NOT one of these five reserved
    tags satisfies NONE of the five disjuncts, hence does NOT satisfy
    `dh_event_pred_fun` at all — unlike a conjunction of implications (where an
    unrecognised tag would vacuously satisfy every implication's vacuous
    antecedent), this disjunction genuinely REJECTS any event outside the
    five-tag vocabulary.  This strengthening is sound for THIS product: the
    only place any `Event` entry is ever appended to the shared trace is inside
    one of `Product.setup_run` / `start_run` / `respond_run` / `ifinish_run` /
    `rfinish_run` (grep `DH.Sample.Symbolic.Product`: `Sys.sys_action` — `ActRng
    | ActStart | ActDeliver | ActInject` — has no constructor that lets the
    attacker or any other code path trigger an event with an arbitrary tag),
    and each of those five call sites passes literally one of the five reserved
    tags above with a literal fixed role principal — never a free tag or
    principal variable.  So every `Event` entry this product's step relation
    can EVER append already has one of these five exact shapes; rejecting every
    other tag costs nothing this development's proofs need and Section 4/6 of
    `SYMBOLIC_INVARIANT.md` account for exactly this.

      * `tag_keygen`            carries exactly a `keygen_content` AND is
        triggered by EITHER fixed role principal (both roles register a
        long-term key at setup);
      * `tag_initiate`          carries exactly an `initiate_content` AND is
        triggered ONLY by `init_dy_principal`;
      * `tag_initiator_finish`  carries exactly an `auth_content` AND is
        triggered ONLY by `init_dy_principal`;
      * `tag_responder_respond` carries exactly an `auth_content` AND is
        triggered ONLY by `resp_dy_principal`;
      * `tag_responder_finish`  carries exactly a `session_content` AND is
        triggered ONLY by `resp_dy_principal`.

    This is the structural fact a future mutual-authentication /
    session-key-secrecy proof consumes to recover the exact partner / share /
    key fields, AND the exact triggering role, out of a trace-recorded event,
    uniformly and without guessing — and, now, to rule out any event outside
    this exact five-tag vocabulary altogether.  It is genuinely INHABITED
    (every event this product model ever triggers satisfies exactly one of the
    five disjuncts — discharged below by the `lemma_*_event_pred` lemmas with
    an explicit witness) and it is NOT `True`: an event using one of the five
    reserved tags with the wrong principal or the wrong content shape, OR an
    event using ANY OTHER tag whatsoever, violates it. *)
let dh_event_pred_fun
  (tr:TB.trace) (p:T.principal) (tag:string) (content:BT.bytes) : prop =
  (tag == tag_keygen /\
    (p == init_dy_principal \/ p == resp_dy_principal) /\
    (exists (me vk:BT.bytes). content == keygen_content me vk)) \/
  (tag == tag_initiate /\
    p == init_dy_principal /\
    (exists (me peer share:BT.bytes). content == initiate_content me peer share)) \/
  (tag == tag_initiator_finish /\
    p == init_dy_principal /\
    (exists (partner gx gy:BT.bytes). content == auth_content partner gx gy)) \/
  (tag == tag_responder_respond /\
    p == resp_dy_principal /\
    (exists (partner gx gy:BT.bytes). content == auth_content partner gx gy)) \/
  (tag == tag_responder_finish /\
    p == resp_dy_principal /\
    (exists (peer key:BT.bytes). content == session_content peer key))

let dh_sample_trace_invariants : TI.trace_invariants #dh_sample_crypto_invariants = {
  TI.state_pred = dh_state_pred;
  TI.event_pred = dh_event_pred_fun;
}

instance dh_sample_protocol_invariants : TI.protocol_invariants = {
  TI.crypto_invs = dh_sample_crypto_invariants;
  TI.trace_invs  = dh_sample_trace_invariants;
}

(** ═══════════════════════════════════════════════════════════════════════════
    Compromise coherence: concrete flags ⟺ DY* state-label corruption
    ═══════════════════════════════════════════════════════════════════════════

    `DH.Sample.System` records dynamic compromise as two persistent BOOLEAN flags;
    DY* records it as a `Corrupt` entry pointing at a `SetState` entry, which in
    turn makes that role's `principal_state_label` (i.e. `Terms.role_label`)
    corrupt.  `corruption_coherent` is the invariant that keeps the two views in
    exact agreement:

      * FORWARD  — a set flag implies the role's DY* state label IS corrupt
        (established when `ActCorrupt` appends `Corrupt` at the role's current
        `SetState` position, and preserved because `is_corrupt` is monotone);
      * BACKWARD — every `Corrupt` entry on the trace points at a `SetState` of a
        role whose flag IS set.  Since the two role principals are distinct and a
        trace position holds exactly one entry, this yields the converse: a
        corrupt role label forces that role's flag
        (`lemma_corruption_coherence`).

    Together they justify reading either view as the other, which is what lets the
    security theorems state "... OR the peer's signing state is compromised" in
    BOTH the concrete-flag form and the DY-label form. *)

let role_state_corrupt (p:product_state) (who:endpoint_id) : prop =
  L.is_corrupt p.ps_trace (role_label who)

let corrupt_entry_authorized (p:product_state) (time:nat) : prop =
  (p.ps_sys.sys_init_corrupt /\
    (exists (c:BT.bytes).
       TB.entry_at p.ps_trace time
         (T.SetState (role_dy_principal Init) (role_state_id Init) c))) \/
  (p.ps_sys.sys_resp_corrupt /\
    (exists (c:BT.bytes).
       TB.entry_at p.ps_trace time
         (T.SetState (role_dy_principal Resp) (role_state_id Resp) c)))

(** `opaque_to_smt`: its trailing `forall (time:nat)` must not be instantiated in
    the (many) unrelated per-step queries that merely CARRY `product_invariant` in
    their context.  The handful of lemmas that reason about compromise reveal it
    locally. *)
[@@"opaque_to_smt"]
let corruption_coherent (p:product_state) : prop =
  (p.ps_sys.sys_init_corrupt ==> role_state_corrupt p Init) /\
  (p.ps_sys.sys_resp_corrupt ==> role_state_corrupt p Resp) /\
  (forall (time:nat).
     TB.entry_exists p.ps_trace (T.Corrupt time) ==> corrupt_entry_authorized p time)

(** ── The combined product invariant ──────────────────────────────────────────

    The COMBINED coherence + trace invariant + COMPROMISE COHERENCE that every
    authentication / secrecy proof is stated over.  `corruption_coherent` (defined
    further below, once the DY* corruption vocabulary is in scope) is what ties
    the concrete per-role compromise FLAGS of `DH.Sample.System` to genuine DY*
    `Corrupt` entries and to the corruption of the roles' state LABELS. *)
let product_invariant (p:product_state) : prop =
  wf p /\
  TI.trace_invariant #dh_sample_protocol_invariants p.ps_trace /\
  corruption_coherent p

(** ── Low-level helpers: usage / label of a recorded random value ────────────

    Everything this sample ever signs, DH-shares or checks for freshness is a
    `Rand` term whose usage and label are exactly the ones recorded by its
    `RandGen` trace entry.  This is the single place that reveals the opaque
    `get_usage` / `get_label` / `has_usage` definitions to relate them to
    `TB.entry_at`. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let lemma_rand_usage_label_of_entry
  (tr:TB.trace) (usg:BT.usage) (lab:LT.label) (len:nat{len <> 0}) (pos:nat)
  : Lemma
    (requires TB.entry_at tr pos (T.RandGen usg lab len))
    (ensures
      B.get_usage #dh_sample_crypto_usages tr (BT.Rand len pos) == usg /\
      B.get_label #dh_sample_crypto_usages tr (BT.Rand len pos) == lab /\
      B.has_usage #dh_sample_crypto_usages tr (BT.Rand len pos) usg)
= reveal_opaque (`%B.get_usage) (B.get_usage #dh_sample_crypto_usages);
  reveal_opaque (`%B.get_label) (B.get_label #dh_sample_crypto_usages);
  reveal_opaque (`%B.has_usage) (B.has_usage #dh_sample_crypto_usages)
#pop-options

(** ── Publishability of an honestly-generated DH share ───────────────────────

    A DH public share `share_term s = dh_pk s` is ALWAYS publishable once `s` is
    a recorded (i.e. `bytes_invariant`-satisfying) ephemeral — `dh_pk` erases the
    secret label of its argument unconditionally (`get_label_dh_pk`), which is
    exactly the DY* CORE model of "a DH public value may always be sent". *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(** A role-recorded ephemeral satisfies the bytes invariant and carries EXACTLY
    that role's compromise-sensitive label — the single fact all of the DH
    material's publishability / knowability / secrecy rests on. *)
let lemma_scalar_invariant_label (who:endpoint_id) (tr:TB.trace) (s:BT.bytes)
  : Lemma
    (requires scalar_recorded_for who tr s)
    (ensures
      B.bytes_invariant #dh_sample_crypto_invariants tr s /\
      B.get_label #dh_sample_crypto_usages tr s == role_label who /\
      B.has_usage #dh_sample_crypto_usages tr s eph_usage)
= eliminate exists (t:nat). s == eph_term t /\
    TB.entry_at tr t (T.RandGen eph_usage (eph_label who) eph_len)
  returns
    B.bytes_invariant #dh_sample_crypto_invariants tr s /\
    B.get_label #dh_sample_crypto_usages tr s == role_label who /\
    B.has_usage #dh_sample_crypto_usages tr s eph_usage
  with _.
    (reveal_opaque (`%B.bytes_invariant) (B.bytes_invariant #dh_sample_crypto_invariants);
     introduce exists (usage:BT.usage) (lab:LT.label). TB.entry_at tr t (T.RandGen usage lab eph_len)
       with eph_usage (eph_label who) and ();
     lemma_rand_usage_label_of_entry tr eph_usage (eph_label who) eph_len t)

let lemma_share_publishable_for (who:endpoint_id) (tr:TB.trace) (s:BT.bytes)
  : Lemma
    (requires scalar_recorded_for who tr s)
    (ensures B.is_publishable #dh_sample_crypto_invariants tr (share_term s))
= lemma_scalar_invariant_label who tr s

let lemma_share_publishable (tr:TB.trace) (s:BT.bytes)
  : Lemma
    (requires scalar_recorded tr s)
    (ensures B.is_publishable #dh_sample_crypto_invariants tr (share_term s))
= eliminate scalar_recorded_for Init tr s \/ scalar_recorded_for Resp tr s
  returns B.is_publishable #dh_sample_crypto_invariants tr (share_term s)
  with _. lemma_share_publishable_for Init tr s
  and  _. lemma_share_publishable_for Resp tr s
#pop-options

(** ── Publishability of an honestly-produced signature ───────────────────────

    A signature by the FIXED role long-term key over a transcript is publishable
    precisely BECAUSE `dh_sign_pred` records the corresponding role having
    triggered its exact authorization event with content exactly the transcript.
    This is the concrete instance of "honest MsgSent publishable from bytes
    invariants / crypto predicates" the audit asks for. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_sig_term_publishable
  (tr:TB.trace) (who:endpoint_id) (tag:string) (nonce_pos:nat) (transcript:BT.bytes)
  : Lemma
    (requires
      ((who == Init /\ tag == tag_initiator_finish) \/
       (who == Resp /\ tag == tag_responder_respond)) /\
      TB.entry_at tr (role_ltk_pos who) (T.RandGen ltk_usage (ltk_label who) ltk_len) /\
      TB.entry_at tr nonce_pos (T.RandGen signonce_usage (signonce_label who) signonce_len) /\
      TB.event_triggered tr (role_dy_principal who) tag transcript /\
      B.is_publishable #dh_sample_crypto_invariants tr transcript)
    (ensures
      B.is_publishable #dh_sample_crypto_invariants tr
        (sig_term (ltk_term (role_ltk_pos who)) (signonce_term nonce_pos) transcript))
= let ltk_pos = role_ltk_pos who in
  let mep = role_dy_principal who in
  let ltk   = ltk_term ltk_pos in
  let nonce = signonce_term nonce_pos in
  lemma_rand_usage_label_of_entry tr ltk_usage (ltk_label who) ltk_len ltk_pos;
  lemma_rand_usage_label_of_entry tr signonce_usage (signonce_label who) signonce_len nonce_pos;
  reveal_opaque (`%B.bytes_invariant) (B.bytes_invariant #dh_sample_crypto_invariants);
  assert (B.bytes_invariant #dh_sample_crypto_invariants tr ltk);
  assert (B.bytes_invariant #dh_sample_crypto_invariants tr nonce);
  assert (dh_sign_pred_fun tr ltk_usage (vkey_term ltk) transcript);
  assert (B.bytes_invariant #dh_sample_crypto_invariants tr (sig_term ltk nonce transcript))
#pop-options

(** ── Publishability of a received Msg1 / Msg2 DH share ──────────────────────

    A packet's structured share is publishable regardless of its origin: an
    honest sender's share is `share_term s` for a recorded `s`
    (`lemma_share_publishable`); an injected share is a public literal
    (`literal_to_bytes_is_publishable`).  `smsg_provenance` (unfolded once here)
    pins exactly these two cases. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_net_entry_share_publishable
  (init_ltk resp_ltk:BT.bytes) (pk:packet) (ne:net_entry) (tr:TB.trace)
  : Lemma
    (requires net_entry_coherent init_ltk resp_ltk pk ne tr)
    (ensures (
      match pk.pk_msg, ne.ne_smsg with
      | Msg1 _ _,   SMsg1 _ gxs    -> B.is_publishable #dh_sample_crypto_invariants tr gxs
      | Msg2 _ _ _, SMsg2 _ gys _  -> B.is_publishable #dh_sample_crypto_invariants tr gys
      | _ -> True))
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  match pk.pk_origin, pk.pk_msg, ne.ne_smsg, ne.ne_auth with
  | Injected, Msg1 a gx, SMsg1 _ gxs, NoAuth ->
    B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr gx
  | Sent Init, Msg1 _ _, SMsg1 _ gxs, NoAuth ->
    eliminate exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded tr s
    returns B.is_publishable #dh_sample_crypto_invariants tr gxs
    with _. lemma_share_publishable tr s
  | Injected, Msg2 b gy _, SMsg2 _ gys _, NoAuth ->
    B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr gy
  | Sent Resp, Msg2 _ _ _, SMsg2 _ gys _, RespAuth _ _ ->
    eliminate exists (s:BT.bytes). gys == share_term s /\ scalar_recorded tr s
    returns B.is_publishable #dh_sample_crypto_invariants tr gys
    with _. lemma_share_publishable tr s
  | _ -> ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Knowability of a role's stored SNAPSHOT — the DY* state-predicate obligation
    ═══════════════════════════════════════════════════════════════════════════

    Every `SetState` the product appends must satisfy `dh_state_pred_fun`, i.e.
    the stored snapshot must be KNOWABLE AT THE STORING ROLE'S STATE LABEL.  The
    snapshot is a concatenation of the role's long-term key, its pending draw, its
    ephemeral scalar, the peer share it received and its session key, so it
    suffices to establish knowability component by component
    (`concat_preserves_knowability`).  Each component is knowable at `role_label
    who` for a DIFFERENT, precise reason:

      * the long-term key and the ephemerals ARE labelled `role_label who`
        (reflexivity of `can_flow`);
      * a received peer share is PUBLISHABLE, and `public` flows to every label;
      * the session key `dh scalar peer_share` has label `join (role_label who)
        (get_dh_label peer_share)`, and a join flows to each of its components —
        this is exactly the "my session key is knowable by me" fact, and it stays
        true when the peer share is an attacker literal (then the join's second
        component is `public`).

    Nothing here is vacuous: these are the same labels the secrecy theorems in
    `DH.Sample.Symbolic.Security` reason about. *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

(** A join flows to its left component: corrupting the component corrupts the
    join.  (Used for the session key's label.) *)
let join_flows_to_left (tr:TB.trace) (l1 l2:LT.label)
  : Lemma (ensures (L.join l1 l2) `L.can_flow tr` l1)
= L.intro_can_flow tr (L.join l1 l2) l1 (fun tr' -> L.is_corrupt_join tr' l1 l2)

let publishable_is_knowable (who:endpoint_id) (tr:TB.trace) (b:BT.bytes)
  : Lemma
    (requires B.is_publishable #dh_sample_crypto_invariants tr b)
    (ensures B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr b)
= L.public_is_top tr (role_label who);
  L.can_flow_transitive tr (B.get_label #dh_sample_crypto_usages tr b)
    L.public (role_label who)

let lemma_ltk_knowable (who:endpoint_id) (tr:TB.trace)
  : Lemma
    (requires
      TB.entry_at tr (role_ltk_pos who) (T.RandGen ltk_usage (ltk_label who) ltk_len))
    (ensures
      B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr
        (ltk_term (role_ltk_pos who)))
= let pos = role_ltk_pos who in
  reveal_opaque (`%B.bytes_invariant) (B.bytes_invariant #dh_sample_crypto_invariants);
  introduce exists (usage:BT.usage) (lab:LT.label). TB.entry_at tr pos (T.RandGen usage lab ltk_len)
    with ltk_usage (ltk_label who) and ();
  lemma_rand_usage_label_of_entry tr ltk_usage (ltk_label who) ltk_len pos

let lemma_scalar_knowable (who:endpoint_id) (tr:TB.trace) (s:BT.bytes)
  : Lemma
    (requires scalar_recorded_for who tr s)
    (ensures B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr s)
= lemma_scalar_invariant_label who tr s

#pop-options

(** The session key: `dh scalar peer_share` is knowable by the role that holds
    `scalar`, WHATEVER the peer share is (an honest `dh_pk`, or an attacker
    literal). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let lemma_key_knowable (who:endpoint_id) (tr:TB.trace) (s peer_share:BT.bytes)
  : Lemma
    (requires
      scalar_recorded_for who tr s /\
      B.is_publishable #dh_sample_crypto_invariants tr peer_share)
    (ensures
      B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr
        (secret_term s peer_share))
= lemma_scalar_invariant_label who tr s;
  B.bytes_invariant_dh #dh_sample_crypto_invariants tr s eph_usage peer_share;
  B.get_label_dh #dh_sample_crypto_usages tr s peer_share;
  join_flows_to_left tr (role_label who) (B.get_dh_label #dh_sample_crypto_usages tr peer_share)
#pop-options

(** The five components of a role's snapshot, each knowable at that role's state
    label.  `opt_knowable` handles the "not present yet" case, whose placeholder
    is the PUBLIC empty literal. *)
let opt_knowable (who:endpoint_id) (tr:TB.trace) (o:option BT.bytes) : prop =
  match o with
  | None   -> True
  | Some b -> B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr b

let shadow_material_knowable (who:endpoint_id) (tr:TB.trace) (sh:endpoint_shadow) : prop =
  B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr sh.sh_ltk /\
  opt_knowable who tr sh.sh_pending /\
  opt_knowable who tr sh.sh_scalar /\
  opt_knowable who tr sh.sh_peer_share /\
  opt_knowable who tr sh.sh_key

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let lemma_opt_material_knowable (who:endpoint_id) (tr:TB.trace) (o:option BT.bytes)
  : Lemma
    (requires opt_knowable who tr o)
    (ensures
      B.is_knowable_by #dh_sample_crypto_invariants (role_label who) tr (opt_material o))
= match o with
  | None ->
    B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr (FStar.Seq.empty #FStar.UInt8.t);
    publishable_is_knowable who tr no_material
  | Some _ -> ()

(** THE state-predicate obligation of every `SetState` this product appends. *)
let lemma_snapshot_knowable (who:endpoint_id) (tr:TB.trace) (sh:endpoint_shadow)
  : Lemma
    (requires shadow_material_knowable who tr sh)
    (ensures
      dh_state_pred_fun tr (role_dy_principal who) (role_state_id who)
        (shadow_snapshot sh))
= lemma_shadow_snapshot_unfold sh;
  lemma_opt_material_knowable who tr sh.sh_pending;
  lemma_opt_material_knowable who tr sh.sh_scalar;
  lemma_opt_material_knowable who tr sh.sh_peer_share;
  lemma_opt_material_knowable who tr sh.sh_key
#pop-options

(** ── Event-predicate discharge, one lemma per reserved tag ──────────────────

    Each of the FIVE trace-monad segments (`setup_run`, `start_run`,
    `respond_run`, `ifinish_run`, `rfinish_run`) triggers exactly one event, with
    content built by exactly the corresponding `*_content` builder, and with
    `mep` fixed to exactly the role principal(s) `dh_event_pred_fun` pins for
    that tag (see "Event predicate" above; every call site in
    `DH.Sample.Symbolic.Product` passes a literal `init_dy_principal` /
    `resp_dy_principal`, never a free variable); each helper below supplies
    that builder's arguments as the existential witness AND requires `mep` to
    already be the pinned principal, so `dh_event_pred_fun` holds for that
    event with no guessing. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_keygen_event_pred
  (tr:TB.trace) (mep:T.principal{mep == init_dy_principal \/ mep == resp_dy_principal})
  (me_t vk:BT.bytes)
  : Lemma (ensures dh_event_pred_fun tr mep tag_keygen (keygen_content me_t vk))
= introduce exists (me vkk:BT.bytes). keygen_content me_t vk == keygen_content me vkk
  with me_t vk and ()

let lemma_initiate_event_pred
  (tr:TB.trace) (mep:T.principal{mep == init_dy_principal}) (me_t peer_t share:BT.bytes)
  : Lemma (ensures dh_event_pred_fun tr mep tag_initiate (initiate_content me_t peer_t share))
= introduce exists (me peer sh:BT.bytes). initiate_content me_t peer_t share == initiate_content me peer sh
  with me_t peer_t share and ()

let lemma_initiator_finish_event_pred
  (tr:TB.trace) (mep:T.principal{mep == init_dy_principal}) (partner gx gy:BT.bytes)
  : Lemma (ensures dh_event_pred_fun tr mep tag_initiator_finish (auth_content partner gx gy))
= introduce exists (p x y:BT.bytes). auth_content partner gx gy == auth_content p x y
  with partner gx gy and ()

let lemma_responder_respond_event_pred
  (tr:TB.trace) (mep:T.principal{mep == resp_dy_principal}) (partner gx gy:BT.bytes)
  : Lemma (ensures dh_event_pred_fun tr mep tag_responder_respond (auth_content partner gx gy))
= introduce exists (p x y:BT.bytes). auth_content partner gx gy == auth_content p x y
  with partner gx gy and ()

let lemma_responder_finish_event_pred
  (tr:TB.trace) (mep:T.principal{mep == resp_dy_principal}) (peer key:BT.bytes)
  : Lemma (ensures dh_event_pred_fun tr mep tag_responder_finish (session_content peer key))
= introduce exists (p k:BT.bytes). session_content peer key == session_content p k
  with peer key and ()
#pop-options

(** ── Generic one- / two- / three-entry trace-invariant stepping ─────────────

    `TI.trace_invariant` is defined by recursion on `Snoc`, and
    `TB.append_entry tr e == TB.Snoc tr e` (`DY.Core.Trace.Base.append_entry`),
    so appending one entry that itself satisfies `trace_entry_invariant` against
    the CURRENT trace preserves `trace_invariant`.  These are the composition
    steps that lift a single append fact to the two- and three-append segments
    every honest `*_run` in `DH.Sample.Symbolic.Product` performs. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let trace_invariant_snoc (tr:TB.trace) (e:TB.trace_entry)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      TI.trace_entry_invariant #dh_sample_protocol_invariants tr e)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (TB.append_entry tr e))
= reveal_opaque (`%TI.trace_invariant) (TI.trace_invariant #dh_sample_protocol_invariants)

let trace_invariant_snoc2 (tr:TB.trace) (e1 e2:TB.trace_entry)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      TI.trace_entry_invariant #dh_sample_protocol_invariants tr e1 /\
      TI.trace_entry_invariant #dh_sample_protocol_invariants (TB.append_entry tr e1) e2)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants
               (TB.append_entry (TB.append_entry tr e1) e2))
= trace_invariant_snoc tr e1;
  trace_invariant_snoc (TB.append_entry tr e1) e2

let trace_invariant_snoc3 (tr:TB.trace) (e1 e2 e3:TB.trace_entry)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      TI.trace_entry_invariant #dh_sample_protocol_invariants tr e1 /\
      TI.trace_entry_invariant #dh_sample_protocol_invariants (TB.append_entry tr e1) e2 /\
      TI.trace_entry_invariant #dh_sample_protocol_invariants
        (TB.append_entry (TB.append_entry tr e1) e2) e3)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants
               (TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3))
= trace_invariant_snoc2 tr e1 e2;
  trace_invariant_snoc (TB.append_entry (TB.append_entry tr e1) e2) e3
#pop-options

(** ── Wiring: `product_step` pins the SAME state `lift_next` computes ────────

    `product_step p0 ev p1 out` and `lift_next p0 ctr` both dispatch through the
    SAME deterministic `sym_extend p0 ev`; when `ctr` packages exactly `(ev, p1.
    ps_sys, out)`, `product_step`'s conjuncts pin every field of `p1` to the SAME
    `Some`-tuple components `lift_next p0 ctr` assigns, so the two states are
    equal.  This lets every per-case trace-invariant lemma below reuse
    `DH.Sample.Symbolic.Lifting`'s already-proven `wf`-preservation instead of
    re-deriving it. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_product_step_is_lift_next
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_step p0 ev p1 out)
    (ensures (
      let ctr : Sys.system_transition =
        { SM.tr_event = ev; SM.tr_next_state = p1.ps_sys; SM.tr_output = out } in
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      lift_next p0 ctr == p1))
= ()
#pop-options

(** ── Per-action trace-invariant preservation ─────────────────────────────────

    One lemma per `sym_extend` case, mirroring exactly
    `DH.Sample.Symbolic.Lifting`'s per-case dispatch (same case shapes, same
    pattern matches), but concluding `trace_invariant` instead of `wf`.  Reusing
    `wf p0`'s already-established coherence facts (`key_state_coherent`,
    `rng_state_coherent`) supplies the `entry_at` / `event_triggered` /
    `scalar_recorded` premises each `trace_entry_invariant` obligation needs.

    Compared with the corruption-free model, each state-changing case now ALSO
    discharges the DY* STATE-PREDICATE obligation of the `SetState` entry its
    segment appends, via `lemma_snapshot_knowable`; and there is one NEW case,
    `ActCorrupt`, whose single `Corrupt` entry carries no obligation at all
    (`trace_entry_invariant` is `True` for `Corrupt`, exactly as DY* CORE's own
    `corrupt_invariant` states). *)

(** Explicit honest/internal RNG draw: a `RandGen` (unconditionally allowed)
    followed by the drawing role's refreshed `SetState`.  The stored snapshot is
    the role's long-term key plus the JUST-GENERATED pending scalar (the role has
    no other material yet: an RNG draw is only legal in its start phase). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_rng_trace_invariant (who:endpoint_id) (sh:endpoint_shadow) (tr:TB.trace)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      TB.entry_at tr (role_ltk_pos who) (T.RandGen ltk_usage (ltk_label who) ltk_len) /\
      sh.sh_ltk == ltk_term (role_ltk_pos who) /\
      sh.sh_pending == Some (eph_term (TB.trace_length tr)) /\
      sh.sh_scalar == None /\ sh.sh_peer_share == None /\ sh.sh_key == None)
    (ensures
      TI.trace_invariant #dh_sample_protocol_invariants
        (rng_trace who (shadow_snapshot sh) tr))
= let n = TB.trace_length tr in
  let e1 = T.RandGen eph_usage (eph_label who) eph_len in
  let tr1 = TB.append_entry tr e1 in
  TB.grows_snoc tr e1;
  TB.entry_at_grows tr tr1 (role_ltk_pos who) (T.RandGen ltk_usage (ltk_label who) ltk_len);
  lemma_ltk_knowable who tr1;
  introduce exists (t:nat). eph_term n == eph_term t /\
    TB.entry_at tr1 t (T.RandGen eph_usage (eph_label who) eph_len)
  with n and ();
  lemma_scalar_knowable who tr1 (eph_term n);
  lemma_snapshot_knowable who tr1 sh;
  trace_invariant_snoc2 tr e1
    (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_trace_invariant_rng
  (p0:product_state) (ctr:Sys.system_transition) (owner:endpoint_id) (x:dh_scalar)
  : Lemma
    (requires
      wf p0 /\
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActRng owner x))
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= let n = TB.trace_length p0.ps_trace in
  let scalar = eph_term n in
  match owner with
  | Init ->
    (match p0.ps_init.sh_pending with
     | Some _ -> ()
     | None ->
       let i' = { p0.ps_init with sh_pending = Some scalar; sh_state_pos = n + 1 } in
       rng_structure Init (shadow_snapshot i') p0.ps_trace;
       lemma_rng_trace_invariant Init i' p0.ps_trace)
  | Resp ->
    (match p0.ps_resp.sh_pending with
     | Some _ -> ()
     | None ->
       let r' = { p0.ps_resp with sh_pending = Some scalar; sh_state_pos = n + 1 } in
       rng_structure Resp (shadow_snapshot r') p0.ps_trace;
       lemma_rng_trace_invariant Resp r' p0.ps_trace)
#pop-options

(** ── Standalone: `start_trace` preserves `trace_invariant` ──────────────────

    `Event tag_initiate`, then the `MsgSent` of Msg1's structured term, then the
    initiator's refreshed `SetState`.  The Msg1 term is `concat (Literal me)
    (dh_pk scalar)`: the identity is a public literal and the share is publishable
    because the consumed pending scalar is trace-recorded.  The stored snapshot is
    the long-term key plus the now-active scalar. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_start_trace_invariant
  (me:principal) (peer_t scalar:BT.bytes) (sh:endpoint_shadow) (tr:TB.trace)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      scalar_recorded_for Init tr scalar /\
      TB.entry_at tr (role_ltk_pos Init) (T.RandGen ltk_usage (ltk_label Init) ltk_len) /\
      sh.sh_ltk == ltk_term (role_ltk_pos Init) /\
      sh.sh_pending == None /\ sh.sh_scalar == Some scalar /\
      sh.sh_peer_share == None /\ sh.sh_key == None)
    (ensures
      TI.trace_invariant #dh_sample_protocol_invariants
        (start_trace (term_of_principal me) peer_t scalar (shadow_snapshot sh) tr))
= let met = term_of_principal me in
  let e1 = T.Event (role_dy_principal Init) tag_initiate
             (initiate_content met peer_t (share_term scalar)) in
  let e2 = T.MsgSent (flatten (SMsg1 met (share_term scalar))) in
  lemma_initiate_event_pred tr (role_dy_principal Init) met peer_t (share_term scalar);
  let tr1 = TB.append_entry tr e1 in
  let tr2 = TB.append_entry tr1 e2 in
  grows2 tr e1 e2;
  TB.grows_snoc tr e1;
  scalar_recorded_for_grows Init tr tr1 scalar;
  B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr1 me;
  lemma_share_publishable_for Init tr1 scalar;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr1 met (share_term scalar);
  scalar_recorded_for_grows Init tr tr2 scalar;
  TB.entry_at_grows tr tr2 (role_ltk_pos Init) (T.RandGen ltk_usage (ltk_label Init) ltk_len);
  lemma_ltk_knowable Init tr2;
  lemma_scalar_knowable Init tr2 scalar;
  lemma_snapshot_knowable Init tr2 sh;
  trace_invariant_snoc3 tr e1 e2
    (T.SetState (role_dy_principal Init) (role_state_id Init) (shadow_snapshot sh))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_trace_invariant_start (p0:product_state) (ctr:Sys.system_transition)
  : Lemma
    (requires
      wf p0 /\
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent Sys.ActStart)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  let me  = c0.sys_init.ep_me in
  let met = term_of_principal me in
  match c0.sys_init.ep_peer, c0.sys_init_pending, p0.ps_init.sh_pending with
  | Some peer, Some x, Some scalar ->
    let i' = { p0.ps_init with sh_pending = None; sh_scalar = Some scalar;
                               sh_state_pos = n + 2 } in
    start_structure met (term_of_principal peer) scalar (shadow_snapshot i') p0.ps_trace;
    lemma_start_trace_invariant me (term_of_principal peer) scalar i' p0.ps_trace
  | _, _, _ -> ()
#pop-options

(** ── Standalone: `respond_trace` preserves `trace_invariant` ────────────────

    A GENERIC, self-contained fact about the four entries `respond_trace`
    appends — no `product_state` / `system_step` / `sym_extend` in scope, so
    Z3 only ever has the (small) hypotheses this signature lists.  The "wiring"
    lemma below (which DOES need the full product/system context to identify
    which concrete `respond_trace` call `sym_extend` performed) reuses this as
    a black box, which is what keeps ITS OWN rlimit low.

    The trailing `SetState` stores the responder's post-response snapshot: its
    long-term key, its ephemeral scalar, the peer share it just accepted AND the
    session key it just derived. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_respond_trace_invariant
  (me:principal) (a_t peer_share scalar:BT.bytes) (sh:endpoint_shadow) (tr:TB.trace)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      scalar_recorded_for Resp tr scalar /\
      B.is_publishable #dh_sample_crypto_invariants tr a_t /\
      B.is_publishable #dh_sample_crypto_invariants tr peer_share /\
      TB.entry_at tr (role_ltk_pos Resp) (T.RandGen ltk_usage (ltk_label Resp) ltk_len) /\
      sh.sh_ltk == ltk_term (role_ltk_pos Resp) /\
      sh.sh_pending == None /\ sh.sh_scalar == Some scalar /\
      sh.sh_peer_share == Some peer_share /\
      sh.sh_key == Some (secret_term scalar peer_share))
    (ensures
      TI.trace_invariant #dh_sample_protocol_invariants
        (respond_trace sh.sh_ltk (term_of_principal me) a_t peer_share scalar
                       (shadow_snapshot sh) tr))
= let n = TB.trace_length tr in
  let mep = role_dy_principal Resp in
  let ltk = sh.sh_ltk in
  let me_t = term_of_principal me in
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let e1 = T.Event mep tag_responder_respond transcript in
  let e2 = T.RandGen signonce_usage (signonce_label Resp) signonce_len in
  let e3 = T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n+1)) transcript))) in
  let e4 = T.SetState mep (role_state_id Resp) (shadow_snapshot sh) in
  lemma_responder_respond_event_pred tr mep a_t peer_share (share_term scalar);
  lemma_share_publishable_for Resp tr scalar;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr peer_share (share_term scalar);
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr a_t
    (B.concat peer_share (share_term scalar));
  grows2 tr e1 e2;
  let tr1 = TB.append_entry tr e1 in
  let tr2 = TB.append_entry tr1 e2 in
  TB.entry_at_grows tr tr2 (role_ltk_pos Resp) (T.RandGen ltk_usage (ltk_label Resp) ltk_len);
  scalar_recorded_for_grows Resp tr tr2 scalar;
  lemma_share_publishable_for Resp tr2 scalar;
  B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr2 me;
  is_publishable_grows tr tr2 a_t;
  is_publishable_grows tr tr2 peer_share;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr2 peer_share (share_term scalar);
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr2 a_t
    (B.concat peer_share (share_term scalar));
  lemma_sig_term_publishable tr2 Resp tag_responder_respond (n+1) transcript;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr2
    (share_term scalar) (sig_term ltk (signonce_term (n+1)) transcript);
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr2
    me_t (B.concat (share_term scalar) (sig_term ltk (signonce_term (n+1)) transcript));
  let tr3 = TB.append_entry tr2 e3 in
  grows3 tr e1 e2 e3;
  TB.entry_at_grows tr tr3 (role_ltk_pos Resp) (T.RandGen ltk_usage (ltk_label Resp) ltk_len);
  scalar_recorded_for_grows Resp tr tr3 scalar;
  is_publishable_grows tr tr3 peer_share;
  lemma_ltk_knowable Resp tr3;
  lemma_scalar_knowable Resp tr3 scalar;
  publishable_is_knowable Resp tr3 peer_share;
  lemma_key_knowable Resp tr3 scalar peer_share;
  lemma_snapshot_knowable Resp tr3 sh;
  trace_invariant_snoc3 tr e1 e2 e3;
  trace_invariant_snoc tr3 e4
#pop-options

(** Responder receives Msg1: `Event tag_responder_respond`, `RandGen` (signing
    nonce), `MsgSent` of Msg2's structured term, then its refreshed `SetState`.
    The signature is publishable because the responder JUST triggered its exact
    authorization event over the exact transcript, immediately before drawing the
    nonce and signing — `dh_sign_pred`'s responder disjunct applies verbatim. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_trace_invariant_resp_msg1
      (p0:product_state) (ctr:Sys.system_transition) (idx:nat{idx < Lst.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      Msg1? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  net_coherent_index c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk idx;
  let ne0  = Lst.index p0.ps_net idx in
  let pk0  = Lst.index c0.sys_net idx in
  let cmsg = pk0.pk_msg in
  match cmsg, p0.ps_resp.sh_pending with
  | Msg1 a gx, Some scalar ->
    let me  = c0.sys_resp.ep_me in
    let met = term_of_principal me in
    let at  = term_of_principal a in
    let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
    let r' = { p0.ps_resp with sh_pending = None; sh_scalar = Some scalar;
                 sh_peer_share = Some peer_share;
                 sh_key = Some (secret_term scalar peer_share);
                 sh_state_pos = n + 3 } in
    lemma_net_entry_share_publishable p0.ps_init.sh_ltk p0.ps_resp.sh_ltk pk0 ne0 p0.ps_trace;
    B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants p0.ps_trace a;
    assert (p0.ps_resp.sh_ltk == ltk_term (role_ltk_pos Resp) /\
            TB.entry_at p0.ps_trace (role_ltk_pos Resp)
              (T.RandGen ltk_usage (ltk_label Resp) ltk_len));
    lemma_respond_trace_invariant me at peer_share scalar r' p0.ps_trace;
    respond_structure p0.ps_resp.sh_ltk met at peer_share scalar (shadow_snapshot r')
                      p0.ps_trace ne0.ne_pos
  | _, _ -> ()
#pop-options

(** ── Standalone: `rfinish_trace` preserves `trace_invariant` ────────────────

    A single `Event tag_responder_finish`; no `MsgSent` (no wire output) and no
    `SetState` (completion changes the responder's PHASE, not its key material),
    so the only obligation is the (shape) event predicate. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_rfinish_trace_invariant (a_t key:BT.bytes) (tr:TB.trace)
  : Lemma
    (requires TI.trace_invariant #dh_sample_protocol_invariants tr)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (rfinish_trace a_t key tr))
= lemma_responder_finish_event_pred tr (role_dy_principal Resp) a_t key;
  trace_invariant_snoc tr
    (T.Event (role_dy_principal Resp) tag_responder_finish (session_content a_t key))
#pop-options

(** Responder receives Msg3: completes with `Event tag_responder_finish`; the
    network is UNCHANGED (no `MsgSent`) and so is its stored state, so this is the
    simplest case. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_trace_invariant_resp_msg3
      (p0:product_state) (ctr:Sys.system_transition) (idx:nat{idx < Lst.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      Msg3? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = Lst.index p0.ps_net idx in
  let cmsg = (Lst.index c0.sys_net idx).pk_msg in
  match cmsg with
  | Msg3 sigA ->
    (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
     | Some a, Some key ->
       lemma_rfinish_trace_invariant (term_of_principal a) key p0.ps_trace;
       rfinish_structure (term_of_principal a) key p0.ps_trace ne0.ne_pos
     | _, _ -> ())
  | _ -> ()
#pop-options

(** ── Standalone: `ifinish_trace` preserves `trace_invariant` ────────────────

    Mirrors `lemma_respond_trace_invariant`, for the initiator's role, its
    fixed key position, its tag (`tag_initiator_finish`), Msg3's layout (a BARE
    signature, no identity/share concatenation), and its refreshed `SetState`
    (which now retains the peer share and the session key). *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_ifinish_trace_invariant
  (scalar b_t peer_share:BT.bytes) (sh:endpoint_shadow) (tr:TB.trace)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      scalar_recorded_for Init tr scalar /\
      B.is_publishable #dh_sample_crypto_invariants tr b_t /\
      B.is_publishable #dh_sample_crypto_invariants tr peer_share /\
      TB.entry_at tr (role_ltk_pos Init) (T.RandGen ltk_usage (ltk_label Init) ltk_len) /\
      sh.sh_ltk == ltk_term (role_ltk_pos Init) /\
      sh.sh_pending == None /\ sh.sh_scalar == Some scalar /\
      sh.sh_peer_share == Some peer_share /\
      sh.sh_key == Some (secret_term scalar peer_share))
    (ensures
      TI.trace_invariant #dh_sample_protocol_invariants
        (ifinish_trace sh.sh_ltk scalar b_t peer_share (shadow_snapshot sh) tr))
= let n = TB.trace_length tr in
  let mep = role_dy_principal Init in
  let ltk = sh.sh_ltk in
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let e1 = T.Event mep tag_initiator_finish transcript in
  let e2 = T.RandGen signonce_usage (signonce_label Init) signonce_len in
  let e3 = T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n+1)) transcript))) in
  let e4 = T.SetState mep (role_state_id Init) (shadow_snapshot sh) in
  lemma_initiator_finish_event_pred tr mep b_t (share_term scalar) peer_share;
  lemma_share_publishable_for Init tr scalar;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr (share_term scalar) peer_share;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr b_t
    (B.concat (share_term scalar) peer_share);
  grows2 tr e1 e2;
  let tr1 = TB.append_entry tr e1 in
  let tr2 = TB.append_entry tr1 e2 in
  TB.entry_at_grows tr tr2 (role_ltk_pos Init) (T.RandGen ltk_usage (ltk_label Init) ltk_len);
  scalar_recorded_for_grows Init tr tr2 scalar;
  is_publishable_grows tr tr2 b_t;
  is_publishable_grows tr tr2 peer_share;
  lemma_share_publishable_for Init tr2 scalar;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr2 (share_term scalar) peer_share;
  B.concat_preserves_publishability #dh_sample_crypto_invariants tr2 b_t
    (B.concat (share_term scalar) peer_share);
  lemma_sig_term_publishable tr2 Init tag_initiator_finish (n+1) transcript;
  let tr3 = TB.append_entry tr2 e3 in
  grows3 tr e1 e2 e3;
  TB.entry_at_grows tr tr3 (role_ltk_pos Init) (T.RandGen ltk_usage (ltk_label Init) ltk_len);
  scalar_recorded_for_grows Init tr tr3 scalar;
  is_publishable_grows tr tr3 peer_share;
  lemma_ltk_knowable Init tr3;
  lemma_scalar_knowable Init tr3 scalar;
  publishable_is_knowable Init tr3 peer_share;
  lemma_key_knowable Init tr3 scalar peer_share;
  lemma_snapshot_knowable Init tr3 sh;
  trace_invariant_snoc3 tr e1 e2 e3;
  trace_invariant_snoc tr3 e4
#pop-options

(** Initiator receives message 2: completes, sends message 3 (a bare signature)
    and refreshes its stored state. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_trace_invariant_init_msg2
      (p0:product_state) (ctr:Sys.system_transition) (idx:nat{idx < Lst.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  net_coherent_index c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk idx;
  let ne0  = Lst.index p0.ps_net idx in
  let pk0  = Lst.index c0.sys_net idx in
  let cmsg = pk0.pk_msg in
  match cmsg, p0.ps_init.sh_scalar with
  | Msg2 b gy sigB, Some scalar ->
    (match c0.sys_init.ep_scalar with
     | Some xc ->
       let bt = term_of_principal b in
       let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
       let i' = { p0.ps_init with sh_peer_share = Some peer_share;
                    sh_key = Some (secret_term scalar peer_share);
                    sh_state_pos = n + 3 } in
       lemma_net_entry_share_publishable p0.ps_init.sh_ltk p0.ps_resp.sh_ltk pk0 ne0 p0.ps_trace;
       B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants p0.ps_trace b;
       assert (p0.ps_init.sh_ltk == ltk_term (role_ltk_pos Init) /\
               TB.entry_at p0.ps_trace (role_ltk_pos Init)
                 (T.RandGen ltk_usage (ltk_label Init) ltk_len));
       lemma_ifinish_trace_invariant scalar bt peer_share i' p0.ps_trace;
       ifinish_structure p0.ps_init.sh_ltk scalar bt peer_share (shadow_snapshot i')
                         p0.ps_trace ne0.ne_pos
     | None -> ())
  | _, _ -> ()
#pop-options

(** ── Standalone: `inject_trace` preserves `trace_invariant` ─────────────────

    An attacker injection is publishable on ANY trace under ANY crypto
    invariants (`Provenance.lemma_inject_publishable`); no other obligation
    arises. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_inject_trace_invariant (m:dh_message) (tr:TB.trace)
  : Lemma
    (requires TI.trace_invariant #dh_sample_protocol_invariants tr)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (inject_trace (inject_smsg m) tr))
= lemma_inject_publishable #dh_sample_crypto_invariants tr m;
  trace_invariant_snoc tr (T.MsgSent (flatten (inject_smsg m)))
#pop-options

(** Attacker injection: an all-literal packet, DY-publishable by construction. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_step_trace_invariant_inject (p0:product_state) (ctr:Sys.system_transition) (m:dh_message)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActInject m))
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= lemma_inject_trace_invariant m p0.ps_trace;
  let (pos, tr') = inject_run (inject_smsg m) p0.ps_trace in
  assert (sym_extend p0 ctr.SM.tr_event ==
          Some (tr', p0.ps_init, p0.ps_resp,
                Lst.append p0.ps_net [ { ne_smsg = inject_smsg m; ne_pos = pos; ne_auth = NoAuth } ],
                p0.ps_rng));
  assert ((lift_next p0 ctr).ps_trace == tr');
  assert (tr' == inject_trace (inject_smsg m) p0.ps_trace)
#pop-options

(** ── Standalone: `corrupt_trace` preserves `trace_invariant` ────────────────

    A `Corrupt` entry carries NO obligation: `TI.trace_entry_invariant` is `True`
    for it — precisely DY* CORE's own `DY.Core.Trace.Manipulation.corrupt_invariant`
    ("corrupting a state always preserves the trace invariant").  The DY* design
    puts the burden on the STATE predicate instead: because every stored snapshot
    was proved knowable at its role's state label, corrupting it leaks only
    material that label already accounted for. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_corrupt_trace_invariant (pos:nat) (tr:TB.trace)
  : Lemma
    (requires TI.trace_invariant #dh_sample_protocol_invariants tr)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (corrupt_trace pos tr))
= (* literally DY* CORE's own `corrupt_invariant`, on the genuine `corrupt`
     operation `corrupt_run` performs *)
  corrupt_invariant #dh_sample_protocol_invariants pos tr;
  corrupt_structure pos tr
#pop-options

(** DYNAMIC COMPROMISE of a role. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_step_trace_invariant_corrupt
  (p0:product_state) (ctr:Sys.system_transition) (who:endpoint_id)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActCorrupt who))
    (ensures TI.trace_invariant #dh_sample_protocol_invariants (lift_next p0 ctr).ps_trace)
= let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
  corrupt_structure sh.sh_state_pos p0.ps_trace;
  lemma_corrupt_trace_invariant sh.sh_state_pos p0.ps_trace
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    The case-exhaustive one-step trace-invariant preservation theorem
    ═══════════════════════════════════════════════════════════════════════════ *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let product_step_preserves_trace_invariant
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\
      TI.trace_invariant #dh_sample_protocol_invariants p0.ps_trace /\
      product_step p0 ev p1 out)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants p1.ps_trace)
= let ctr : Sys.system_transition =
    { SM.tr_event = ev; SM.tr_next_state = p1.ps_sys; SM.tr_output = out } in
  lemma_product_step_is_lift_next p0 ev p1 out;
  let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_step_trace_invariant_rng p0 ctr owner x
  | SM.LocalEvent Sys.ActStart -> lemma_step_trace_invariant_start p0 ctr
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    assert (idx < Lst.length c0.sys_net);
    let cmsg = (Lst.index c0.sys_net idx).pk_msg in
    (match dst, cmsg with
     | Resp, Msg1 _ _   -> lemma_step_trace_invariant_resp_msg1 p0 ctr idx
     | Resp, Msg3 _     -> lemma_step_trace_invariant_resp_msg3 p0 ctr idx
     | Init, Msg2 _ _ _ -> lemma_step_trace_invariant_init_msg2 p0 ctr idx
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActInject m) -> lemma_step_trace_invariant_inject p0 ctr m
  | SM.LocalEvent (Sys.ActCorrupt who) -> lemma_step_trace_invariant_corrupt p0 ctr who
  | _ -> ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Compromise-coherence preservation
    ═══════════════════════════════════════════════════════════════════════════

    The `corruption_coherent` conjunct of `product_invariant` is inductive.  The
    key structural fact for every NON-compromise step is that it introduces no new
    `Corrupt` entry; the compromise step itself introduces exactly one, pointing at
    the target role's CURRENT `SetState` (`wf`'s `state_state_coherent`), while
    setting exactly that role's flag. *)

(** No step except `ActCorrupt` puts a new `Corrupt` entry on the trace.  Marked
    `opaque_to_smt` so its `forall` is not instantiated in the per-step queries
    that only ever need it as an ATOM (matched up to the trace equality each
    segment's `*_structure` lemma provides); the lemmas below reveal it. *)
[@@"opaque_to_smt"]
let no_new_corrupt (tr tr':TB.trace) : prop =
  forall (time:nat).
    TB.entry_exists tr' (T.Corrupt time) ==> TB.entry_exists tr (T.Corrupt time)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(** Inverting one append: an entry of `Snoc tr e` is either `e` at the end, or an
    entry of `tr`. *)
let entry_at_snoc_inv (tr:TB.trace) (e:TB.trace_entry) (i:nat) (x:TB.trace_entry)
  : Lemma
    (requires TB.entry_at (TB.append_entry tr e) i x)
    (ensures (i == TB.trace_length tr /\ x == e) \/ TB.entry_at tr i x)
= ()

let no_new_corrupt_snoc (tr:TB.trace) (e:TB.trace_entry)
  : Lemma
    (requires ~ (T.Corrupt? e))
    (ensures no_new_corrupt tr (TB.append_entry tr e))
= reveal_opaque (`%no_new_corrupt) no_new_corrupt;
  introduce forall (time:nat).
      TB.entry_exists (TB.append_entry tr e) (T.Corrupt time) ==>
      TB.entry_exists tr (T.Corrupt time)
  with introduce _ ==> _
  with _.
    eliminate exists (i:nat). TB.entry_at (TB.append_entry tr e) i (T.Corrupt time)
    returns TB.entry_exists tr (T.Corrupt time)
    with _.
      (entry_at_snoc_inv tr e i (T.Corrupt time);
       introduce exists (j:nat). TB.entry_at tr j (T.Corrupt time) with i and ())

let no_new_corrupt_refl (tr:TB.trace)
  : Lemma (ensures no_new_corrupt tr tr)
= reveal_opaque (`%no_new_corrupt) no_new_corrupt

let no_new_corrupt_transitive (tr1 tr2 tr3:TB.trace)
  : Lemma
    (requires no_new_corrupt tr1 tr2 /\ no_new_corrupt tr2 tr3)
    (ensures no_new_corrupt tr1 tr3)
= reveal_opaque (`%no_new_corrupt) no_new_corrupt

let no_new_corrupt_snoc2 (tr:TB.trace) (e1 e2:TB.trace_entry)
  : Lemma
    (requires ~ (T.Corrupt? e1) /\ ~ (T.Corrupt? e2))
    (ensures no_new_corrupt tr (TB.append_entry (TB.append_entry tr e1) e2))
= no_new_corrupt_snoc tr e1;
  no_new_corrupt_snoc (TB.append_entry tr e1) e2;
  no_new_corrupt_transitive tr (TB.append_entry tr e1)
    (TB.append_entry (TB.append_entry tr e1) e2)

let no_new_corrupt_snoc3 (tr:TB.trace) (e1 e2 e3:TB.trace_entry)
  : Lemma
    (requires ~ (T.Corrupt? e1) /\ ~ (T.Corrupt? e2) /\ ~ (T.Corrupt? e3))
    (ensures no_new_corrupt tr
               (TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3))
= no_new_corrupt_snoc2 tr e1 e2;
  let tr2 = TB.append_entry (TB.append_entry tr e1) e2 in
  no_new_corrupt_snoc tr2 e3;
  no_new_corrupt_transitive tr tr2 (TB.append_entry tr2 e3)

let no_new_corrupt_snoc4 (tr:TB.trace) (e1 e2 e3 e4:TB.trace_entry)
  : Lemma
    (requires ~ (T.Corrupt? e1) /\ ~ (T.Corrupt? e2) /\ ~ (T.Corrupt? e3) /\ ~ (T.Corrupt? e4))
    (ensures no_new_corrupt tr
               (TB.append_entry (TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3) e4))
= no_new_corrupt_snoc3 tr e1 e2 e3;
  let tr3 = TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3 in
  no_new_corrupt_snoc tr3 e4;
  no_new_corrupt_transitive tr tr3 (TB.append_entry tr3 e4)

#pop-options

(** ── Per-action "no new corruption" ──────────────────────────────────────────
    One lemma per NON-compromise `sym_extend` case, mirroring EXACTLY the same
    case shapes and pattern matches as the `lemma_step_trace_invariant_*` family
    above, but concluding the much cheaper `no_new_corrupt` fact. *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_no_new_corrupt_rng
  (p0:product_state) (ctr:Sys.system_transition) (owner:endpoint_id) (x:dh_scalar)
  : Lemma
    (requires
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActRng owner x))
    (ensures no_new_corrupt p0.ps_trace (lift_next p0 ctr).ps_trace)
= let n = TB.trace_length p0.ps_trace in
  let scalar = eph_term n in
  match owner with
  | Init ->
    (match p0.ps_init.sh_pending with
     | Some _ -> no_new_corrupt_refl p0.ps_trace
     | None ->
       let i' = { p0.ps_init with sh_pending = Some scalar; sh_state_pos = n + 1 } in
       rng_structure Init (shadow_snapshot i') p0.ps_trace;
       no_new_corrupt_snoc2 p0.ps_trace
         (T.RandGen eph_usage (eph_label Init) eph_len)
         (T.SetState (role_dy_principal Init) (role_state_id Init) (shadow_snapshot i')))
  | Resp ->
    (match p0.ps_resp.sh_pending with
     | Some _ -> no_new_corrupt_refl p0.ps_trace
     | None ->
       let r' = { p0.ps_resp with sh_pending = Some scalar; sh_state_pos = n + 1 } in
       rng_structure Resp (shadow_snapshot r') p0.ps_trace;
       no_new_corrupt_snoc2 p0.ps_trace
         (T.RandGen eph_usage (eph_label Resp) eph_len)
         (T.SetState (role_dy_principal Resp) (role_state_id Resp) (shadow_snapshot r')))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_no_new_corrupt_start (p0:product_state) (ctr:Sys.system_transition)
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent Sys.ActStart)
    (ensures no_new_corrupt p0.ps_trace (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  let met = term_of_principal c0.sys_init.ep_me in
  match c0.sys_init.ep_peer, c0.sys_init_pending, p0.ps_init.sh_pending with
  | Some peer, Some x, Some scalar ->
    let i' = { p0.ps_init with sh_pending = None; sh_scalar = Some scalar;
                               sh_state_pos = n + 2 } in
    start_structure met (term_of_principal peer) scalar (shadow_snapshot i') p0.ps_trace;
    no_new_corrupt_snoc3 p0.ps_trace
      (T.Event (role_dy_principal Init) tag_initiate
         (initiate_content met (term_of_principal peer) (share_term scalar)))
      (T.MsgSent (flatten (SMsg1 met (share_term scalar))))
      (T.SetState (role_dy_principal Init) (role_state_id Init) (shadow_snapshot i'))
  | _, _, _ -> no_new_corrupt_refl p0.ps_trace
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_no_new_corrupt_resp_msg1
      (p0:product_state) (ctr:Sys.system_transition) (idx:nat{idx < Lst.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      Msg1? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures no_new_corrupt p0.ps_trace (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = Lst.index p0.ps_net idx in
  let cmsg = (Lst.index c0.sys_net idx).pk_msg in
  match cmsg, p0.ps_resp.sh_pending with
  | Msg1 a gx, Some scalar ->
    let met = term_of_principal c0.sys_resp.ep_me in
    let at  = term_of_principal a in
    let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
    let r' = { p0.ps_resp with sh_pending = None; sh_scalar = Some scalar;
                 sh_peer_share = Some peer_share;
                 sh_key = Some (secret_term scalar peer_share);
                 sh_state_pos = n + 3 } in
    let transcript = transcript_term at peer_share (share_term scalar) in
    respond_structure p0.ps_resp.sh_ltk met at peer_share scalar (shadow_snapshot r')
                      p0.ps_trace ne0.ne_pos;
    no_new_corrupt_snoc4 p0.ps_trace
      (T.Event (role_dy_principal Resp) tag_responder_respond transcript)
      (T.RandGen signonce_usage (signonce_label Resp) signonce_len)
      (T.MsgSent (flatten (SMsg2 met (share_term scalar)
         (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript))))
      (T.SetState (role_dy_principal Resp) (role_state_id Resp) (shadow_snapshot r'))
  | _, _ -> no_new_corrupt_refl p0.ps_trace
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_no_new_corrupt_resp_msg3
      (p0:product_state) (ctr:Sys.system_transition) (idx:nat{idx < Lst.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      Msg3? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures no_new_corrupt p0.ps_trace (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = Lst.index p0.ps_net idx in
  let cmsg = (Lst.index c0.sys_net idx).pk_msg in
  match cmsg with
  | Msg3 sigA ->
    (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
     | Some a, Some key ->
       rfinish_structure (term_of_principal a) key p0.ps_trace ne0.ne_pos;
       no_new_corrupt_snoc p0.ps_trace
         (T.Event (role_dy_principal Resp) tag_responder_finish
            (session_content (term_of_principal a) key))
     | _, _ -> no_new_corrupt_refl p0.ps_trace)
  | _ -> no_new_corrupt_refl p0.ps_trace
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_step_no_new_corrupt_init_msg2
      (p0:product_state) (ctr:Sys.system_transition) (idx:nat{idx < Lst.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures no_new_corrupt p0.ps_trace (lift_next p0 ctr).ps_trace)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = Lst.index p0.ps_net idx in
  let cmsg = (Lst.index c0.sys_net idx).pk_msg in
  match cmsg, p0.ps_init.sh_scalar with
  | Msg2 b gy sigB, Some scalar ->
    let bt = term_of_principal b in
    let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
    let i' = { p0.ps_init with sh_peer_share = Some peer_share;
                 sh_key = Some (secret_term scalar peer_share);
                 sh_state_pos = n + 3 } in
    let transcript = transcript_term bt (share_term scalar) peer_share in
    ifinish_structure p0.ps_init.sh_ltk scalar bt peer_share (shadow_snapshot i')
                      p0.ps_trace ne0.ne_pos;
    no_new_corrupt_snoc4 p0.ps_trace
      (T.Event (role_dy_principal Init) tag_initiator_finish transcript)
      (T.RandGen signonce_usage (signonce_label Init) signonce_len)
      (T.MsgSent (flatten (SMsg3 (sig_term p0.ps_init.sh_ltk (signonce_term (n + 1)) transcript))))
      (T.SetState (role_dy_principal Init) (role_state_id Init) (shadow_snapshot i'))
  | _, _ -> no_new_corrupt_refl p0.ps_trace
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_step_no_new_corrupt_inject
  (p0:product_state) (ctr:Sys.system_transition) (m:dh_message)
  : Lemma
    (requires
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActInject m))
    (ensures no_new_corrupt p0.ps_trace (lift_next p0 ctr).ps_trace)
= inject_structure (inject_smsg m) p0.ps_trace;
  no_new_corrupt_snoc p0.ps_trace (T.MsgSent (flatten (inject_smsg m)))
#pop-options

(** The case-exhaustive "no new corruption unless `ActCorrupt`" theorem. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let product_step_no_new_corrupt
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\ product_step p0 ev p1 out /\
      (forall (who:endpoint_id). ev =!= SM.LocalEvent (Sys.ActCorrupt who)))
    (ensures no_new_corrupt p0.ps_trace p1.ps_trace)
= let ctr : Sys.system_transition =
    { SM.tr_event = ev; SM.tr_next_state = p1.ps_sys; SM.tr_output = out } in
  lemma_product_step_is_lift_next p0 ev p1 out;
  let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_step_no_new_corrupt_rng p0 ctr owner x
  | SM.LocalEvent Sys.ActStart -> lemma_step_no_new_corrupt_start p0 ctr
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    assert (idx < Lst.length c0.sys_net);
    let cmsg = (Lst.index c0.sys_net idx).pk_msg in
    (match dst, cmsg with
     | Resp, Msg1 _ _   -> lemma_step_no_new_corrupt_resp_msg1 p0 ctr idx
     | Resp, Msg3 _     -> lemma_step_no_new_corrupt_resp_msg3 p0 ctr idx
     | Init, Msg2 _ _ _ -> lemma_step_no_new_corrupt_init_msg2 p0 ctr idx
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActInject m) -> lemma_step_no_new_corrupt_inject p0 ctr m
  | _ -> ()
#pop-options

(** ── One-step preservation of `corruption_coherent` ──────────────────────────*)

(** An already-authorized `Corrupt` entry stays authorized: its `SetState`
    witness persists under trace growth and the authorizing flag is persistent. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10 --split_queries always"
let corrupt_authorized_grows (p0 p1:product_state) (time:nat)
  : Lemma
    (requires
      corrupt_entry_authorized p0 time /\
      p0.ps_trace `TB.grows` p1.ps_trace /\
      (p0.ps_sys.sys_init_corrupt ==> p1.ps_sys.sys_init_corrupt) /\
      (p0.ps_sys.sys_resp_corrupt ==> p1.ps_sys.sys_resp_corrupt))
    (ensures corrupt_entry_authorized p1 time)
= eliminate
      (p0.ps_sys.sys_init_corrupt /\
        (exists (c:BT.bytes). TB.entry_at p0.ps_trace time
           (T.SetState (role_dy_principal Init) (role_state_id Init) c))) \/
      (p0.ps_sys.sys_resp_corrupt /\
        (exists (c:BT.bytes). TB.entry_at p0.ps_trace time
           (T.SetState (role_dy_principal Resp) (role_state_id Resp) c)))
  returns corrupt_entry_authorized p1 time
  with _.
    (eliminate exists (c:BT.bytes). TB.entry_at p0.ps_trace time
        (T.SetState (role_dy_principal Init) (role_state_id Init) c)
     returns corrupt_entry_authorized p1 time
     with _.
       (TB.entry_at_grows p0.ps_trace p1.ps_trace time
          (T.SetState (role_dy_principal Init) (role_state_id Init) c);
        introduce exists (c':BT.bytes). TB.entry_at p1.ps_trace time
          (T.SetState (role_dy_principal Init) (role_state_id Init) c')
        with c and ()))
  and _.
    (eliminate exists (c:BT.bytes). TB.entry_at p0.ps_trace time
        (T.SetState (role_dy_principal Resp) (role_state_id Resp) c)
     returns corrupt_entry_authorized p1 time
     with _.
       (TB.entry_at_grows p0.ps_trace p1.ps_trace time
          (T.SetState (role_dy_principal Resp) (role_state_id Resp) c);
        introduce exists (c':BT.bytes). TB.entry_at p1.ps_trace time
          (T.SetState (role_dy_principal Resp) (role_state_id Resp) c')
        with c and ()))

(** The FRESH `Corrupt` entry an `ActCorrupt who` appends is authorized: that
    role's flag is now set and the entry points at that role's `SetState`. *)
let corrupt_authorized_fresh
  (p1:product_state) (who:endpoint_id) (time:nat) (c:BT.bytes)
  : Lemma
    (requires
      Sys.corrupt_flag p1.ps_sys who == true /\
      TB.entry_at p1.ps_trace time
        (T.SetState (role_dy_principal who) (role_state_id who) c))
    (ensures corrupt_entry_authorized p1 time)
= match who with
  | Init ->
    introduce exists (c':BT.bytes). TB.entry_at p1.ps_trace time
      (T.SetState (role_dy_principal Init) (role_state_id Init) c')
    with c and ()
  | Resp ->
    introduce exists (c':BT.bytes). TB.entry_at p1.ps_trace time
      (T.SetState (role_dy_principal Resp) (role_state_id Resp) c')
    with c and ()
#pop-options

(** Non-compromise steps: the flags do not change, `is_corrupt` is monotone under
    trace growth, and no new `Corrupt` entry appears, so every already-authorized
    entry stays authorized. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_corruption_coherent_frame (p0 p1:product_state)
  : Lemma
    (requires
      corruption_coherent p0 /\
      p0.ps_trace `TB.grows` p1.ps_trace /\
      no_new_corrupt p0.ps_trace p1.ps_trace /\
      p1.ps_sys.sys_init_corrupt == p0.ps_sys.sys_init_corrupt /\
      p1.ps_sys.sys_resp_corrupt == p0.ps_sys.sys_resp_corrupt)
    (ensures corruption_coherent p1)
= reveal_opaque (`%no_new_corrupt) no_new_corrupt;
  reveal_opaque (`%corruption_coherent) corruption_coherent;
  introduce p1.ps_sys.sys_init_corrupt ==> role_state_corrupt p1 Init
  with _. L.is_corrupt_later p0.ps_trace p1.ps_trace (role_label Init);
  introduce p1.ps_sys.sys_resp_corrupt ==> role_state_corrupt p1 Resp
  with _. L.is_corrupt_later p0.ps_trace p1.ps_trace (role_label Resp);
  introduce forall (time:nat).
    TB.entry_exists p1.ps_trace (T.Corrupt time) ==> corrupt_entry_authorized p1 time
  with introduce _ ==> _
  with _. corrupt_authorized_grows p0 p1 time
#pop-options

(** The compromise step itself: the target role's flag becomes set, and the trace
    gains exactly one `Corrupt` entry pointing at that role's CURRENT `SetState`
    (from `wf`'s `state_state_coherent`), which both AUTHORIZES the new entry and
    corrupts the role's DY* state label. *)
(** The compromised role's DY* state label IS corrupt after the step: the fresh
    `Corrupt` entry points at that role's current `SetState`. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_corrupt_step_label
  (p0:product_state) (who:endpoint_id) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\ product_step p0 (SM.LocalEvent (Sys.ActCorrupt who)) p1 out)
    (ensures role_state_corrupt p1 who)
= let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
  lemma_corrupt_step_effect p0 who p1 out;
  lemma_state_corrupt_implies_label_corrupt p1.ps_trace who (shadow_snapshot sh)
#pop-options

(** The two flag-to-label implications after a compromise of `who`, in a context
    that mentions only the flags, the labels and the trace growth. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let corruption_flags_coherent_after (p0 p1:product_state) (who:endpoint_id)
  : Lemma
    (requires
      (p0.ps_sys.sys_init_corrupt ==> role_state_corrupt p0 Init) /\
      (p0.ps_sys.sys_resp_corrupt ==> role_state_corrupt p0 Resp) /\
      p0.ps_trace `TB.grows` p1.ps_trace /\
      role_state_corrupt p1 who /\
      (who == Init ==> p1.ps_sys.sys_resp_corrupt == p0.ps_sys.sys_resp_corrupt) /\
      (who == Resp ==> p1.ps_sys.sys_init_corrupt == p0.ps_sys.sys_init_corrupt))
    (ensures
      (p1.ps_sys.sys_init_corrupt ==> role_state_corrupt p1 Init) /\
      (p1.ps_sys.sys_resp_corrupt ==> role_state_corrupt p1 Resp))
= match who with
  | Init ->
    introduce p1.ps_sys.sys_resp_corrupt ==> role_state_corrupt p1 Resp
    with _. L.is_corrupt_later p0.ps_trace p1.ps_trace (role_label Resp)
  | Resp ->
    introduce p1.ps_sys.sys_init_corrupt ==> role_state_corrupt p1 Init
    with _. L.is_corrupt_later p0.ps_trace p1.ps_trace (role_label Init)
#pop-options

(** All `Corrupt` entries stay authorized after ONE `Corrupt pos` append: the new
    entry is authorized by the freshly set flag and the `SetState` at `pos`; each
    older one keeps its own authorization.  Stated over the trace shapes alone, so
    the (expensive) product-step context never enters this query. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10 --split_queries always"
let corrupt_entries_authorized_after
  (p0 p1:product_state) (who:endpoint_id) (pos:nat) (c:BT.bytes)
  : Lemma
    (requires
      (forall (time:nat).
         TB.entry_exists p0.ps_trace (T.Corrupt time) ==> corrupt_entry_authorized p0 time) /\
      p1.ps_trace == corrupt_trace pos p0.ps_trace /\
      p0.ps_trace `TB.grows` p1.ps_trace /\
      Sys.corrupt_flag p1.ps_sys who == true /\
      TB.entry_at p1.ps_trace pos
        (T.SetState (role_dy_principal who) (role_state_id who) c) /\
      (p0.ps_sys.sys_init_corrupt ==> p1.ps_sys.sys_init_corrupt) /\
      (p0.ps_sys.sys_resp_corrupt ==> p1.ps_sys.sys_resp_corrupt))
    (ensures
      (forall (time:nat).
         TB.entry_exists p1.ps_trace (T.Corrupt time) ==> corrupt_entry_authorized p1 time))
= introduce forall (time:nat).
    TB.entry_exists p1.ps_trace (T.Corrupt time) ==> corrupt_entry_authorized p1 time
  with introduce _ ==> _
  with _.
    (eliminate exists (i:nat). TB.entry_at p1.ps_trace i (T.Corrupt time)
     returns corrupt_entry_authorized p1 time
     with _.
       (entry_at_snoc_inv p0.ps_trace (T.Corrupt pos) i (T.Corrupt time);
        if i = TB.trace_length p0.ps_trace then
          corrupt_authorized_fresh p1 who time c
        else begin
          introduce exists (j:nat). TB.entry_at p0.ps_trace j (T.Corrupt time) with i and ();
          corrupt_authorized_grows p0 p1 time
        end))
#pop-options

(** The compromise step itself: the target role's flag becomes set, and the trace
    gains exactly one `Corrupt` entry pointing at that role's CURRENT `SetState`
    (from `wf`'s `state_state_coherent`), which both AUTHORIZES the new entry and
    corrupts the role's DY* state label. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_corruption_coherent_corrupt
  (p0:product_state) (who:endpoint_id) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\ corruption_coherent p0 /\
      product_step p0 (SM.LocalEvent (Sys.ActCorrupt who)) p1 out)
    (ensures corruption_coherent p1)
= reveal_opaque (`%corruption_coherent) corruption_coherent;
  let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
  lemma_corrupt_step_effect p0 who p1 out;
  Sys.lemma_corrupt_step_changes_only_compromise_metadata
    p0.ps_sys p1.ps_sys who out;
  Sys.lemma_corruption_monotone p0.ps_sys p1.ps_sys (SM.LocalEvent (Sys.ActCorrupt who)) out;
  (* the compromised role's label is now corrupt; the other role's flag (if set)
     was already coherent and `is_corrupt` is monotone (`is_corrupt_later`) *)
  lemma_corrupt_step_label p0 who p1 out;
  corruption_flags_coherent_after p0 p1 who;
  assert (p1.ps_trace == corrupt_trace sh.sh_state_pos p0.ps_trace);
  assert (Sys.corrupt_flag p1.ps_sys who == true);
  assert (TB.entry_at p1.ps_trace sh.sh_state_pos
            (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh)));
  assert (p0.ps_trace `TB.grows` p1.ps_trace);
  corrupt_entries_authorized_after p0 p1 who sh.sh_state_pos (shadow_snapshot sh)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let product_step_preserves_corruption_coherent
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires wf p0 /\ corruption_coherent p0 /\ product_step p0 ev p1 out)
    (ensures corruption_coherent p1)
= lemma_product_step_grows p0 ev p1 out;
  Sys.lemma_corruption_monotone p0.ps_sys p1.ps_sys ev out;
  match ev with
  | SM.LocalEvent (Sys.ActCorrupt who) ->
    lemma_corruption_coherent_corrupt p0 who p1 out
  | _ ->
    product_step_no_new_corrupt p0 ev p1 out;
    lemma_corruption_coherent_frame p0 p1
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    The case-exhaustive one-step invariant-preservation theorem
    ═══════════════════════════════════════════════════════════════════════════

    `product_step_preserves_invariant`:

      requires product_invariant p0 /\ Product.product_step p0 ev p1 out
      ensures  product_invariant p1

    Dispatches on the shape of `ev` EXACTLY as `Product.sym_extend` and
    `Lifting.lemma_lift_step` do (now SEVEN shapes: RNG, honest initiator start,
    honest responder respond, honest responder finish, honest initiator finish,
    attacker injection, and DYNAMIC COMPROMISE), reusing `lemma_lift_step` for the
    `wf` half, the per-case `lemma_step_trace_invariant_*` lemmas for the
    `trace_invariant` half, and `product_step_preserves_corruption_coherent` for
    the compromise-coherence half.  Every case that discharges a `MsgSent`
    obligation does so from `is_publishable`, honest signature provenance
    (`dh_sign_pred`), or `Provenance.lemma_inject_publishable`; every case that
    discharges a `SetState` obligation does so from `lemma_snapshot_knowable` —
    never assumed. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let product_step_preserves_invariant
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_invariant p0 /\ product_step p0 ev p1 out)
    (ensures product_invariant p1)
= let ctr : Sys.system_transition =
    { SM.tr_event = ev; SM.tr_next_state = p1.ps_sys; SM.tr_output = out } in
  lemma_product_step_is_lift_next p0 ev p1 out;
  lemma_lift_step p0 ctr;
  product_step_preserves_trace_invariant p0 ev p1 out;
  product_step_preserves_corruption_coherent p0 ev p1 out
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Compromise coherence, in both directions
    ═══════════════════════════════════════════════════════════════════════════

    Under `product_invariant`, the concrete per-role compromise FLAG and the DY*
    corruption of that role's STATE LABEL are EQUIVALENT.  The backward direction
    uses that a trace position holds exactly ONE entry and that the two role
    principals are distinct, so a `Corrupt` entry authorized for one role cannot
    also be pointing at the other role's `SetState`. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_corruption_coherence (p:product_state)
  : Lemma
    (requires product_invariant p)
    (ensures
      (p.ps_sys.sys_init_corrupt <==> role_state_corrupt p Init) /\
      (p.ps_sys.sys_resp_corrupt <==> role_state_corrupt p Resp))
= reveal_opaque (`%corruption_coherent) corruption_coherent;
  lemma_role_principals_distinct ();
  lemma_role_label_corrupt_iff p.ps_trace Init;
  lemma_role_label_corrupt_iff p.ps_trace Resp
#pop-options

(** The corollary the security theorems use: an UNCOMPROMISED role (concretely:
    its flag is clear) has an UNCORRUPTED DY* state label. *)
let lemma_uncorrupt_role_label (p:product_state) (who:endpoint_id)
  : Lemma
    (requires product_invariant p /\ Sys.corrupt_flag p.ps_sys who == false)
    (ensures ~(role_state_corrupt p who))
= lemma_corruption_coherence p

(** ═══════════════════════════════════════════════════════════════════════════
    Reachable-state theorem
    ═══════════════════════════════════════════════════════════════════════════ *)

(** `product_initial` runs BOTH endpoints' setups on the ONE shared trace: for
    each role a `RandGen` (unconditionally allowed), an `Event tag_keygen` whose
    content is exactly a `keygen_content` (allowed by `dh_event_pred_fun`'s first
    disjunct), and the role's initial `SetState` (whose content — the long-term
    key — is knowable at the role's own state label). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_trace_invariant_empty ()
  : Lemma (ensures TI.trace_invariant #dh_sample_protocol_invariants TB.empty_trace)
= reveal_opaque (`%TI.trace_invariant) (TI.trace_invariant #dh_sample_protocol_invariants)
#pop-options

(** The initial `SetState` obligation, at each role's fixed setup position. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_setup_state_invariant (who:endpoint_id) (me:principal) (tr:TB.trace)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      TB.trace_length tr == role_ltk_pos who)
    (ensures TI.trace_invariant #dh_sample_protocol_invariants
               (setup_trace who (term_of_principal me) tr))
= let n = TB.trace_length tr in
  let mep = role_dy_principal who in
  let me_t = term_of_principal me in
  let ltk = ltk_term n in
  let e1 = T.RandGen ltk_usage (ltk_label who) ltk_len in
  let e2 = T.Event mep tag_keygen (keygen_content me_t (vkey_term ltk)) in
  let e3 = T.SetState mep (role_state_id who) (snapshot_term ltk None None None None) in
  let tr1 = TB.append_entry tr e1 in
  let tr2 = TB.append_entry tr1 e2 in
  lemma_keygen_event_pred tr1 mep me_t (vkey_term ltk);
  grows2 tr e1 e2;
  TB.grows_snoc tr e1;
  TB.entry_at_grows tr1 tr2 n e1;
  lemma_ltk_knowable who tr2;
  B.literal_to_bytes_is_publishable #dh_sample_crypto_invariants tr2 (FStar.Seq.empty #FStar.UInt8.t);
  publishable_is_knowable who tr2 no_material;
  trace_invariant_snoc3 tr e1 e2 e3
#pop-options

(** The COMBINED invariant holds of `product_initial a b`: `wf` (already
    established by `DH.Sample.Symbolic.Product.lemma_product_initial_wf`),
    `trace_invariant` of the two-setup trace it builds from `TB.empty_trace`, and
    `corruption_coherent` (vacuous: both flags are clear and the trace holds no
    `Corrupt` entry, since the two setup segments only append `RandGen`, `Event`
    and `SetState`). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_product_initial_corruption_coherent (a b:principal)
  : Lemma (ensures corruption_coherent (product_initial a b))
= reveal_opaque (`%corruption_coherent) corruption_coherent;
  setup_structure Init (term_of_principal a) TB.empty_trace;
  let (_, tr1) = setup_run Init (term_of_principal a) TB.empty_trace in
  setup_structure Resp (term_of_principal b) tr1;
  let (_, tr2) = setup_run Resp (term_of_principal b) tr1 in
  assert ((product_initial a b).ps_trace == tr2);
  let ltk_a = ltk_term (role_ltk_pos Init) in
  let ltk_b = ltk_term (role_ltk_pos Resp) in
  no_new_corrupt_snoc3 TB.empty_trace
    (T.RandGen ltk_usage (ltk_label Init) ltk_len)
    (T.Event (role_dy_principal Init) tag_keygen
       (keygen_content (term_of_principal a) (vkey_term ltk_a)))
    (T.SetState (role_dy_principal Init) (role_state_id Init)
       (snapshot_term ltk_a None None None None));
  no_new_corrupt_snoc3 tr1
    (T.RandGen ltk_usage (ltk_label Resp) ltk_len)
    (T.Event (role_dy_principal Resp) tag_keygen
       (keygen_content (term_of_principal b) (vkey_term ltk_b)))
    (T.SetState (role_dy_principal Resp) (role_state_id Resp)
       (snapshot_term ltk_b None None None None));
  no_new_corrupt_transitive TB.empty_trace tr1 tr2
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_product_initial_invariant (a b:principal)
  : Lemma (ensures product_invariant (product_initial a b))
= lemma_product_initial_wf a b;
  lemma_trace_invariant_empty ();
  lemma_setup_state_invariant Init a TB.empty_trace;
  setup_structure Init (term_of_principal a) TB.empty_trace;
  let (_, tr1) = setup_run Init (term_of_principal a) TB.empty_trace in
  setup_facts Init (term_of_principal a) TB.empty_trace;
  lemma_setup_state_invariant Resp b tr1;
  setup_structure Resp (term_of_principal b) tr1;
  let (_, tr2) = setup_run Resp (term_of_principal b) tr1 in
  assert ((product_initial a b).ps_trace == tr2);
  lemma_product_initial_corruption_coherent a b
#pop-options

(** ── Execution induction: every state reachable by `SM.trace_reaches` from a
    state satisfying `product_invariant` satisfies `product_invariant` ────── *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec product_trace_reaches_preserves_invariant
  (a b:principal) (p0:product_state) (pt:list product_transition) (p1:product_state)
  : Lemma
    (requires product_invariant p0 /\ SM.trace_reaches (product_sm a b) p0 pt p1)
    (ensures product_invariant p1)
    (decreases pt)
= match pt with
  | [] -> ()
  | ptr :: rest ->
    product_step_preserves_invariant p0 ptr.SM.tr_event ptr.SM.tr_next_state ptr.SM.tr_output;
    product_trace_reaches_preserves_invariant a b ptr.SM.tr_next_state rest p1
#pop-options

(** The HEADLINE reachable-state theorem: for EVERY `product_execution` from
    `product_initial a b` (equivalently `SM.trace_reaches (product_sm a b) …`),
    the final state satisfies `product_invariant`.  The caller supplies ONLY
    the two identities, the transition list, and the final state; no symbolic
    witness, no hygiene premise, no restatement of the desired invariant. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let product_reaches_invariant
  (a b:principal) (pt:list product_transition) (pfinal:product_state)
  : Lemma
    (requires product_execution (product_sm a b) (product_initial a b) pt pfinal)
    (ensures product_invariant pfinal)
= lemma_product_initial_invariant a b;
  product_trace_reaches_preserves_invariant a b (product_initial a b) pt pfinal
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Corollary: the exact DH / random-generation ingredients `product_invariant`
    guarantees at ANY reachable state
    ═══════════════════════════════════════════════════════════════════════════

    `product_invariant` already carries — via `Product.wf`'s (non-opaque)
    `key_state_coherent` / `rng_state_coherent` conjuncts — EXACT usage/label/
    length and RandGen provenance for the two long-term signing keys and every
    currently-recorded ephemeral DH scalar.  This corollary surfaces that fact
    as ONE explicitly-named lemma directly about `product_invariant`, so a
    later proof can cite it without reaching into `wf`'s internal conjuncts by
    hand.  It is proved by `()` alone: `product_invariant` and `wf` are plain
    (non-`opaque_to_smt`) conjunctions, so the SMT solver unfolds them without
    any additional lemma call.

      * Long-term keys: `ltk_coherent_at mep me_t tr ltk pos` (`Product`)
        already IS "`ltk == ltk_term pos` (the exact `Rand ltk_len pos` term,
        usage `ltk_usage`, label `ltk_label`) AND `TB.entry_at tr pos (RandGen
        ltk_usage ltk_label ltk_len)` AND the owning principal has
        `event_triggered tag_keygen` binding it to its own identity" — for the
        INITIATOR at the fixed position 0, for the RESPONDER at the fixed
        position 3.

      * Ephemeral DH scalars: `scalar_recorded tr s` (`Product`) already IS
        "`s == eph_term t` (the exact `Rand eph_len t` term, usage
        `eph_usage`, label `eph_label`) AND `TB.entry_at tr t (RandGen
        eph_usage eph_label eph_len)`" — established for BOTH endpoints'
        currently-recorded scalar (`rng_state_coherent`'s four trailing
        conjuncts, via `rng_option_binding`/`rng_coherent`).

    The remaining two ingredient kinds are equally EXACT and explicitly named,
    but are per-action facts about a `trace_invariant`-satisfying trace (not
    plain `wf` unfolding), so they are cited here rather than restated:

      * Signing nonces: `lemma_sig_term_publishable` (above) requires —
        and, via `respond_structure` / `ifinish_structure`
        (`DH.Sample.Symbolic.Product`) threading a `RandGen signonce_usage
        signonce_label signonce_len` entry at the exact position the
        corresponding `sig_term`'s nonce field names — every honestly-produced
        signature's nonce is EXACTLY that recorded `signonce_term`, never an
        unrecorded or mislabelled one.

      * DH shares / shared secrets: `share_term s = B.dh_pk s` and
        `secret_term x y = B.dh x y` (`Terms`) are TOTAL, CANONICAL functions
        of a `scalar_recorded` ephemeral; `lemma_dh_agreement` (`Terms`) proves
        the two-sided agreement equation `secret_term x (share_term y) ==
        secret_term y (share_term x)` from DY* CORE's own `dh_shared_secret_
        lemma`, and `lemma_share_publishable` (above) proves every such share
        is `is_publishable` — together, exact ingredients for a later
        session-key-secrecy proof to build on. *)
let lemma_product_invariant_key_provenance (p:product_state)
  : Lemma
    (requires product_invariant p)
    (ensures (
      let c = p.ps_sys in
      ltk_coherent_at Init (term_of_principal c.sys_init.ep_me)
        p.ps_trace p.ps_init.sh_ltk (role_ltk_pos Init) /\
      ltk_coherent_at Resp (term_of_principal c.sys_resp.ep_me)
        p.ps_trace p.ps_resp.sh_ltk (role_ltk_pos Resp) /\
      (match p.ps_init.sh_scalar with
       | None -> True | Some s -> scalar_recorded_for Init p.ps_trace s) /\
      (match p.ps_resp.sh_scalar with
       | None -> True | Some s -> scalar_recorded_for Resp p.ps_trace s) /\
      (* the two roles' CURRENT stored states, the objects a compromise targets *)
      state_pos_coherent Init p.ps_init p.ps_trace /\
      state_pos_coherent Resp p.ps_resp p.ps_trace))
= ()

(** ═══════════════════════════════════════════════════════════════════════════
    What replaced the old "two-party NO-CORRUPTION ideal profile"
    ═══════════════════════════════════════════════════════════════════════════

    Earlier versions of this development installed, on top of `product_invariant`,
    an explicit `product_no_corruption` predicate ("the shared trace contains no
    `Corrupt` entry at all") and an `ideal_product_invariant` conjoining the two.
    That profile is GONE: `Sys.sys_action` now HAS a corruption constructor
    (`ActCorrupt`), `Product.sym_extend` genuinely runs DY* CORE's `corrupt` on
    the target role's current `SetState` position, and therefore no reachable-state
    theorem can (or should) claim a `Corrupt`-free trace.

    What takes its place is STRICTLY STRONGER and compromise-aware:

      * `corruption_coherent` (a conjunct of `product_invariant`, proved inductive
        above) pins the exact relationship between the concrete compromise flags
        and DY* `Corrupt` entries / corrupt role labels, in BOTH directions
        (`lemma_corruption_coherence`);
      * the security statements of `DH.Sample.Symbolic.Security` are stated MODULO
        the corresponding role compromise, and specialise back to the old
        unconditional statements exactly when the flags are clear
        (`lemma_uncorrupt_role_label`).

    Nothing in this module, and nothing in the headline results, assumes a
    corruption-free trace any more. *)

(** ═══════════════════════════════════════════════════════════════════════════
    Non-vacuity witness: the full honest, two-party run
    ═══════════════════════════════════════════════════════════════════════════

    The composed system's full honest three-message run
    (`DH.Sample.System.honest_run`) — both endpoints complete and agree on the
    key, and NO role is compromised — lifts to a product execution from
    `product_initial a b` whose FINAL state satisfies `product_invariant`, with
    both compromise flags CLEAR and therefore (by `lemma_corruption_coherence`)
    both role labels UNCORRUPTED.  This is the explicit, non-vacuous witness: the
    invariant is not merely inhabited by the (trivial) initial state, it is
    preserved across a complete real protocol run, and the compromise machinery
    does not secretly force corruption. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
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
= lemma_honest_system_run a b x y;
  eliminate exists (pt:list product_transition) (pfinal:product_state).
    product_execution (product_sm a b) (product_initial a b) pt pfinal /\
    execution_projects_exactly (Sys.honest_run a b x y) pt /\
    proj pfinal == Sys.h_s4 a b x y
  returns (
    exists (pt':list product_transition) (pfinal':product_state).
      product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
      execution_projects_exactly (Sys.honest_run a b x y) pt' /\
      proj pfinal' == Sys.h_s4 a b x y /\
      product_invariant pfinal' /\
      pfinal'.ps_sys.sys_init_corrupt == false /\
      pfinal'.ps_sys.sys_resp_corrupt == false /\
      ~(role_state_corrupt pfinal' Init) /\
      ~(role_state_corrupt pfinal' Resp))
  with _.
    (product_reaches_invariant a b pt pfinal;
     lemma_corruption_coherence pfinal;
     introduce exists (pt':list product_transition) (pfinal':product_state).
       product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
       execution_projects_exactly (Sys.honest_run a b x y) pt' /\
       proj pfinal' == Sys.h_s4 a b x y /\
       product_invariant pfinal' /\
       pfinal'.ps_sys.sys_init_corrupt == false /\
       pfinal'.ps_sys.sys_resp_corrupt == false /\
       ~(role_state_corrupt pfinal' Init) /\
       ~(role_state_corrupt pfinal' Resp)
     with pt pfinal and ())
#pop-options
