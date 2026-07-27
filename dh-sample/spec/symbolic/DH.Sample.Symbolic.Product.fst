module DH.Sample.Symbolic.Product

(**
  DH.Sample.Symbolic.Product — the *symbolic product of the WHOLE composed
  system*.  There is ONE product state, containing the complete concrete system
  state (`DH.Sample.System.system_state` — both endpoints AND the explicit
  network) verbatim, together with a SINGLE shared Dolev-Yao / DY* trace and
  coherent symbolic shadows for BOTH endpoints, every private RNG-registry
  entry, and every network packet.

  This module depends ONLY on the DY* CORE library, the neutral
  Common.StateMachine framework, the standalone dh-sample pure specification
  (including the composed `DH.Sample.System`) and DH.Sample.Symbolic.Terms.  It
  never imports, opens or reuses any DY* example, and it never references any
  example module.

  One trace, honest structured sends, sound attacker injection
  ------------------------------------------------------------
  The provenance of every step is produced by RUNNING the genuine DY* CORE
  trace-monad operations (`mk_rand`, `trigger_event`, `send_msg`, `recv_msg`)
  threaded in causal order on the ONE shared trace.  Both endpoints run their
  setups on this single trace, so their long-term keys are DISTINCT `RandGen`
  entries (times 0 and 3), attributed to fixed distinct DY role principals.
  Consequently:

    * only an explicit composed `ActRng` runs `mk_rand` for an ephemeral.  Its
      concrete registry entry and secret `Rand` are paired in `ps_rng`; start
      and responder-response steps consume the pending pair rather than
      idealising an unrestricted scalar after the fact;

    * an HONEST send puts the EXACT STRUCTURED symbolic message the sender
      generated onto the wire (`send_msg (flatten smsg)` where the share is
      `share_term (its own scalar)` and the signature is `sig_term ltk nonce
      transcript` — genuine `DhPub` / `Sign` terms, NEVER literals).  Signature
      provenance pins `ltk` to the exact sender-role shadow key, the nonce to the
      send position, and the transcript to the stored structured shares.  The
      network shadow (`ps_net`) stores that same `sym_msg`, so a later DELIVERY
      reuses the identical term;

    * an ATTACKER INJECTION puts a publishable all-literal message on the wire
      (`inject_smsg m`), modelling sound Dolev-Yao traffic (publishability is
      discharged in DH.Sample.Symbolic.Provenance).  An injected Msg1 CAN drive
      responder progress (Msg1 delivery is unrestricted), but its shadow is a
      public `Literal`, not an honest `share_term`;

    * a DELIVERY reads a prior `MsgSent` with the genuine `recv_msg` at the
      delivered packet's recorded position, and the receiver combines its scalar
      with the STRUCTURED share it actually received.  Completion deliveries
      additionally carry `system_step`'s `ideal_completion_link_ok` run/session
      link (same Msg1 index) and the honest `Sent Resp`/`Sent Init` completion
      origin.

  Because one concrete system step performs several DY* operations, the product
  is a stuttering refinement whose observable projection onto the concrete system
  is nonetheless EXACT (same before state, event, after state, outputs).

  Dynamic compromise
  ------------------
  Each role owns ONE DY* state (`Terms.role_state_id`).  Every segment that
  changes a role's live secret material ENDS with a genuine `set_state` storing
  that role's CURRENT snapshot — long-term key, pending draw, ephemeral scalar,
  received peer share AND session key (`Terms.snapshot_term`) — and the role's
  shadow records the trace POSITION of that `SetState` (`sh_state_pos`), which
  `wf` pins to hold exactly that snapshot.  `ActCorrupt who` then runs the
  genuine DY* CORE `corrupt` on THAT position, so a compromise deterministically
  hands the attacker exactly the material the role holds at that moment.  The
  responder's Msg3 completion stores nothing new: it changes its PHASE, not its
  key material (whose snapshot was already written at its Msg1 delivery).

  NO ERASURE is modelled: material is never dropped from a later snapshot, so a
  post-session compromise still reveals the session key.  Consequently this model
  offers NO forward secrecy, by design and explicitly (see
  dh-sample/SYMBOLIC_SECURITY.md).

  The symbolic-crypto boundary versus computational assumptions
  ------------------------------------------------------------
  This is a symbolic-crypto model: signatures are genuine `Sign` terms and
  unforgeability holds only while the SIGNING ROLE is uncompromised (an attacker
  injection is an all-literal term, which cannot be an honest `Sign`; a
  completion delivery requires the appropriate honest peer origin AND a matching
  run link UNLESS that peer is compromised — see `DH.Sample.System`).  The
  abstract concrete interface states only functional correctness; no
  computational hardness theorem is assumed or proved here, and the interface
  alone is never the justification for a completion.
*)

module SM   = Common.StateMachine
module SMc  = DH.Sample.StateMachine
module Sys  = DH.Sample.System
module Cr   = DH.Sample.Crypto
module B    = DY.Core.Bytes
module BT   = DY.Core.Bytes.Type
module T    = DY.Core.Trace.Type
module TB   = DY.Core.Trace.Base
module LT   = DY.Core.Label.Type
module L    = FStar.List.Tot
open DY.Core.Trace.Manipulation

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.System
open DH.Sample.Symbolic.Terms

(** ── Effect of each DY* CORE trace operation ───────────────────────────────
    First-order, SMT-pattern-triggered characterisations of the genuine trace
    operations, proved by revealing the opaque operation. *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let mk_rand_effect (usg:BT.usage) (lab:LT.label) (len:nat{len <> 0}) (tr:TB.trace)
  : Lemma
    (ensures mk_rand usg lab len tr ==
             (BT.Rand len (TB.trace_length tr), TB.append_entry tr (T.RandGen usg lab len)))
    [SMTPat (mk_rand usg lab len tr)]
= reveal_opaque (`%mk_rand) mk_rand

let send_msg_effect (msg:BT.bytes) (tr:TB.trace)
  : Lemma
    (ensures send_msg msg tr == (TB.trace_length tr, TB.append_entry tr (T.MsgSent msg)))
    [SMTPat (send_msg msg tr)]
= reveal_opaque (`%send_msg) send_msg

let trigger_event_effect (p:T.principal) (tag:string) (content:BT.bytes) (tr:TB.trace)
  : Lemma
    (ensures trigger_event p tag content tr == ((), TB.append_entry tr (T.Event p tag content)))
    [SMTPat (trigger_event p tag content tr)]
= reveal_opaque (`%trigger_event) trigger_event

let recv_msg_effect (i:T.timestamp) (tr:TB.trace)
  : Lemma
    (ensures snd (recv_msg i tr) == tr)
    [SMTPat (recv_msg i tr)]
= reveal_opaque (`%recv_msg) recv_msg

(** The genuine DY* CORE state-storing operation: appending one `SetState` entry
    for the principal / session identifier / content given. *)
let set_state_effect (prin:T.principal) (sid:T.state_id) (content:BT.bytes) (tr:TB.trace)
  : Lemma
    (ensures set_state prin sid content tr ==
             ((), TB.append_entry tr (T.SetState prin sid content)))
    [SMTPat (set_state prin sid content tr)]
= reveal_opaque (`%set_state) set_state

(** The genuine DY* CORE compromise operation: appending one `Corrupt` entry
    naming the trace position of the state being compromised. *)
let corrupt_effect (time:T.timestamp) (tr:TB.trace)
  : Lemma
    (ensures corrupt time tr == ((), TB.append_entry tr (T.Corrupt time)))
    [SMTPat (corrupt time tr)]
= reveal_opaque (`%corrupt) corrupt

#pop-options

(** ── Genuine DY* trace-monad segments ───────────────────────────────────────
    Each concrete system step's provenance is the trace produced by RUNNING these
    computations.  Receiving segments begin with a genuine `recv_msg` at the
    delivered packet's position (which does not change the trace) and then append
    the endpoint's own random generations / authorizations / sends.

    EVERY segment that changes a role's live secret material ENDS with a genuine
    DY* `set_state` writing that role's NEW snapshot (`content`, supplied by the
    caller, which is exactly `shadow_snapshot` of the updated shadow — see
    `sym_extend`).  That `SetState` entry is the object a later `Corrupt` entry
    points at, so a compromise always hands the attacker EXACTLY the material the
    role holds at that moment.  The responder's Msg3 completion changes only its
    PHASE — no new key material — so it writes no new state (its session key was
    already retained in the snapshot written at its Msg1 delivery). *)

(** Setup: draw the endpoint's long-term signing key, register it, and store the
    initial role state (the long-term key only). *)
let setup_run (who:endpoint_id) (me_t:BT.bytes) (tr:TB.trace) : (BT.bytes & TB.trace) =
  let mep = role_dy_principal who in
  let (ltk, tr) = mk_rand ltk_usage (ltk_label who) ltk_len tr in
  let (_, tr) = trigger_event mep tag_keygen (keygen_content me_t (vkey_term ltk)) tr in
  let (_, tr) = set_state mep (role_state_id who) (snapshot_term ltk None None None None) tr in
  (ltk, tr)

(** One explicit ideal-RNG transition: draw a role-labelled ephemeral, then
    refresh the drawing role's stored state (which now holds the pending draw). *)
let rng_run (who:endpoint_id) (content:BT.bytes) (tr:TB.trace) : (BT.bytes & TB.trace) =
  let (scalar, tr) = mk_rand eph_usage (eph_label who) eph_len tr in
  let (_, tr) = set_state (role_dy_principal who) (role_state_id who) content tr in
  (scalar, tr)

(** Initiator start consumes a scalar drawn by an earlier `rng_run`. *)
let start_run (me_t peer_t scalar content:BT.bytes) (tr:TB.trace)
  : (BT.bytes & TB.trace) =
  let mep = role_dy_principal Init in
  let (_, tr) = trigger_event mep tag_initiate (initiate_content me_t peer_t (share_term scalar)) tr in
  let (_, tr) = send_msg (flatten (SMsg1 me_t (share_term scalar))) tr in
  let (_, tr) = set_state mep (role_state_id Init) content tr in
  (scalar, tr)

(** Responder respond consumes a scalar drawn by an earlier `rng_run`: read the
    delivered message 1, authorize, draw a signing nonce, send message 2, and
    store the new responder state (scalar, peer share AND session key). *)
let respond_run (ltk me_t a_t peer_share scalar content:BT.bytes)
                (tr:TB.trace) (rpos:nat)
  : (BT.bytes & TB.trace) =
  let mep = role_dy_principal Resp in
  let (_, tr) = recv_msg rpos tr in
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let (_, tr) = trigger_event mep tag_responder_respond transcript tr in
  let (signonce, tr) = mk_rand signonce_usage (signonce_label Resp) signonce_len tr in
  let (_, tr) = send_msg (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk signonce transcript))) tr in
  let (_, tr) = set_state mep (role_state_id Resp) content tr in
  (scalar, tr)

(** Initiator finish: read the delivered message 2, authorize, draw a signing
    nonce, send message 3, and store the new initiator state (peer share AND
    session key). *)
let ifinish_run (ltk scalar b_t peer_share content:BT.bytes) (tr:TB.trace) (rpos:nat)
  : (unit & TB.trace) =
  let mep = role_dy_principal Init in
  let (_, tr) = recv_msg rpos tr in
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let (_, tr) = trigger_event mep tag_initiator_finish transcript tr in
  let (signonce, tr) = mk_rand signonce_usage (signonce_label Init) signonce_len tr in
  let (_, tr) = send_msg (flatten (SMsg3 (sig_term ltk signonce transcript))) tr in
  let (_, tr) = set_state mep (role_state_id Init) content tr in
  ((), tr)

(** Responder finish: read the delivered message 3, record completion.  No new
    key material, hence no new stored state. *)
let rfinish_run (a_t key:BT.bytes) (tr:TB.trace) (rpos:nat) : (unit & TB.trace) =
  let (_, tr) = recv_msg rpos tr in
  trigger_event (role_dy_principal Resp) tag_responder_finish (session_content a_t key) tr

(** Attacker injection: put publishable all-literal bytes on the network. *)
let inject_run (sm:sym_msg) (tr:TB.trace) : (nat & TB.trace) =
  send_msg (flatten sm) tr

(** DYNAMIC COMPROMISE: the genuine DY* CORE `corrupt` operation, applied to the
    trace position of the target role's CURRENT stored state.  This is the only
    place a `Corrupt` entry is ever produced, and it is deterministic: the
    position is read off the role's shadow, never chosen by a caller. *)
let corrupt_run (pos:nat) (tr:TB.trace) : (unit & TB.trace) =
  corrupt pos tr

(** ── Transparent trace chains of each segment ───────────────────────────────*)

let setup_trace (who:endpoint_id) (me_t:BT.bytes) (tr:TB.trace) : TB.trace =
  let mep = role_dy_principal who in
  let ltk = ltk_term (TB.trace_length tr) in
  TB.append_entry
    (TB.append_entry
      (TB.append_entry tr (T.RandGen ltk_usage (ltk_label who) ltk_len))
      (T.Event mep tag_keygen (keygen_content me_t (vkey_term ltk))))
    (T.SetState mep (role_state_id who) (snapshot_term ltk None None None None))

let rng_trace (who:endpoint_id) (content:BT.bytes) (tr:TB.trace) : TB.trace =
  TB.append_entry
    (TB.append_entry tr (T.RandGen eph_usage (eph_label who) eph_len))
    (T.SetState (role_dy_principal who) (role_state_id who) content)

let start_trace (me_t peer_t scalar content:BT.bytes) (tr:TB.trace) : TB.trace =
  let mep = role_dy_principal Init in
  TB.append_entry
    (TB.append_entry
      (TB.append_entry tr
        (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))))
      (T.MsgSent (flatten (SMsg1 me_t (share_term scalar)))))
    (T.SetState mep (role_state_id Init) content)

let respond_trace (ltk me_t a_t peer_share scalar content:BT.bytes)
                  (tr:TB.trace) : TB.trace =
  let mep = role_dy_principal Resp in
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let signonce = signonce_term (TB.trace_length tr + 1) in
  TB.append_entry
    (TB.append_entry
      (TB.append_entry
        (TB.append_entry tr
          (T.Event mep tag_responder_respond transcript))
        (T.RandGen signonce_usage (signonce_label Resp) signonce_len))
      (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk signonce transcript)))))
    (T.SetState mep (role_state_id Resp) content)

let ifinish_trace (ltk scalar b_t peer_share content:BT.bytes) (tr:TB.trace) : TB.trace =
  let mep = role_dy_principal Init in
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let signonce = signonce_term (TB.trace_length tr + 1) in
  TB.append_entry
    (TB.append_entry
      (TB.append_entry
        (TB.append_entry tr (T.Event mep tag_initiator_finish transcript))
        (T.RandGen signonce_usage (signonce_label Init) signonce_len))
      (T.MsgSent (flatten (SMsg3 (sig_term ltk signonce transcript)))))
    (T.SetState mep (role_state_id Init) content)

let rfinish_trace (a_t key:BT.bytes) (tr:TB.trace) : TB.trace =
  TB.append_entry tr
    (T.Event (role_dy_principal Resp) tag_responder_finish (session_content a_t key))

let inject_trace (sm:sym_msg) (tr:TB.trace) : TB.trace =
  TB.append_entry tr (T.MsgSent (flatten sm))

let corrupt_trace (pos:nat) (tr:TB.trace) : TB.trace =
  TB.append_entry tr (T.Corrupt pos)

(** ── Structure lemmas: each run equals its transparent chain ────────────────*)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"

let setup_structure (who:endpoint_id) (me_t:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let (ltk, tr') = setup_run who me_t tr in
      ltk == ltk_term (TB.trace_length tr) /\ tr' == setup_trace who me_t tr))
= let (ltk, tr') = setup_run who me_t tr in
  assert (ltk == ltk_term (TB.trace_length tr));
  assert (tr' == setup_trace who me_t tr)

let rng_structure (who:endpoint_id) (content:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let (scalar, tr') = rng_run who content tr in
      scalar == eph_term (TB.trace_length tr) /\ tr' == rng_trace who content tr))
= let (scalar, tr') = rng_run who content tr in
  assert (scalar == eph_term (TB.trace_length tr));
  assert (tr' == rng_trace who content tr)

let start_structure (me_t peer_t scalar content:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let (scalar', tr') = start_run me_t peer_t scalar content tr in
      scalar' == scalar /\ tr' == start_trace me_t peer_t scalar content tr))
= let (scalar', tr') = start_run me_t peer_t scalar content tr in
  assert (scalar' == scalar);
  assert (tr' == start_trace me_t peer_t scalar content tr)

let respond_structure (ltk me_t a_t peer_share scalar content:BT.bytes)
                      (tr:TB.trace) (rpos:nat)
  : Lemma (ensures (
      let (scalar', tr') = respond_run ltk me_t a_t peer_share scalar content tr rpos in
      scalar' == scalar /\
      tr' == respond_trace ltk me_t a_t peer_share scalar content tr))
= let (scalar', tr') = respond_run ltk me_t a_t peer_share scalar content tr rpos in
  assert (scalar' == scalar);
  assert (tr' == respond_trace ltk me_t a_t peer_share scalar content tr)

let ifinish_structure (ltk scalar b_t peer_share content:BT.bytes) (tr:TB.trace) (rpos:nat)
  : Lemma (ensures (
      let (_, tr') = ifinish_run ltk scalar b_t peer_share content tr rpos in
      tr' == ifinish_trace ltk scalar b_t peer_share content tr))
= let (_, tr') = ifinish_run ltk scalar b_t peer_share content tr rpos in
  assert (tr' == ifinish_trace ltk scalar b_t peer_share content tr)

let rfinish_structure (a_t key:BT.bytes) (tr:TB.trace) (rpos:nat)
  : Lemma (ensures (
      let (_, tr') = rfinish_run a_t key tr rpos in
      tr' == rfinish_trace a_t key tr))
= let (_, tr') = rfinish_run a_t key tr rpos in
  assert (tr' == rfinish_trace a_t key tr)

let inject_structure (sm:sym_msg) (tr:TB.trace)
  : Lemma (ensures (
      let (pos, tr') = inject_run sm tr in
      pos == TB.trace_length tr /\ tr' == inject_trace sm tr))
= let (pos, tr') = inject_run sm tr in
  assert (pos == TB.trace_length tr);
  assert (tr' == inject_trace sm tr)

let corrupt_structure (pos:nat) (tr:TB.trace)
  : Lemma (ensures (
      let (_, tr') = corrupt_run pos tr in
      tr' == corrupt_trace pos tr))
= reveal_opaque (`%corrupt) corrupt

#pop-options

(** ── `grows` chaining helpers for nested append_entry ───────────────────────*)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let grows2 (tr:TB.trace) (e1 e2:TB.trace_entry)
  : Lemma (ensures tr `TB.grows` TB.append_entry (TB.append_entry tr e1) e2)
= let t1 = TB.append_entry tr e1 in
  TB.grows_snoc tr e1;
  TB.grows_snoc t1 e2;
  TB.grows_transitive tr t1 (TB.append_entry t1 e2)

let grows3 (tr:TB.trace) (e1 e2 e3:TB.trace_entry)
  : Lemma (ensures tr `TB.grows` TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3)
= let t2 = TB.append_entry (TB.append_entry tr e1) e2 in
  grows2 tr e1 e2;
  TB.grows_snoc t2 e3;
  TB.grows_transitive tr t2 (TB.append_entry t2 e3)

let grows4 (tr:TB.trace) (e1 e2 e3 e4:TB.trace_entry)
  : Lemma (ensures tr `TB.grows`
             TB.append_entry (TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3) e4)
= let t3 = TB.append_entry (TB.append_entry (TB.append_entry tr e1) e2) e3 in
  grows3 tr e1 e2 e3;
  TB.grows_snoc t3 e4;
  TB.grows_transitive tr t3 (TB.append_entry t3 e4)
#pop-options

(** ── Segment facts: growth and exact entry positions ────────────────────────

    Every segment's `grows` fact plus the EXACT position of each entry it appends,
    including the trailing `SetState` (whose position is what the role's shadow
    records as its "current state pointer", and what a later `Corrupt` targets). *)

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10"

let setup_facts (who:endpoint_id) (me_t:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let mep = role_dy_principal who in
      let tr' = setup_trace who me_t tr in
      tr `TB.grows` tr' /\
      TB.trace_length tr' == n + 3 /\
      TB.entry_at tr' n (T.RandGen ltk_usage (ltk_label who) ltk_len) /\
      TB.entry_at tr' (n + 1) (T.Event mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n)))) /\
      TB.entry_at tr' (n + 2)
        (T.SetState mep (role_state_id who) (snapshot_term (ltk_term n) None None None None)) /\
      TB.event_triggered tr' mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n)))))
= let n = TB.trace_length tr in
  let mep = role_dy_principal who in
  grows3 tr (T.RandGen ltk_usage (ltk_label who) ltk_len)
            (T.Event mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n))))
            (T.SetState mep (role_state_id who) (snapshot_term (ltk_term n) None None None None))

let rng_facts (who:endpoint_id) (content:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = rng_trace who content tr in
      tr `TB.grows` tr' /\
      TB.trace_length tr' == n + 2 /\
      TB.entry_at tr' n (T.RandGen eph_usage (eph_label who) eph_len) /\
      TB.entry_at tr' (n + 1)
        (T.SetState (role_dy_principal who) (role_state_id who) content)))
= let n = TB.trace_length tr in
  grows2 tr (T.RandGen eph_usage (eph_label who) eph_len)
            (T.SetState (role_dy_principal who) (role_state_id who) content)

let start_facts (me_t peer_t scalar content:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let mep = role_dy_principal Init in
      let tr' = start_trace me_t peer_t scalar content tr in
      tr `TB.grows` tr' /\
      TB.trace_length tr' == n + 3 /\
      TB.entry_at tr' n (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))) /\
      TB.entry_at tr' (n + 1) (T.MsgSent (flatten (SMsg1 me_t (share_term scalar)))) /\
      TB.entry_at tr' (n + 2) (T.SetState mep (role_state_id Init) content) /\
      TB.event_triggered tr' mep tag_initiate (initiate_content me_t peer_t (share_term scalar))))
= let n = TB.trace_length tr in
  let mep = role_dy_principal Init in
  let tr' = start_trace me_t peer_t scalar content tr in
  grows3 tr (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar)))
            (T.MsgSent (flatten (SMsg1 me_t (share_term scalar))))
            (T.SetState mep (role_state_id Init) content);
  assert (TB.entry_at tr' n (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))));
  assert (TB.entry_at tr' (n + 1) (T.MsgSent (flatten (SMsg1 me_t (share_term scalar)))))

let respond_facts (ltk me_t a_t peer_share scalar content:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let mep = role_dy_principal Resp in
      let transcript = transcript_term a_t peer_share (share_term scalar) in
      let tr' = respond_trace ltk me_t a_t peer_share scalar content tr in
      tr `TB.grows` tr' /\
      TB.trace_length tr' == n + 4 /\
      TB.entry_at tr' n (T.Event mep tag_responder_respond transcript) /\
      TB.entry_at tr' (n + 1) (T.RandGen signonce_usage (signonce_label Resp) signonce_len) /\
      TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript)))) /\
      TB.entry_at tr' (n + 3) (T.SetState mep (role_state_id Resp) content) /\
      TB.event_triggered tr' mep tag_responder_respond transcript))
= let n = TB.trace_length tr in
  let mep = role_dy_principal Resp in
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let tr' = respond_trace ltk me_t a_t peer_share scalar content tr in
  grows4 tr (T.Event mep tag_responder_respond transcript)
            (T.RandGen signonce_usage (signonce_label Resp) signonce_len)
            (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript))))
            (T.SetState mep (role_state_id Resp) content);
  assert (TB.entry_at tr' n (T.Event mep tag_responder_respond transcript));
  assert (TB.entry_at tr' (n + 1) (T.RandGen signonce_usage (signonce_label Resp) signonce_len));
  assert (TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript)))))

let ifinish_facts (ltk scalar b_t peer_share content:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let mep = role_dy_principal Init in
      let transcript = transcript_term b_t (share_term scalar) peer_share in
      let tr' = ifinish_trace ltk scalar b_t peer_share content tr in
      tr `TB.grows` tr' /\
      TB.trace_length tr' == n + 4 /\
      TB.entry_at tr' n (T.Event mep tag_initiator_finish transcript) /\
      TB.entry_at tr' (n + 1) (T.RandGen signonce_usage (signonce_label Init) signonce_len) /\
      TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript)))) /\
      TB.entry_at tr' (n + 3) (T.SetState mep (role_state_id Init) content) /\
      TB.event_triggered tr' mep tag_initiator_finish transcript))
= let n = TB.trace_length tr in
  let mep = role_dy_principal Init in
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let tr' = ifinish_trace ltk scalar b_t peer_share content tr in
  grows4 tr (T.Event mep tag_initiator_finish transcript)
            (T.RandGen signonce_usage (signonce_label Init) signonce_len)
            (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript))))
            (T.SetState mep (role_state_id Init) content);
  assert (TB.entry_at tr' n (T.Event mep tag_initiator_finish transcript));
  assert (TB.entry_at tr' (n + 1) (T.RandGen signonce_usage (signonce_label Init) signonce_len));
  assert (TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript)))))

let rfinish_facts (a_t key:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let mep = role_dy_principal Resp in
      let tr' = rfinish_trace a_t key tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.Event mep tag_responder_finish (session_content a_t key)) /\
      TB.event_triggered tr' mep tag_responder_finish (session_content a_t key)))
= let n = TB.trace_length tr in
  TB.grows_snoc tr (T.Event (role_dy_principal Resp) tag_responder_finish (session_content a_t key))

let inject_facts (sm:sym_msg) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = inject_trace sm tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.MsgSent (flatten sm))))
= let n = TB.trace_length tr in
  TB.grows_snoc tr (T.MsgSent (flatten sm))

(** The compromise segment: the trace grows by exactly one `Corrupt` entry, which
    names the position given (the target role's current state). *)
let corrupt_facts (pos:nat) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = corrupt_trace pos tr in
      tr `TB.grows` tr' /\
      TB.trace_length tr' == n + 1 /\
      TB.entry_at tr' n (T.Corrupt pos) /\
      TB.entry_exists tr' (T.Corrupt pos)))
= let n = TB.trace_length tr in
  TB.grows_snoc tr (T.Corrupt pos);
  introduce exists (i:nat). TB.entry_at (corrupt_trace pos tr) i (T.Corrupt pos)
  with n and ()

#pop-options

(** ── The product state ─────────────────────────────────────────────────────

    The concrete SYSTEM state verbatim, ONE shared DY* trace, and coherent
    symbolic shadows for both endpoints and for every network packet. *)

noeq
type endpoint_shadow = {
  sh_ltk        : BT.bytes;         (* long-term signing key term (a fresh Rand) *)
  sh_pending    : option BT.bytes;  (* explicit RNG draw reserved for this role *)
  sh_scalar     : option BT.bytes;  (* ephemeral scalar term, once drawn         *)
  sh_peer_share : option BT.bytes;  (* the symbolic peer share received          *)
  sh_key        : option BT.bytes;  (* derived shared-secret term, once computed *)
  (* THE CURRENT STATE POINTER: the trace position of the role's most recent DY*
     `SetState` entry.  `wf` (below) pins that entry to hold EXACTLY this shadow's
     snapshot, and `ActCorrupt` corrupts EXACTLY this position. *)
  sh_state_pos  : nat;
}

(** The DY* state content of a role: every piece of material it currently holds,
    explicitly retained (no erasure — see `DH.Sample.Symbolic.Terms.snapshot_term`).

    It is `opaque_to_smt`: the five-way nested concatenation must not unfold into
    every per-step lift/coherence query (which only ever needs the snapshot as an
    ATOM, matched by congruence from the shadow it is taken of).  The one place
    that genuinely needs its structure — the DY* state-predicate obligation of
    each `SetState` entry, in `DH.Sample.Symbolic.Invariant` — `reveal`s it
    locally, via `lemma_shadow_snapshot_unfold` below. *)
[@@"opaque_to_smt"]
let shadow_snapshot (sh:endpoint_shadow) : BT.bytes =
  snapshot_term sh.sh_ltk sh.sh_pending sh.sh_scalar sh.sh_peer_share sh.sh_key

let lemma_shadow_snapshot_unfold (sh:endpoint_shadow)
  : Lemma (ensures
      shadow_snapshot sh ==
      snapshot_term sh.sh_ltk sh.sh_pending sh.sh_scalar sh.sh_peer_share sh.sh_key)
= reveal_opaque (`%shadow_snapshot) shadow_snapshot

(** Authentication context stored when an honest signature-bearing packet is
    sent.  It makes the signed transcript first-class and exact—never an
    existential "some transcript" recovered later. *)
noeq
type net_auth =
  | NoAuth
  | RespAuth : partner:BT.bytes -> peer_share:BT.bytes -> net_auth
  | InitAuth : partner:BT.bytes -> my_share:BT.bytes -> peer_share:BT.bytes -> net_auth

noeq
type net_entry = {
  ne_smsg : sym_msg;   (* the EXACT structured symbolic message on the wire *)
  ne_pos  : nat;       (* the position of its MsgSent on the shared trace   *)
  ne_auth : net_auth;  (* exact honest signed-transcript inputs, if any      *)
}

(** Symbolic half of one concrete private RNG-registry entry. *)
noeq
type rng_shadow = {
  rs_owner : endpoint_id;
  rs_term  : BT.bytes;
  rs_pos   : nat;
}

noeq
type product_state = {
  ps_sys   : system_state;      (* the concrete composed system state, verbatim  *)
  ps_trace : TB.trace;          (* THE ONE shared DY* trace (grows monotonically) *)
  ps_init  : endpoint_shadow;   (* initiator symbolic shadow                     *)
  ps_resp  : endpoint_shadow;   (* responder symbolic shadow                     *)
  ps_net   : list net_entry;    (* per-packet symbolic shadow, parallel to sys_net *)
  ps_rng   : list rng_shadow;   (* parallel private RNG provenance registry       *)
}

(** The observable projection: the concrete composed system state. *)
let proj (p:product_state) : system_state = p.ps_sys

(** ── Fixed setup positions ──────────────────────────────────────────────────

    Both endpoints' setups run on the ONE shared trace, in a fixed order, so every
    setup entry sits at a FIXED, named position:

      0 : initiator long-term key `RandGen`      3 : responder long-term key `RandGen`
      1 : initiator `Event tag_keygen`           4 : responder `Event tag_keygen`
      2 : initiator initial `SetState`           5 : responder initial `SetState`

    `role_ltk_pos` / `role_setup_state_pos` name them; nothing below hard-codes a
    bare numeral. *)
let role_ltk_pos (who:endpoint_id) : nat =
  match who with
  | Init -> 0
  | Resp -> 3

let role_setup_state_pos (who:endpoint_id) : nat =
  match who with
  | Init -> 2
  | Resp -> 5

(** ── Initial product state ──────────────────────────────────────────────────

    Both endpoints run their setup on the ONE shared trace; each ends by STORING
    its initial role state (its long-term signing key), which is what a later
    `ActCorrupt` of a role that has not yet drawn an ephemeral corrupts. *)
let product_initial (a b:principal) : product_state =
  let (ltk_a, tr1) = setup_run Init (term_of_principal a) TB.empty_trace in
  let (ltk_b, tr2) = setup_run Resp (term_of_principal b) tr1 in
  { ps_sys   = system_initial a b;
    ps_trace = tr2;
    ps_init  = { sh_ltk = ltk_a; sh_pending = None; sh_scalar = None;
                 sh_peer_share = None; sh_key = None;
                 sh_state_pos = role_setup_state_pos Init };
    ps_resp  = { sh_ltk = ltk_b; sh_pending = None; sh_scalar = None;
                 sh_peer_share = None; sh_key = None;
                 sh_state_pos = role_setup_state_pos Resp };
    ps_net   = [];
    ps_rng   = [] }

(** ── The canonical symbolic extension of one system step ────────────────────

    `sym_extend p0 ev` computes the (new trace, new initiator shadow, new
    responder shadow, new network shadow) produced by running the genuine
    trace-monad segment of the shape-legal event `ev` from product state `p0`,
    or `None` if the event is not shape-legal.  Both the product step relation and
    the total lift are DEFINED through this single function, so they agree by
    construction. *)
let sym_extend (p0:product_state) (ev:sys_event)
  : (option (TB.trace & endpoint_shadow & endpoint_shadow & list net_entry & list rng_shadow)) =
  let c0 = p0.ps_sys in
  let n  = TB.trace_length p0.ps_trace in
  match ev with
  | SM.LocalEvent (ActRng owner _) ->
    (match owner with
     | Init ->
       (match p0.ps_init.sh_pending with
        | Some _ -> None
        | None ->
          let scalar = eph_term n in
          let i' = { p0.ps_init with sh_pending = Some scalar; sh_state_pos = n + 1 } in
          let (_, tr') = rng_run Init (shadow_snapshot i') p0.ps_trace in
          Some (tr', i', p0.ps_resp, p0.ps_net,
                { rs_owner = Init; rs_term = scalar; rs_pos = n } :: p0.ps_rng))
     | Resp ->
       (match p0.ps_resp.sh_pending with
        | Some _ -> None
        | None ->
          let scalar = eph_term n in
          let r' = { p0.ps_resp with sh_pending = Some scalar; sh_state_pos = n + 1 } in
          let (_, tr') = rng_run Resp (shadow_snapshot r') p0.ps_trace in
          Some (tr', p0.ps_init, r', p0.ps_net,
                { rs_owner = Resp; rs_term = scalar; rs_pos = n } :: p0.ps_rng)))
  | SM.LocalEvent ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       let me  = c0.sys_init.ep_me in
       let met = term_of_principal me in
       let i' = { p0.ps_init with sh_pending = None; sh_scalar = Some scalar;
                                  sh_state_pos = n + 2 } in
       let (_, tr') =
         start_run met (term_of_principal peer) scalar (shadow_snapshot i') p0.ps_trace in
       let ne = { ne_smsg = SMsg1 met (share_term scalar);
                  ne_pos = n + 1; ne_auth = NoAuth } in
       Some (tr', i', p0.ps_resp, L.append p0.ps_net [ ne ], p0.ps_rng)
     | _, _ -> None)
  | SM.LocalEvent (ActDeliver idx dst) ->
    if idx < L.length c0.sys_net && idx < L.length p0.ps_net then begin
      let ne0  = L.index p0.ps_net idx in
      let cmsg = (L.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg1 a gx ->
        (match p0.ps_resp.sh_pending with
         | None -> None
         | Some scalar ->
           let me  = c0.sys_resp.ep_me in
           let met = term_of_principal me in
           let at  = term_of_principal a in
           let peer_share =
            (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
           let r' = { p0.ps_resp with sh_pending = None; sh_scalar = Some scalar;
                        sh_peer_share = Some peer_share;
                        sh_key = Some (secret_term scalar peer_share);
                        sh_state_pos = n + 3 } in
           let (_, tr') =
            respond_run p0.ps_resp.sh_ltk met at peer_share scalar (shadow_snapshot r')
                        p0.ps_trace ne0.ne_pos in
           let transcript = transcript_term at peer_share (share_term scalar) in
           let ne = {
            ne_smsg = SMsg2 met (share_term scalar)
                        (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
            ne_pos  = n + 2;
            ne_auth = RespAuth at peer_share } in
           Some (tr', p0.ps_init, r', L.append p0.ps_net [ ne ], p0.ps_rng))
      | Resp, Msg3 _ ->
        (* completion changes the responder's PHASE only: no new key material, so
           no new stored state and no move of the current-state pointer. *)
        (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
         | Some a, Some key ->
           let (_, tr') =
             rfinish_run (term_of_principal a) key p0.ps_trace ne0.ne_pos in
           Some (tr', p0.ps_init, p0.ps_resp, p0.ps_net, p0.ps_rng)
         | _ -> None)
      | Init, Msg2 b gy _ ->
        (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
         | Some _xc, Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
           let i' = { p0.ps_init with sh_peer_share = Some peer_share;
                        sh_key = Some (secret_term scalar peer_share);
                        sh_state_pos = n + 3 } in
           let (_, tr') =
             ifinish_run p0.ps_init.sh_ltk scalar
                         (term_of_principal b) peer_share (shadow_snapshot i')
                         p0.ps_trace ne0.ne_pos in
           let transcript = transcript_term (term_of_principal b) (share_term scalar) peer_share in
           let ne = {
             ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk
                               (signonce_term (n + 1)) transcript);
             ne_pos  = n + 2;
             ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share } in
           Some (tr', i', p0.ps_resp, L.append p0.ps_net [ ne ], p0.ps_rng)
         | _ -> None)
      | _, _ -> None
    end else None
  | SM.LocalEvent (ActInject m) ->
    let (pos, tr') = inject_run (inject_smsg m) p0.ps_trace in
    Some (tr', p0.ps_init, p0.ps_resp,
         L.append p0.ps_net
           [ { ne_smsg = inject_smsg m; ne_pos = pos; ne_auth = NoAuth } ],
         p0.ps_rng)
  (* DYNAMIC COMPROMISE: run the genuine DY* CORE `corrupt` on the target role's
     CURRENT state position.  Deterministic (the position is read off the role's
     own shadow) and shadow-preserving: no key material, network packet or RNG
     entry changes — only the trace records the compromise. *)
  | SM.LocalEvent (ActCorrupt who) ->
    let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
    let (_, tr') = corrupt_run sh.sh_state_pos p0.ps_trace in
    Some (tr', p0.ps_init, p0.ps_resp, p0.ps_net, p0.ps_rng)
  | _ -> None

(** ── The product step relation ─────────────────────────────────────────────

    Conjoins the EXACT concrete system step (`System.system_step` on the
    projections — same before state, event, after state, output) with the trace /
    shadow extension produced by the genuine segment. *)
let product_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : GTot prop =
  Sys.system_step p0.ps_sys ev p1.ps_sys out /\
  (match sym_extend p0 ev with
   | None -> False
   | Some (tr', i', r', net', rng') ->
     p1.ps_trace == tr' /\ p1.ps_init == i' /\ p1.ps_resp == r' /\
     p1.ps_net == net' /\ p1.ps_rng == rng')

(** ── The product state machine ─────────────────────────────────────────────*)

noextract
let product_sm (a b:principal)
  : SM.state_machine product_state dh_message sys_action local_output = {
  SM.sm_initial_state = product_initial a b;
  SM.sm_step          = product_step;
}

(** ── Coherence profile `wf` ─────────────────────────────────────────────────

    ONE relation tying the concrete system state to the shared trace and the
    symbolic shadows.  It bundles: identity-bound long-term keys for BOTH
    endpoints at their DISTINCT setup positions; a heterogeneous, canonical
    per-endpoint state representation (`init_repr` / `resp_repr`); recorded
    freshness of each present ephemeral; and per-packet network coherence
    (`net_coherent`). *)

let ltk_coherent_at (who:endpoint_id) (me_t:BT.bytes) (tr:TB.trace) (ltk:BT.bytes) (pos:nat) : prop =
  ltk == ltk_term pos /\
  TB.entry_at tr pos (T.RandGen ltk_usage (ltk_label who) ltk_len) /\
  TB.event_triggered tr (role_dy_principal who) tag_keygen
    (keygen_content me_t (vkey_term ltk))

(** An ephemeral scalar generated BY A NAMED ROLE: a `Rand` at a trace position
    carrying the DH usage AND that role's compromise-sensitive label.  The label
    is what makes the derived session key's secrecy conditional on exactly the two
    roles' compromise, so the owning role is part of the fact. *)
let scalar_recorded_for (who:endpoint_id) (tr:TB.trace) (s:BT.bytes) : prop =
  exists (t:nat). s == eph_term t /\
    TB.entry_at tr t (T.RandGen eph_usage (eph_label who) eph_len)

(** The role-agnostic version, used wherever only "this is a generated ephemeral"
    matters (e.g. publishability of `dh_pk`, which holds for any label). *)
let scalar_recorded (tr:TB.trace) (s:BT.bytes) : prop =
  scalar_recorded_for Init tr s \/ scalar_recorded_for Resp tr s

let lemma_scalar_recorded_weaken (who:endpoint_id) (tr:TB.trace) (s:BT.bytes)
  : Lemma (requires scalar_recorded_for who tr s) (ensures scalar_recorded tr s)
= ()

(** The concrete and symbolic RNG registries are parallel.  Every symbolic
    representative is exactly the secret Rand at its recorded generation
    position; the concrete registry's `system_rng_wf` supplies no-reuse. *)
let rng_entry_coherent (d:rng_draw) (rs:rng_shadow) (tr:TB.trace) : prop =
  rs.rs_owner == d.rd_owner /\
  rs.rs_term == eph_term rs.rs_pos /\
  TB.entry_at tr rs.rs_pos (T.RandGen eph_usage (eph_label rs.rs_owner) eph_len)

let rec rng_coherent (draws:list rng_draw) (sh:list rng_shadow) (tr:TB.trace)
  : Tot prop (decreases draws) =
  match draws, sh with
  | [], [] -> True
  | d :: dt, rs :: rt ->
    rng_entry_coherent d rs tr /\ rng_coherent dt rt tr
  | _, _ -> False

let rec rng_binding
  (draws:list rng_draw) (sh:list rng_shadow)
  (owner:endpoint_id) (x:dh_scalar) (s:BT.bytes)
  : Tot prop (decreases draws) =
  match draws, sh with
  | d :: dt, rs :: rt ->
    (d.rd_owner == owner /\ d.rd_scalar == x /\
     rs.rs_owner == owner /\ rs.rs_term == s) \/
    rng_binding dt rt owner x s
  | _, _ -> False

let rng_option_binding
  (draws:list rng_draw) (sh:list rng_shadow) (owner:endpoint_id)
  (cx:option dh_scalar) (ss:option BT.bytes) : prop =
  match cx, ss with
  | None, None -> True
  | Some x, Some s -> rng_binding draws sh owner x s
  | _, _ -> False

(** Heterogeneous, canonical representation of the initiator's concrete fields by
    its symbolic shadow, exhaustive over the initiator phases.  The concrete
    integer scalar and the symbolic `Rand` live in different types and are NEVER
    byte-equated; the derived key is the CURRENT symbolic scalar combined with the
    symbolic peer share the initiator actually received. *)
let init_repr (c:endpoint_state) (sh:endpoint_shadow) : prop =
  match c.ep_phase with
  | Init_Start ->
    c.ep_scalar == None /\ c.ep_my_share == None /\ c.ep_peer_share == None /\ c.ep_key == None /\
    sh.sh_scalar == None /\ sh.sh_peer_share == None /\ sh.sh_key == None
  | Init_Wait2 ->
    (match c.ep_scalar, sh.sh_scalar with
     | Some x, Some _s ->
       c.ep_my_share == Some (Cr.dh_exp x) /\ c.ep_peer_share == None /\ c.ep_key == None /\
       sh.sh_pending == None /\ sh.sh_peer_share == None /\ sh.sh_key == None
     | _ -> False)
  | Init_Done ->
    (match c.ep_scalar, c.ep_peer_share, sh.sh_scalar, sh.sh_peer_share, sh.sh_key with
     | Some x, Some gy, Some s, Some psh, Some k ->
       c.ep_my_share == Some (Cr.dh_exp x) /\
       c.ep_key == Some (Cr.dh_agree x gy) /\
       sh.sh_pending == None /\
       k == secret_term s psh
     | _ -> False)
  | _ -> False

let resp_repr (c:endpoint_state) (sh:endpoint_shadow) : prop =
  match c.ep_phase with
  | Resp_Start ->
    c.ep_peer == None /\ c.ep_scalar == None /\ c.ep_my_share == None /\
    c.ep_peer_share == None /\ c.ep_key == None /\
    sh.sh_scalar == None /\ sh.sh_peer_share == None /\ sh.sh_key == None
  | Resp_Wait3 ->
    (match c.ep_scalar, c.ep_peer_share, sh.sh_scalar, sh.sh_peer_share, sh.sh_key with
     | Some y, Some gx, Some s, Some psh, Some k ->
       c.ep_my_share == Some (Cr.dh_exp y) /\
       c.ep_key == Some (Cr.dh_agree y gx) /\
       sh.sh_pending == None /\
       k == secret_term s psh
     | _ -> False)
  | Resp_Done ->
    (match c.ep_scalar, c.ep_peer_share, sh.sh_scalar, sh.sh_peer_share, sh.sh_key with
     | Some y, Some gx, Some s, Some psh, Some k ->
       c.ep_my_share == Some (Cr.dh_exp y) /\
       c.ep_key == Some (Cr.dh_agree y gx) /\
       sh.sh_pending == None /\
       k == secret_term s psh
     | _ -> False)
  | _ -> False

(** ── Focused endpoint-representation transfer lemmas ─────────────────────────

    `init_repr` / `resp_repr` are exhaustive five-way matches; re-establishing one
    inside a per-step lift proof (whose context already carries `wf p0`, the
    concrete `system_step` and the whole `sym_extend` computation) is exactly the
    kind of goal that makes a query expensive.  These two lemmas do it ONCE, in a
    tiny context that mentions only the two endpoint states and the two shadows,
    so each per-step proof only has to instantiate them. *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(** The initiator completing on message 2: it keeps its scalar and own share,
    records the peer share it received and the derived key, and refreshes its
    stored-state pointer. *)
let init_repr_finish
  (c0:endpoint_state) (sh0:endpoint_shadow)
  (x:dh_scalar) (gy:dh_share) (scalar peer_share:BT.bytes) (pos:nat)
  : Lemma
    (requires
      init_repr c0 sh0 /\
      c0.ep_phase == Init_Wait2 /\
      c0.ep_scalar == Some x /\
      sh0.sh_scalar == Some scalar)
    (ensures
      init_repr ({ c0 with ep_phase = Init_Done; ep_peer_share = Some gy;
                           ep_key = Some (Cr.dh_agree x gy) })
                ({ sh0 with sh_peer_share = Some peer_share;
                            sh_key = Some (secret_term scalar peer_share);
                            sh_state_pos = pos }))
= ()

(** The responder answering message 1: it adopts the scalar it had pending, the
    peer share it received and the derived key, and refreshes its pointer. *)
let resp_repr_respond
  (c0 c1:endpoint_state) (sh0:endpoint_shadow)
  (y:dh_scalar) (gx:dh_share) (a:principal) (scalar peer_share:BT.bytes) (pos:nat)
  : Lemma
    (requires
      c1 == { c0 with ep_phase = Resp_Wait3; ep_peer = Some a;
                      ep_scalar = Some y; ep_my_share = Some (Cr.dh_exp y);
                      ep_peer_share = Some gx; ep_key = Some (Cr.dh_agree y gx) })
    (ensures
      resp_repr c1 ({ sh0 with sh_pending = None; sh_scalar = Some scalar;
                               sh_peer_share = Some peer_share;
                               sh_key = Some (secret_term scalar peer_share);
                               sh_state_pos = pos }))
= ()

#pop-options

(** Whether a symbolic message has the same shape (tag) as a concrete one.  This
    is the OLD, tag-only notion of per-packet coherence.  It is ORIGIN-BLIND: it
    holds for an all-literal (attacker-injection–shaped) `SMsg2` paired with an
    honest-origin `Msg2` just as readily as for the responder's own structured
    send (see `lemma_tag_match_origin_blind`).  It is retained ONLY to exhibit
    that gap; `net_coherent` no longer uses it. *)
let smsg_tag_matches (m:dh_message) (sm:sym_msg) : prop =
  match m, sm with
  | Msg1 _ _,   SMsg1 _ _   -> True
  | Msg2 _ _ _, SMsg2 _ _ _ -> True
  | Msg3 _,     SMsg3 _     -> True
  | _, _ -> False

(** ── Origin-sensitive symbolic provenance of one packet ──────────────────────

    The structural provenance a single packet's symbolic shadow MUST carry, keyed
    on the ORIGIN the concrete packet already records (`pk_origin`).  This is what
    upgrades coherence from mere tag-agreement to origin-specific faithfulness:

      * an HONEST `Sent` packet's shadow is STRUCTURALLY EXACT for the sender's
        concrete send — the identity field is the sender's `term_of_principal`,
        every DH share is a genuine `share_term` (a `DhPub`) of a trace-recorded
        ephemeral, and every signature is a genuine `sig_term` (a `Sign`).  NONE of
        these honest fields is a public literal, so the term on the wire is exactly
        the structured message the sender generated, and a later delivery (which
        reuses that same term) can NEVER reclassify an honest share/signature as a
        literal;

      * an `Injected` packet's shadow is EXACTLY the all-literal `inject_smsg` of
        its own concrete message — sound Dolev-Yao traffic that asserts no
        cryptographic origin and is DY-publishable (discharged in
        DH.Sample.Symbolic.Provenance).

    A `Sent Init` packet is a Msg1 or a Msg3; a `Sent Resp` packet is a Msg2; every
    other (origin, message, shadow) combination is excluded (`False`) because it
    never arises from an honest send.  So `wf` can neither mislabel a packet's
    provenance nor admit a literal in place of an honest structured field.

    It is `opaque_to_smt`: the heavy three-way match must not unfold into every
    context that mentions `wf` (which would bloat unrelated per-step queries).  The
    handful of lemmas that reason about its internal structure `reveal` it locally. *)
let auth_nonce_pos (send_pos:nat) : nat =
  if send_pos = 0 then 0 else send_pos - 1

let lemma_auth_nonce_pos_succ (n:nat)
  : Lemma (ensures auth_nonce_pos (n + 1) == n)
= ()

[@@"opaque_to_smt"]
let smsg_provenance
  (init_ltk resp_ltk:BT.bytes) (pk:packet) (ne:net_entry) (tr:TB.trace) : prop =
  match pk.pk_origin, pk.pk_msg, ne.ne_smsg, ne.ne_auth with
  | Injected, _, sm, NoAuth ->
    sm == inject_smsg pk.pk_msg
  | Sent Init, Msg1 a _, SMsg1 a_s gxs, NoAuth ->
    a_s == term_of_principal a /\
    (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded_for Init tr s)
  | Sent Resp, Msg2 b _ _, SMsg2 b_s gys sgs, RespAuth partner peer_share ->
    b_s == term_of_principal b /\
    (exists (s:BT.bytes). gys == share_term s /\ scalar_recorded_for Resp tr s) /\
    sgs == sig_term resp_ltk (signonce_term (auth_nonce_pos ne.ne_pos))
             (transcript_term partner peer_share gys)
  | Sent Init, Msg3 _, SMsg3 sgs, InitAuth partner my_share peer_share ->
    sgs == sig_term init_ltk (signonce_term (auth_nonce_pos ne.ne_pos))
             (transcript_term partner my_share peer_share)
  | _, _, _, _ -> False

(** Per-packet network coherence: a packet's structured shadow is a `MsgSent` on
    the shared trace at its recorded position AND carries the origin-specific
    provenance above.  (`smsg_provenance` already fixes the shadow's tag, so
    tag-agreement is subsumed — see `lemma_net_entry_coherent_tag`.) *)
let net_entry_coherent
  (init_ltk resp_ltk:BT.bytes) (pk:packet) (ne:net_entry) (tr:TB.trace) : prop =
  ne.ne_pos < TB.trace_length tr /\
  TB.entry_at tr ne.ne_pos (T.MsgSent (flatten ne.ne_smsg)) /\
  smsg_provenance init_ltk resp_ltk pk ne tr

(** Whole-network coherence: parallel length, and every packet's shadow is
    origin-coherent.  Stated as a bounded `forall` over indices (rather than a
    recursive `prop`), so it instantiates and re-establishes robustly under the
    SMT solver.

    It is `opaque_to_smt` for the SAME reason as `smsg_provenance`: `net_coherent`
    is a conjunct of `wf`, which appears (as `wf p0` / `wf p1`) in every per-step
    lift query; if its `forall` unfolded there it would bloat unrelated split
    sub-goals.  The list lemmas below `reveal` it locally. *)
[@@"opaque_to_smt"]
let net_coherent
  (net:list packet) (sh:list net_entry) (tr:TB.trace)
  (init_ltk resp_ltk:BT.bytes) : prop =
  L.length net == L.length sh /\
  (forall (i:nat). i < L.length net ==>
    net_entry_coherent init_ltk resp_ltk (L.index net i) (L.index sh i) tr)

let key_state_coherent (p:product_state) : prop =
  let c = p.ps_sys in
  ltk_coherent_at Init (term_of_principal c.sys_init.ep_me)
                  p.ps_trace p.ps_init.sh_ltk (role_ltk_pos Init) /\
  ltk_coherent_at Resp (term_of_principal c.sys_resp.ep_me)
                  p.ps_trace p.ps_resp.sh_ltk (role_ltk_pos Resp)

(** ── The CURRENT-STATE pointer coherence ────────────────────────────────────

    A role's recorded `sh_state_pos` is a real position on the shared trace, and
    the entry there is a `SetState` of THAT role holding EXACTLY that role's
    CURRENT snapshot — its long-term key together with whatever pending draw,
    ephemeral scalar, received peer share and session key it holds right now.

    This is what makes `ActCorrupt` meaningful and honest: corrupting the role
    hands the attacker precisely this material, and (because the product refreshes
    the pointer after every state-changing action) precisely the material the role
    holds AT THE TIME OF THE COMPROMISE — never a stale, weaker snapshot. *)
let state_pos_coherent (who:endpoint_id) (sh:endpoint_shadow) (tr:TB.trace) : prop =
  sh.sh_state_pos < TB.trace_length tr /\
  TB.entry_at tr sh.sh_state_pos
    (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh))

let state_state_coherent (p:product_state) : prop =
  state_pos_coherent Init p.ps_init p.ps_trace /\
  state_pos_coherent Resp p.ps_resp p.ps_trace

let rng_state_coherent (p:product_state) : prop =
  let c = p.ps_sys in
  system_rng_wf c /\
  rng_coherent c.sys_rng p.ps_rng p.ps_trace /\
  rng_option_binding c.sys_rng p.ps_rng Init
    c.sys_init_pending p.ps_init.sh_pending /\
  rng_option_binding c.sys_rng p.ps_rng Resp
    c.sys_resp_pending p.ps_resp.sh_pending /\
  rng_option_binding c.sys_rng p.ps_rng Init
    c.sys_init.ep_scalar p.ps_init.sh_scalar /\
  rng_option_binding c.sys_rng p.ps_rng Resp
    c.sys_resp.ep_scalar p.ps_resp.sh_scalar /\
  (match p.ps_init.sh_pending with None -> True | Some s -> scalar_recorded_for Init p.ps_trace s) /\
  (match p.ps_resp.sh_pending with None -> True | Some s -> scalar_recorded_for Resp p.ps_trace s) /\
  (match p.ps_init.sh_scalar with None -> True | Some s -> scalar_recorded_for Init p.ps_trace s) /\
  (match p.ps_resp.sh_scalar with None -> True | Some s -> scalar_recorded_for Resp p.ps_trace s)

let endpoint_state_coherent (p:product_state) : prop =
  let c = p.ps_sys in
  init_repr c.sys_init p.ps_init /\
  resp_repr c.sys_resp p.ps_resp

let network_state_coherent (p:product_state) : prop =
  let c = p.ps_sys in
  net_coherent c.sys_net p.ps_net p.ps_trace p.ps_init.sh_ltk p.ps_resp.sh_ltk

let wf (p:product_state) : prop =
  key_state_coherent p /\
  rng_state_coherent p /\
  endpoint_state_coherent p /\
  network_state_coherent p /\
  state_state_coherent p

(** ── Trace-growth persistence of the coherence components ────────────────────

    As the shared trace grows, an established long-term-key coherence and an
    established ephemeral recording persist (their `RandGen` / `Event` entries
    stay on the trace). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let ltk_coherent_grows (who:endpoint_id) (me_t:BT.bytes) (tr tr':TB.trace) (ltk:BT.bytes) (pos:nat)
  : Lemma (requires ltk_coherent_at who me_t tr ltk pos /\ tr `TB.grows` tr')
          (ensures ltk_coherent_at who me_t tr' ltk pos)
= TB.entry_at_grows tr tr' pos (T.RandGen ltk_usage (ltk_label who) ltk_len);
  TB.event_triggered_grows tr tr' (role_dy_principal who) tag_keygen
    (keygen_content me_t (vkey_term ltk))

let scalar_recorded_for_grows (who:endpoint_id) (tr tr':TB.trace) (s:BT.bytes)
  : Lemma (requires scalar_recorded_for who tr s /\ tr `TB.grows` tr')
          (ensures scalar_recorded_for who tr' s)
= eliminate exists (t:nat). s == eph_term t /\
    TB.entry_at tr t (T.RandGen eph_usage (eph_label who) eph_len)
  returns scalar_recorded_for who tr' s
  with _.
    TB.entry_at_grows tr tr' t (T.RandGen eph_usage (eph_label who) eph_len)

let scalar_recorded_grows (tr tr':TB.trace) (s:BT.bytes)
  : Lemma (requires scalar_recorded tr s /\ tr `TB.grows` tr')
          (ensures scalar_recorded tr' s)
= eliminate scalar_recorded_for Init tr s \/ scalar_recorded_for Resp tr s
  returns scalar_recorded tr' s
  with _. scalar_recorded_for_grows Init tr tr' s
  and  _. scalar_recorded_for_grows Resp tr tr' s

let rng_entry_coherent_grows (d:rng_draw) (rs:rng_shadow) (tr tr':TB.trace)
  : Lemma
    (requires rng_entry_coherent d rs tr /\ tr `TB.grows` tr')
    (ensures rng_entry_coherent d rs tr')
= TB.entry_at_grows tr tr' rs.rs_pos
    (T.RandGen eph_usage (eph_label rs.rs_owner) eph_len)

let rec rng_coherent_grows
  (draws:list rng_draw) (sh:list rng_shadow) (tr tr':TB.trace)
  : Lemma
    (requires rng_coherent draws sh tr /\ tr `TB.grows` tr')
    (ensures rng_coherent draws sh tr')
    (decreases draws)
= match draws, sh with
  | d :: dt, rs :: rt ->
    rng_entry_coherent_grows d rs tr tr';
    rng_coherent_grows dt rt tr tr'
  | _, _ -> ()

let rng_coherent_cons
  (draws:list rng_draw) (sh:list rng_shadow) (tr tr':TB.trace)
  (owner:endpoint_id) (x:dh_scalar) (s:BT.bytes) (pos:nat)
  : Lemma
    (requires
      rng_coherent draws sh tr /\ tr `TB.grows` tr' /\
      s == eph_term pos /\
      TB.entry_at tr' pos (T.RandGen eph_usage (eph_label owner) eph_len))
    (ensures
      rng_coherent
        ({ rd_owner = owner; rd_scalar = x } :: draws)
        ({ rs_owner = owner; rs_term = s; rs_pos = pos } :: sh)
        tr')
= rng_coherent_grows draws sh tr tr'

(** Trace-growth preservation when a protocol step changes only non-RNG
    endpoint fields (phase, peer share, key, etc.). *)
let rng_fields_stable (p0 p1:product_state) : prop =
  p1.ps_sys.sys_rng == p0.ps_sys.sys_rng /\
  p1.ps_sys.sys_init_pending == p0.ps_sys.sys_init_pending /\
  p1.ps_sys.sys_resp_pending == p0.ps_sys.sys_resp_pending /\
  p1.ps_sys.sys_init.ep_scalar == p0.ps_sys.sys_init.ep_scalar /\
  p1.ps_sys.sys_resp.ep_scalar == p0.ps_sys.sys_resp.ep_scalar /\
  p1.ps_rng == p0.ps_rng /\
  p1.ps_init.sh_pending == p0.ps_init.sh_pending /\
  p1.ps_resp.sh_pending == p0.ps_resp.sh_pending /\
  p1.ps_init.sh_scalar == p0.ps_init.sh_scalar /\
  p1.ps_resp.sh_scalar == p0.ps_resp.sh_scalar

#push-options "--split_queries always"
let rng_state_coherent_grows_to (p0 p1:product_state)
  : Lemma
    (requires
      rng_state_coherent p0 /\
      system_rng_wf p1.ps_sys /\
      rng_fields_stable p0 p1 /\
      p0.ps_trace `TB.grows` p1.ps_trace)
    (ensures rng_state_coherent p1)
= rng_coherent_grows p0.ps_sys.sys_rng p0.ps_rng p0.ps_trace p1.ps_trace;
  (match p0.ps_init.sh_pending with
   | Some s -> scalar_recorded_for_grows Init p0.ps_trace p1.ps_trace s
   | None -> ());
  (match p0.ps_resp.sh_pending with
   | Some s -> scalar_recorded_for_grows Resp p0.ps_trace p1.ps_trace s
   | None -> ());
  (match p0.ps_init.sh_scalar with
   | Some s -> scalar_recorded_for_grows Init p0.ps_trace p1.ps_trace s
   | None -> ());
  (match p0.ps_resp.sh_scalar with
   | Some s -> scalar_recorded_for_grows Resp p0.ps_trace p1.ps_trace s
   | None -> ())
#pop-options

#pop-options

(** ── Network-coherence list lemmas ──────────────────────────────────────────*)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(** Indexing helpers for `append` (proved by a short induction on the prefix). *)

(** `append_length` in the library is SMT-triggered on the `@` operator; we expose
    the same fact on `L.append` so the index refinements below discharge. *)
let append_length_l (#a:Type) (l1 l2:list a)
  : Lemma (ensures L.length (L.append l1 l2) == L.length l1 + L.length l2)
          [SMTPat (L.length (L.append l1 l2))]
= L.append_length l1 l2

let rec index_app_left (#a:Type) (l1 l2:list a) (i:nat)
  : Lemma (requires i < L.length l1)
          (ensures L.index (L.append l1 l2) i == L.index l1 i)
          (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl -> if i = 0 then () else index_app_left tl l2 (i - 1)

let rec index_app_right (#a:Type) (l1 l2:list a) (i:nat)
  : Lemma (requires L.length l1 <= i /\ i < L.length l1 + L.length l2)
          (ensures L.index (L.append l1 l2) i == L.index l2 (i - L.length l1))
          (decreases l1)
= match l1 with
  | [] -> ()
  | hd :: tl -> index_app_right tl l2 (i - 1)

let net_coherent_length (net:list packet) (sh:list net_entry) (tr:TB.trace)
                        (init_ltk resp_ltk:BT.bytes)
  : Lemma (requires net_coherent net sh tr init_ltk resp_ltk)
          (ensures L.length net == L.length sh)
= reveal_opaque (`%net_coherent) net_coherent

let net_coherent_index (net:list packet) (sh:list net_entry) (tr:TB.trace)
                       (init_ltk resp_ltk:BT.bytes) (i:nat)
  : Lemma (requires net_coherent net sh tr init_ltk resp_ltk /\ i < L.length net)
          (ensures (
            L.length net == L.length sh /\
            net_entry_coherent init_ltk resp_ltk
              (L.index net i) (L.index sh i) tr))
= reveal_opaque (`%net_coherent) net_coherent

(** Persistence of the (trace-dependent) share-recording witness under `grows`. *)
let share_recorded_grows (who:endpoint_id) (gxs:BT.bytes) (tr tr':TB.trace)
  : Lemma
    (requires (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded_for who tr s) /\
              tr `TB.grows` tr')
    (ensures (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded_for who tr' s))
= eliminate exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded_for who tr s
  returns (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded_for who tr' s)
  with _.
    (scalar_recorded_for_grows who tr tr' s;
     introduce exists (s':BT.bytes). gxs == share_term s' /\ scalar_recorded_for who tr' s'
     with s and ())

(** Per-packet origin coherence persists as the shared trace grows: the `MsgSent`
    entry and any share-recording witness carry over; the identity / signature
    structure is trace-independent. *)
let net_entry_coherent_grows
  (init_ltk resp_ltk:BT.bytes) (pk:packet) (ne:net_entry) (tr tr':TB.trace)
  : Lemma
    (requires net_entry_coherent init_ltk resp_ltk pk ne tr /\ tr `TB.grows` tr')
    (ensures net_entry_coherent init_ltk resp_ltk pk ne tr')
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  TB.trace_length_grows tr tr';
  TB.entry_at_grows tr tr' ne.ne_pos (T.MsgSent (flatten ne.ne_smsg));
  match pk.pk_origin, pk.pk_msg, ne.ne_smsg, ne.ne_auth with
  | Sent Init, Msg1 _ _, SMsg1 _ gxs, NoAuth -> share_recorded_grows Init gxs tr tr'
  | Sent Resp, Msg2 _ _ _, SMsg2 _ gys _, RespAuth _ _ ->
    share_recorded_grows Resp gys tr tr'
  | _, _, _, _ -> ()

let net_coherent_grows
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes)
  : Lemma
    (requires net_coherent net sh tr init_ltk resp_ltk /\ tr `TB.grows` tr')
    (ensures net_coherent net sh tr' init_ltk resp_ltk)
= net_coherent_length net sh tr init_ltk resp_ltk;
  introduce forall (i:nat). i < L.length net ==>
    net_entry_coherent init_ltk resp_ltk (L.index net i) (L.index sh i) tr'
  with introduce _ ==> _
  with _.
    (net_coherent_index net sh tr init_ltk resp_ltk i;
     net_entry_coherent_grows init_ltk resp_ltk
       (L.index net i) (L.index sh i) tr tr');
  reveal_opaque (`%net_coherent) net_coherent

#push-options "--split_queries always"
let net_coherent_append
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes)
  (pkt:packet) (ne:net_entry)
  : Lemma
      (requires
        net_coherent net sh tr init_ltk resp_ltk /\ tr `TB.grows` tr' /\
        net_entry_coherent init_ltk resp_ltk pkt ne tr')
      (ensures
        net_coherent (L.append net [pkt]) (L.append sh [ne]) tr'
                     init_ltk resp_ltk)
= append_length_l net [pkt];
  append_length_l sh [ne];
  net_coherent_length net sh tr init_ltk resp_ltk;
  net_coherent_grows net sh tr tr' init_ltk resp_ltk;
  assert (L.length (L.append net [pkt]) == L.length (L.append sh [ne]));
  introduce forall (i:nat). i < L.length (L.append net [pkt]) ==>
    net_entry_coherent init_ltk resp_ltk
      (L.index (L.append net [pkt]) i) (L.index (L.append sh [ne]) i) tr'
  with introduce _ ==> _
  with _.
    if i < L.length net then begin
      index_app_left net [pkt] i;
      index_app_left sh [ne] i;
      net_coherent_index net sh tr' init_ltk resp_ltk i
    end else begin
      index_app_right net [pkt] i;
      index_app_right sh [ne] i
    end;
  reveal_opaque (`%net_coherent) net_coherent
#pop-options

(** ── Origin-coherence "constructors" for the honest sends and injection ──────

    Each establishes `net_entry_coherent` for one concrete send shape, providing
    the structural witness (a recorded scalar for a share, the signing key / nonce
    / transcript for a signature) so the per-step lift proofs stay small. *)

let coherent_sent_msg1
  (init_ltk resp_ltk:BT.bytes)
  (a:principal) (gx:dh_share) (s:BT.bytes) (pos:nat) (tr:TB.trace)
  : Lemma
      (requires
        scalar_recorded_for Init tr s /\ pos < TB.trace_length tr /\
        TB.entry_at tr pos (T.MsgSent (flatten (SMsg1 (term_of_principal a) (share_term s)))))
      (ensures net_entry_coherent init_ltk resp_ltk
                 ({ pk_msg = Msg1 a gx; pk_origin = Sent Init })
                 ({ ne_smsg = SMsg1 (term_of_principal a) (share_term s);
                   ne_pos = pos; ne_auth = NoAuth }) tr)
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  introduce exists (s':BT.bytes). share_term s == share_term s' /\ scalar_recorded_for Init tr s'
  with s and ()

let coherent_sent_msg2
  (init_ltk resp_ltk:BT.bytes)
  (b:principal) (gy:dh_share) (sigB:signature)
  (s partner peer_share:BT.bytes) (pos:nat) (tr:TB.trace)
  : Lemma
      (requires
        scalar_recorded_for Resp tr s /\ pos < TB.trace_length tr /\
        TB.entry_at tr pos
          (T.MsgSent (flatten (SMsg2 (term_of_principal b) (share_term s)
            (sig_term resp_ltk (signonce_term (auth_nonce_pos pos))
              (transcript_term partner peer_share (share_term s)))))))
      (ensures net_entry_coherent init_ltk resp_ltk
                 ({ pk_msg = Msg2 b gy sigB; pk_origin = Sent Resp })
                 ({ ne_smsg = SMsg2 (term_of_principal b) (share_term s)
                     (sig_term resp_ltk (signonce_term (auth_nonce_pos pos))
                       (transcript_term partner peer_share (share_term s)));
                   ne_pos = pos;
                   ne_auth = RespAuth partner peer_share }) tr)
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  introduce exists (s':BT.bytes). share_term s == share_term s' /\ scalar_recorded_for Resp tr s'
  with s and ()

let coherent_sent_msg3
  (init_ltk resp_ltk:BT.bytes) (sigA:signature)
  (partner my_share peer_share:BT.bytes) (pos:nat) (tr:TB.trace)
  : Lemma
      (requires
        pos < TB.trace_length tr /\
        TB.entry_at tr pos
          (T.MsgSent (flatten (SMsg3
            (sig_term init_ltk (signonce_term (auth_nonce_pos pos))
              (transcript_term partner my_share peer_share))))))
      (ensures net_entry_coherent init_ltk resp_ltk
                 ({ pk_msg = Msg3 sigA; pk_origin = Sent Init })
                 ({ ne_smsg = SMsg3
                    (sig_term init_ltk (signonce_term (auth_nonce_pos pos))
                      (transcript_term partner my_share peer_share));
                   ne_pos = pos;
                   ne_auth = InitAuth partner my_share peer_share }) tr)
= reveal_opaque (`%smsg_provenance) smsg_provenance

let coherent_injected
  (init_ltk resp_ltk:BT.bytes) (m:dh_message) (pos:nat) (tr:TB.trace)
  : Lemma
      (requires
        pos < TB.trace_length tr /\
        TB.entry_at tr pos (T.MsgSent (flatten (inject_smsg m))))
      (ensures net_entry_coherent init_ltk resp_ltk
                 ({ pk_msg = m; pk_origin = Injected })
                 ({ ne_smsg = inject_smsg m; ne_pos = pos; ne_auth = NoAuth }) tr)
= reveal_opaque (`%smsg_provenance) smsg_provenance

(** ── Fused "append one packet" coherence steps ──────────────────────────────

    Each fuses the per-shape origin constructor above with `net_coherent_append`,
    so a per-step lift caller adds exactly ONE fact — the resulting whole-network
    coherence — to its (split-query) context, rather than also carrying the
    intermediate per-entry coherence.  This keeps every per-step query small. *)

let net_coherent_append_sent_msg1
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes)
  (a:principal) (gx:dh_share) (s:BT.bytes) (pos:nat)
  : Lemma
      (requires
        net_coherent net sh tr init_ltk resp_ltk /\ tr `TB.grows` tr' /\
        scalar_recorded_for Init tr' s /\ pos < TB.trace_length tr' /\
        TB.entry_at tr' pos (T.MsgSent (flatten (SMsg1 (term_of_principal a) (share_term s)))))
      (ensures
        net_coherent
          (L.append net [ { pk_msg = Msg1 a gx; pk_origin = Sent Init } ])
          (L.append sh  [ { ne_smsg = SMsg1 (term_of_principal a) (share_term s);
                            ne_pos = pos; ne_auth = NoAuth } ])
          tr' init_ltk resp_ltk)
= coherent_sent_msg1 init_ltk resp_ltk a gx s pos tr';
  net_coherent_append net sh tr tr' init_ltk resp_ltk
    ({ pk_msg = Msg1 a gx; pk_origin = Sent Init })
    ({ ne_smsg = SMsg1 (term_of_principal a) (share_term s);
       ne_pos = pos; ne_auth = NoAuth })

let net_coherent_append_sent_msg2
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes)
  (b:principal) (gy:dh_share) (sigB:signature)
  (s partner peer_share:BT.bytes) (pos:nat)
  : Lemma
      (requires
        net_coherent net sh tr init_ltk resp_ltk /\ tr `TB.grows` tr' /\
        scalar_recorded_for Resp tr' s /\ pos < TB.trace_length tr' /\
        TB.entry_at tr' pos
          (T.MsgSent (flatten (SMsg2 (term_of_principal b) (share_term s)
            (sig_term resp_ltk (signonce_term (auth_nonce_pos pos))
              (transcript_term partner peer_share (share_term s)))))))
      (ensures
        net_coherent
          (L.append net [ { pk_msg = Msg2 b gy sigB; pk_origin = Sent Resp } ])
          (L.append sh  [ { ne_smsg = SMsg2 (term_of_principal b) (share_term s)
              (sig_term resp_ltk (signonce_term (auth_nonce_pos pos))
                (transcript_term partner peer_share (share_term s)));
                            ne_pos = pos;
                            ne_auth = RespAuth partner peer_share } ])
          tr' init_ltk resp_ltk)
= coherent_sent_msg2 init_ltk resp_ltk b gy sigB s partner peer_share pos tr';
  net_coherent_append net sh tr tr' init_ltk resp_ltk
    ({ pk_msg = Msg2 b gy sigB; pk_origin = Sent Resp })
    ({ ne_smsg = SMsg2 (term_of_principal b) (share_term s)
        (sig_term resp_ltk (signonce_term (auth_nonce_pos pos))
          (transcript_term partner peer_share (share_term s)));
       ne_pos = pos;
       ne_auth = RespAuth partner peer_share })

let net_coherent_append_sent_msg3
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes)
  (sigA:signature) (partner my_share peer_share:BT.bytes) (pos:nat)
  : Lemma
      (requires
        net_coherent net sh tr init_ltk resp_ltk /\ tr `TB.grows` tr' /\
        pos < TB.trace_length tr' /\
        TB.entry_at tr' pos
          (T.MsgSent (flatten (SMsg3
            (sig_term init_ltk (signonce_term (auth_nonce_pos pos))
              (transcript_term partner my_share peer_share))))))
      (ensures
        net_coherent
          (L.append net [ { pk_msg = Msg3 sigA; pk_origin = Sent Init } ])
          (L.append sh  [ { ne_smsg = SMsg3
              (sig_term init_ltk (signonce_term (auth_nonce_pos pos))
                (transcript_term partner my_share peer_share));
                            ne_pos = pos;
                            ne_auth = InitAuth partner my_share peer_share } ])
          tr' init_ltk resp_ltk)
= coherent_sent_msg3 init_ltk resp_ltk sigA partner my_share peer_share pos tr';
  net_coherent_append net sh tr tr' init_ltk resp_ltk
    ({ pk_msg = Msg3 sigA; pk_origin = Sent Init })
    ({ ne_smsg = SMsg3
        (sig_term init_ltk (signonce_term (auth_nonce_pos pos))
          (transcript_term partner my_share peer_share));
       ne_pos = pos;
       ne_auth = InitAuth partner my_share peer_share })

let net_coherent_append_injected
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes) (m:dh_message) (pos:nat)
  : Lemma
      (requires
        net_coherent net sh tr init_ltk resp_ltk /\ tr `TB.grows` tr' /\
        pos < TB.trace_length tr' /\
        TB.entry_at tr' pos (T.MsgSent (flatten (inject_smsg m))))
      (ensures
        net_coherent
          (L.append net [ { pk_msg = m; pk_origin = Injected } ])
          (L.append sh  [ { ne_smsg = inject_smsg m; ne_pos = pos; ne_auth = NoAuth } ])
          tr' init_ltk resp_ltk)
= coherent_injected init_ltk resp_ltk m pos tr';
  net_coherent_append net sh tr tr' init_ltk resp_ltk
    ({ pk_msg = m; pk_origin = Injected })
    ({ ne_smsg = inject_smsg m; ne_pos = pos; ne_auth = NoAuth })

(** The strengthened per-packet coherence SUBSUMES the old tag-only notion: it
    implies the shadow's constructor matches the concrete message's.  So replacing
    `smsg_tag_matches` by `smsg_provenance` in `net_coherent` loses nothing the old
    definition provided — it only ADDS the origin-specific structure. *)
let lemma_net_entry_coherent_tag
  (init_ltk resp_ltk:BT.bytes) (pk:packet) (ne:net_entry) (tr:TB.trace)
  : Lemma (requires net_entry_coherent init_ltk resp_ltk pk ne tr)
          (ensures smsg_tag_matches pk.pk_msg ne.ne_smsg)
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  match pk.pk_origin, pk.pk_msg, ne.ne_smsg, ne.ne_auth with
  | Injected, Msg1 _ _, _, NoAuth -> ()
  | Injected, Msg2 _ _ _, _, NoAuth -> ()
  | Injected, Msg3 _, _, NoAuth -> ()
  | Sent Init, Msg1 _ _, SMsg1 _ _, NoAuth -> ()
  | Sent Resp, Msg2 _ _ _, SMsg2 _ _ _, RespAuth _ _ -> ()
  | Sent Init, Msg3 _, SMsg3 _, InitAuth _ _ _ -> ()
  | _, _, _, _ -> ()

(** ── The gap this strengthening closes, machine-checked ───────────────────────

    (1) The OLD tag-only coherence is ORIGIN-BLIND: an honest-origin `Msg2` packet
        tag-matches the ALL-LITERAL, attacker-injection–shaped `SMsg2`
        (`inject_smsg`).  So a `wf` state under the old `net_coherent` could pair a
        `{ pk_origin = Sent Resp; pk_msg = Msg2 … }` packet with a literal shadow —
        reclassifying an honest responder signature as a `Literal`. *)
let lemma_tag_match_origin_blind (b:principal) (gy:dh_share) (sigB:signature)
  : Lemma (ensures smsg_tag_matches (Msg2 b gy sigB) (inject_smsg (Msg2 b gy sigB)))
= ()

(** (2) The NEW origin-sensitive provenance REJECTS exactly that pairing: an
        honest `Sent Resp` `Msg2` cannot have the all-literal `inject_smsg` shadow,
        because that shadow's DH share is a `Literal` (never a `share_term`/`DhPub`)
        and its signature is a `Literal` (never a `sig_term`/`Sign`).  Hence no `wf`
        state can reclassify an honest responder send as literals — the concern's
        bad state is unreachable *by the invariant itself*, not merely by argument. *)

(** A public literal is never one of the honest structured builders (here: a DH
    share).  `Literal` and `DhPub` are distinct `bytes` constructors. *)
let literal_neq_share (blob:bytes) (s:BT.bytes)
  : Lemma (ensures term_of_blob blob =!= share_term s)
= normalize_term_spec (term_of_blob blob);
  reveal_opaque (`%B.dh_pk) B.dh_pk;
  assert (share_term s == BT.DhPub s)

let lemma_provenance_rejects_injected_honest_msg2
  (init_ltk resp_ltk:BT.bytes)
  (b:principal) (gy:dh_share) (sigB:signature) (tr:TB.trace)
  : Lemma (ensures ~(
      smsg_provenance init_ltk resp_ltk
        ({ pk_msg = Msg2 b gy sigB; pk_origin = Sent Resp })
        ({ ne_smsg = inject_smsg (Msg2 b gy sigB);
           ne_pos = 0; ne_auth = NoAuth }) tr))
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  assert (inject_smsg (Msg2 b gy sigB)
          == SMsg2 (term_of_principal b) (term_of_blob gy) (term_of_blob sigB));
  introduce forall (s:BT.bytes). term_of_blob gy =!= share_term s
  with literal_neq_share gy s

#pop-options

(** ── Initial well-formedness and non-vacuity ────────────────────────────────*)

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10"

let lemma_product_initial_wf (a b:principal)
  : Lemma (ensures wf (product_initial a b))
= reveal_opaque (`%net_coherent) net_coherent;
  reveal_opaque (`%shadow_snapshot) shadow_snapshot;
  lemma_role_principals_distinct ();
  let tr0 = TB.empty_trace in
  setup_structure Init (term_of_principal a) tr0;
  setup_facts Init (term_of_principal a) tr0;
  let (_, tr1) = setup_run Init (term_of_principal a) tr0 in
  setup_structure Resp (term_of_principal b) tr1;
  setup_facts Resp (term_of_principal b) tr1;
  let (_, tr2) = setup_run Resp (term_of_principal b) tr1 in
  TB.entry_at_grows tr1 tr2 (role_setup_state_pos Init)
    (T.SetState (role_dy_principal Init) (role_state_id Init)
      (snapshot_term (ltk_term (role_ltk_pos Init)) None None None None))

(** Non-vacuity of the supported profile: a well-formed product state exists. *)
let lemma_wf_inhabited (a b:principal)
  : Lemma (ensures (exists (p:product_state). wf p))
= lemma_product_initial_wf a b

#pop-options

(** ── Every product step only GROWS the shared trace ──────────────────────────

    Each `sym_extend` case appends entries to the one shared trace and never
    rewrites it — including the compromise case, which appends exactly one
    `Corrupt` entry.  Dispatch mirrors `sym_extend`; the per-segment `*_facts`
    lemmas each deliver the `grows` fact. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_product_step_grows
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_step p0 ev p1 out)
    (ensures p0.ps_trace `TB.grows` p1.ps_trace)
= let c0 = p0.ps_sys in
  let n = TB.trace_length p0.ps_trace in
  match ev with
  | SM.LocalEvent (ActRng owner x) ->
    (match owner with
     | Init ->
       (match p0.ps_init.sh_pending with
        | None ->
          rng_facts Init
            (shadow_snapshot ({ p0.ps_init with sh_pending = Some (eph_term n);
                                                sh_state_pos = n + 1 }))
            p0.ps_trace
        | Some _ -> ())
     | Resp ->
       (match p0.ps_resp.sh_pending with
        | None ->
          rng_facts Resp
            (shadow_snapshot ({ p0.ps_resp with sh_pending = Some (eph_term n);
                                                sh_state_pos = n + 1 }))
            p0.ps_trace
        | Some _ -> ()))
  | SM.LocalEvent ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       start_facts (term_of_principal c0.sys_init.ep_me)
                   (term_of_principal peer) scalar
                   (shadow_snapshot ({ p0.ps_init with sh_pending = None;
                                         sh_scalar = Some scalar;
                                         sh_state_pos = n + 2 }))
                   p0.ps_trace
     | _, _ -> ())
  | SM.LocalEvent (ActDeliver idx dst) ->
    if idx < L.length c0.sys_net && idx < L.length p0.ps_net then begin
      let ne0  = L.index p0.ps_net idx in
      let cmsg = (L.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg1 a gx ->
        (match p0.ps_resp.sh_pending with
         | Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
           respond_facts p0.ps_resp.sh_ltk
             (term_of_principal c0.sys_resp.ep_me) (term_of_principal a) peer_share scalar
             (shadow_snapshot ({ p0.ps_resp with sh_pending = None;
                                   sh_scalar = Some scalar;
                                   sh_peer_share = Some peer_share;
                                   sh_key = Some (secret_term scalar peer_share);
                                   sh_state_pos = n + 3 }))
             p0.ps_trace
         | None -> ())
      | Resp, Msg3 _ ->
        (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
         | Some a, Some key -> rfinish_facts (term_of_principal a) key p0.ps_trace
         | _ -> ())
      | Init, Msg2 b gy _ ->
        (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
         | Some _xc, Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
           ifinish_facts p0.ps_init.sh_ltk scalar
             (term_of_principal b) peer_share
             (shadow_snapshot ({ p0.ps_init with sh_peer_share = Some peer_share;
                                   sh_key = Some (secret_term scalar peer_share);
                                   sh_state_pos = n + 3 }))
             p0.ps_trace
         | _ -> ())
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (ActInject m) -> inject_facts (inject_smsg m) p0.ps_trace
  | SM.LocalEvent (ActCorrupt who) ->
    (match who with
     | Init -> corrupt_facts p0.ps_init.sh_state_pos p0.ps_trace
     | Resp -> corrupt_facts p0.ps_resp.sh_state_pos p0.ps_trace)
  | _ -> ()
#pop-options

(** ── The compromise step, spelled out ────────────────────────────────────────

    A compromise step appends EXACTLY one genuine DY* `Corrupt` entry, naming the
    target role's CURRENT state position, and changes no shadow, no network entry
    and no RNG entry.  Combined with `wf p0` (whose `state_state_coherent`
    conjunct pins that position to a `SetState` of that role holding EXACTLY the
    role's current snapshot), this is what makes the corruption real: the attacker
    obtains the role's live long-term key AND its live ephemeral / session
    material. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_corrupt_step_effect
  (p0:product_state) (who:endpoint_id) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\
      product_step p0 (SM.LocalEvent (ActCorrupt who)) p1 out)
    (ensures (
      let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
      p1.ps_init == p0.ps_init /\ p1.ps_resp == p0.ps_resp /\
      p1.ps_net == p0.ps_net /\ p1.ps_rng == p0.ps_rng /\
      p1.ps_trace == corrupt_trace sh.sh_state_pos p0.ps_trace /\
      p0.ps_trace `TB.grows` p1.ps_trace /\
      TB.entry_exists p1.ps_trace (T.Corrupt sh.sh_state_pos) /\
      TB.entry_at p1.ps_trace sh.sh_state_pos
        (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh)) /\
      TB.state_was_corrupt p1.ps_trace
        (role_dy_principal who) (role_state_id who) (shadow_snapshot sh)))
= let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
  corrupt_structure sh.sh_state_pos p0.ps_trace;
  corrupt_facts sh.sh_state_pos p0.ps_trace;
  let tr1 = corrupt_trace sh.sh_state_pos p0.ps_trace in
  TB.entry_at_grows p0.ps_trace tr1 sh.sh_state_pos
    (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh));
  introduce exists (time:nat).
      TB.entry_exists tr1 (T.Corrupt time) /\
      TB.entry_at tr1 time
        (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh))
  with sh.sh_state_pos and ()
#pop-options

(** ── Per-delivery STEP SHAPE lemmas ──────────────────────────────────────────

    Each delivery step can only fire from one endpoint phase, in which `wf`
    already pins which shadow fields are present.  Establishing that ONCE here (in
    a context with only `wf` and `system_step`) lets the many downstream
    invariant-preservation proofs match on the delivered message alone, instead of
    re-deriving the shadow's shape inside their own (much larger) queries. *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"

(** Delivering a Msg2 to the initiator: it must be waiting for it, holding both
    its concrete and symbolic scalar and nothing else yet. *)
let lemma_init_msg2_step_shape
  (p0:product_state) (idx:nat) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\
      product_step p0 (SM.LocalEvent (ActDeliver idx Init)) p1 out /\
      idx < L.length p0.ps_sys.sys_net /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures
      idx < L.length p0.ps_net /\
      p0.ps_sys.sys_init.ep_phase == Init_Wait2 /\
      Some? p0.ps_sys.sys_init.ep_scalar /\
      Some? p0.ps_sys.sys_init.ep_my_share /\
      Some? p0.ps_init.sh_scalar /\
      p0.ps_init.sh_pending == None /\
      p0.ps_init.sh_peer_share == None /\
      p0.ps_init.sh_key == None /\
      p1.ps_resp == p0.ps_resp /\
      p1.ps_rng == p0.ps_rng /\
      p1.ps_init.sh_ltk == p0.ps_init.sh_ltk /\
      p1.ps_init.sh_pending == None /\
      p1.ps_init.sh_scalar == p0.ps_init.sh_scalar)
= net_coherent_length p0.ps_sys.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk

(** The EXACT successor shape of that step, with every ingredient supplied by the
    caller as an explicit argument (so the caller never has to match a nested
    `let` in this lemma's conclusion, and this lemma — not the caller — pays for
    unfolding `sym_extend`). *)
let lemma_init_msg2_step_next
  (p0:product_state) (idx:nat) (p1:product_state) (out:sys_output)
  (b:principal) (gy:dh_share) (scalar peer_share:BT.bytes)
  : Lemma
    (requires
      wf p0 /\
      product_step p0 (SM.LocalEvent (ActDeliver idx Init)) p1 out /\
      idx < L.length p0.ps_sys.sys_net /\ idx < L.length p0.ps_net /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg /\
      Msg2?.responder (L.index p0.ps_sys.sys_net idx).pk_msg == b /\
      Msg2?.gy (L.index p0.ps_sys.sys_net idx).pk_msg == gy /\
      p0.ps_init.sh_scalar == Some scalar /\
      peer_share == (match (L.index p0.ps_net idx).ne_smsg with
                     | SMsg2 _ gys _ -> gys
                     | _ -> term_of_blob gy))
    (ensures (
      let n = TB.trace_length p0.ps_trace in
      let transcript =
        transcript_term (term_of_principal b) (share_term scalar) peer_share in
      p1.ps_init == { p0.ps_init with sh_peer_share = Some peer_share;
                        sh_key = Some (secret_term scalar peer_share);
                        sh_state_pos = n + 3 } /\
      p1.ps_net == L.append p0.ps_net
        [ { ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk (signonce_term (n + 1)) transcript);
            ne_pos  = n + 2;
            ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share } ]))
= ()

(** Delivering a Msg1 to the responder: it must be fresh, with a pending draw. *)
let lemma_resp_msg1_step_shape
  (p0:product_state) (idx:nat) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\
      product_step p0 (SM.LocalEvent (ActDeliver idx Resp)) p1 out /\
      idx < L.length p0.ps_sys.sys_net /\
      Msg1? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures
      idx < L.length p0.ps_net /\
      p0.ps_sys.sys_resp.ep_phase == Resp_Start /\
      Some? p0.ps_sys.sys_resp_pending /\
      Some? p0.ps_resp.sh_pending /\
      p0.ps_resp.sh_scalar == None /\
      p0.ps_resp.sh_peer_share == None /\
      p0.ps_resp.sh_key == None /\
      p1.ps_init == p0.ps_init /\
      p1.ps_rng == p0.ps_rng /\
      p1.ps_resp.sh_ltk == p0.ps_resp.sh_ltk /\
      p1.ps_resp.sh_pending == None /\
      p1.ps_resp.sh_scalar == p0.ps_resp.sh_pending /\
      p1.ps_sys.sys_resp.ep_phase == Resp_Wait3)
= net_coherent_length p0.ps_sys.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk

(** The EXACT successor shape of the responder's Msg1 step. *)
let lemma_resp_msg1_step_next
  (p0:product_state) (idx:nat) (p1:product_state) (out:sys_output)
  (a:principal) (gx:dh_share) (scalar peer_share:BT.bytes)
  : Lemma
    (requires
      wf p0 /\
      product_step p0 (SM.LocalEvent (ActDeliver idx Resp)) p1 out /\
      idx < L.length p0.ps_sys.sys_net /\ idx < L.length p0.ps_net /\
      Msg1? (L.index p0.ps_sys.sys_net idx).pk_msg /\
      Msg1?.initiator (L.index p0.ps_sys.sys_net idx).pk_msg == a /\
      Msg1?.gx (L.index p0.ps_sys.sys_net idx).pk_msg == gx /\
      p0.ps_resp.sh_pending == Some scalar /\
      peer_share == (match (L.index p0.ps_net idx).ne_smsg with
                     | SMsg1 _ gxs -> gxs
                     | _ -> term_of_blob gx))
    (ensures (
      let n = TB.trace_length p0.ps_trace in
      let transcript =
        transcript_term (term_of_principal a) peer_share (share_term scalar) in
      p1.ps_resp == { p0.ps_resp with sh_pending = None; sh_scalar = Some scalar;
                        sh_peer_share = Some peer_share;
                        sh_key = Some (secret_term scalar peer_share);
                        sh_state_pos = n + 3 } /\
      p1.ps_net == L.append p0.ps_net
        [ { ne_smsg = SMsg2 (term_of_principal p0.ps_sys.sys_resp.ep_me)
                        (share_term scalar)
                        (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
            ne_pos  = n + 2;
            ne_auth = RespAuth (term_of_principal a) peer_share } ]))
= ()

(** Delivering a Msg3 to the responder: it must have responded already, so it
    holds its scalar, the peer share it accepted and the derived key. *)
let lemma_resp_msg3_step_shape
  (p0:product_state) (idx:nat) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
      wf p0 /\
      product_step p0 (SM.LocalEvent (ActDeliver idx Resp)) p1 out /\
      idx < L.length p0.ps_sys.sys_net /\
      Msg3? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures
      idx < L.length p0.ps_net /\
      p0.ps_sys.sys_resp.ep_phase == Resp_Wait3 /\
      Some? p0.ps_sys.sys_resp.ep_peer /\
      Some? p0.ps_sys.sys_resp.ep_peer_share /\
      Some? p0.ps_sys.sys_resp.ep_my_share /\
      Some? p0.ps_resp.sh_scalar /\
      Some? p0.ps_resp.sh_peer_share /\
      Some? p0.ps_resp.sh_key /\
      p1.ps_sys.sys_resp.ep_phase == Resp_Done /\
      (* the responder's completion changes NO symbolic state at all *)
      p1.ps_init == p0.ps_init /\
      p1.ps_resp == p0.ps_resp /\
      p1.ps_net == p0.ps_net /\
      p1.ps_rng == p0.ps_rng)
= net_coherent_length p0.ps_sys.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk

#pop-options
