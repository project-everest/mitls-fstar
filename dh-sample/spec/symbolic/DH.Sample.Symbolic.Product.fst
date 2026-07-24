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
  entries (times 0 and 2), attributed to fixed distinct DY role principals.
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
      discharged in DH.Sample.Symbolic.Provenance);

    * a DELIVERY reads a prior `MsgSent` with the genuine `recv_msg` at the
      delivered packet's recorded position, and the receiver combines its scalar
      with the STRUCTURED share it actually received.

  Because one concrete system step performs several DY* operations, the product
  is a stuttering refinement whose observable projection onto the concrete system
  is nonetheless EXACT (same before state, event, after state, outputs).

  The ideal-symbolic-crypto boundary versus computational assumptions
  ------------------------------------------------------------------
  This is an IDEAL symbolic-crypto model: signatures are genuine `Sign` terms and
  unforgeability is stipulated (an attacker injection is an all-literal term,
  which cannot be an honest `Sign`; and the concrete completion step already
  requires an honest peer origin — see `DH.Sample.System`).  We make NO
  computational hardness assumption; the toy concrete digest is deliberately weak
  and is never the sole justification for a completion.
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

#pop-options

(** ── Genuine DY* trace-monad segments ───────────────────────────────────────
    Each concrete system step's provenance is the trace produced by RUNNING these
    computations.  Receiving segments begin with a genuine `recv_msg` at the
    delivered packet's position (which does not change the trace) and then append
    the endpoint's own random generations / authorizations / sends. *)

(** Setup: draw the endpoint's long-term signing key and register it. *)
let setup_run (mep:T.principal) (me_t:BT.bytes) (tr:TB.trace) : (BT.bytes & TB.trace) =
  let (ltk, tr) = mk_rand ltk_usage ltk_label ltk_len tr in
  let (_, tr) = trigger_event mep tag_keygen (keygen_content me_t (vkey_term ltk)) tr in
  (ltk, tr)

(** One explicit ideal-RNG transition: draw a secret-labelled ephemeral. *)
let rng_run (tr:TB.trace) : (BT.bytes & TB.trace) =
  mk_rand eph_usage eph_label eph_len tr

(** Initiator start consumes a scalar drawn by an earlier `rng_run`. *)
let start_run (mep:T.principal) (me_t peer_t scalar:BT.bytes) (tr:TB.trace)
  : (BT.bytes & TB.trace) =
  let (_, tr) = trigger_event mep tag_initiate (initiate_content me_t peer_t (share_term scalar)) tr in
  let (_, tr) = send_msg (flatten (SMsg1 me_t (share_term scalar))) tr in
  (scalar, tr)

(** Responder respond consumes a scalar drawn by an earlier `rng_run`: read the
    delivered message 1, authorize, draw a signing nonce, send message 2. *)
let respond_run (mep:T.principal) (ltk me_t a_t peer_share scalar:BT.bytes)
                (tr:TB.trace) (rpos:nat)
  : (BT.bytes & TB.trace) =
  let (_, tr) = recv_msg rpos tr in
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let (_, tr) = trigger_event mep tag_responder_respond transcript tr in
  let (signonce, tr) = mk_rand signonce_usage signonce_label signonce_len tr in
  let (_, tr) = send_msg (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk signonce transcript))) tr in
  (scalar, tr)

(** Initiator finish: read the delivered message 2, authorize, draw a signing
    nonce, send message 3. *)
let ifinish_run (mep:T.principal) (ltk scalar b_t peer_share:BT.bytes) (tr:TB.trace) (rpos:nat)
  : (unit & TB.trace) =
  let (_, tr) = recv_msg rpos tr in
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let (_, tr) = trigger_event mep tag_initiator_finish transcript tr in
  let (signonce, tr) = mk_rand signonce_usage signonce_label signonce_len tr in
  let (_, tr) = send_msg (flatten (SMsg3 (sig_term ltk signonce transcript))) tr in
  ((), tr)

(** Responder finish: read the delivered message 3, record completion. *)
let rfinish_run (mep:T.principal) (a_t key:BT.bytes) (tr:TB.trace) (rpos:nat) : (unit & TB.trace) =
  let (_, tr) = recv_msg rpos tr in
  trigger_event mep tag_responder_finish (session_content a_t key) tr

(** Attacker injection: put publishable all-literal bytes on the network. *)
let inject_run (sm:sym_msg) (tr:TB.trace) : (nat & TB.trace) =
  send_msg (flatten sm) tr

(** ── Transparent trace chains of each segment ───────────────────────────────*)

let setup_trace (mep:T.principal) (me_t:BT.bytes) (tr:TB.trace) : TB.trace =
  let ltk = ltk_term (TB.trace_length tr) in
  TB.append_entry
    (TB.append_entry tr (T.RandGen ltk_usage ltk_label ltk_len))
    (T.Event mep tag_keygen (keygen_content me_t (vkey_term ltk)))

let rng_trace (tr:TB.trace) : TB.trace =
  TB.append_entry tr (T.RandGen eph_usage eph_label eph_len)

let start_trace (mep:T.principal) (me_t peer_t scalar:BT.bytes) (tr:TB.trace) : TB.trace =
  TB.append_entry
    (TB.append_entry tr
      (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))))
    (T.MsgSent (flatten (SMsg1 me_t (share_term scalar))))

let respond_trace (mep:T.principal) (ltk me_t a_t peer_share scalar:BT.bytes)
                  (tr:TB.trace) : TB.trace =
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let signonce = signonce_term (TB.trace_length tr + 1) in
  TB.append_entry
    (TB.append_entry
      (TB.append_entry tr
        (T.Event mep tag_responder_respond transcript))
      (T.RandGen signonce_usage signonce_label signonce_len))
    (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk signonce transcript))))

let ifinish_trace (mep:T.principal) (ltk scalar b_t peer_share:BT.bytes) (tr:TB.trace) : TB.trace =
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let signonce = signonce_term (TB.trace_length tr + 1) in
  TB.append_entry
    (TB.append_entry
      (TB.append_entry tr (T.Event mep tag_initiator_finish transcript))
      (T.RandGen signonce_usage signonce_label signonce_len))
    (T.MsgSent (flatten (SMsg3 (sig_term ltk signonce transcript))))

let rfinish_trace (mep:T.principal) (a_t key:BT.bytes) (tr:TB.trace) : TB.trace =
  TB.append_entry tr (T.Event mep tag_responder_finish (session_content a_t key))

let inject_trace (sm:sym_msg) (tr:TB.trace) : TB.trace =
  TB.append_entry tr (T.MsgSent (flatten sm))

(** ── Structure lemmas: each run equals its transparent chain ────────────────*)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"

let setup_structure (mep:T.principal) (me_t:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let (ltk, tr') = setup_run mep me_t tr in
      ltk == ltk_term (TB.trace_length tr) /\ tr' == setup_trace mep me_t tr))
= let (ltk, tr') = setup_run mep me_t tr in
  assert (ltk == ltk_term (TB.trace_length tr));
  assert (tr' == setup_trace mep me_t tr)

let rng_structure (tr:TB.trace)
  : Lemma (ensures (
      let (scalar, tr') = rng_run tr in
      scalar == eph_term (TB.trace_length tr) /\ tr' == rng_trace tr))
= let (scalar, tr') = rng_run tr in
  assert (scalar == eph_term (TB.trace_length tr));
  assert (tr' == rng_trace tr)

let start_structure (mep:T.principal) (me_t peer_t scalar:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let (scalar', tr') = start_run mep me_t peer_t scalar tr in
      scalar' == scalar /\ tr' == start_trace mep me_t peer_t scalar tr))
= let (scalar', tr') = start_run mep me_t peer_t scalar tr in
  assert (scalar' == scalar);
  assert (tr' == start_trace mep me_t peer_t scalar tr)

let respond_structure (mep:T.principal) (ltk me_t a_t peer_share scalar:BT.bytes)
                      (tr:TB.trace) (rpos:nat)
  : Lemma (ensures (
      let (scalar', tr') = respond_run mep ltk me_t a_t peer_share scalar tr rpos in
      scalar' == scalar /\
      tr' == respond_trace mep ltk me_t a_t peer_share scalar tr))
= let (scalar', tr') = respond_run mep ltk me_t a_t peer_share scalar tr rpos in
  assert (scalar' == scalar);
  assert (tr' == respond_trace mep ltk me_t a_t peer_share scalar tr)

let ifinish_structure (mep:T.principal) (ltk scalar b_t peer_share:BT.bytes) (tr:TB.trace) (rpos:nat)
  : Lemma (ensures (
      let (_, tr') = ifinish_run mep ltk scalar b_t peer_share tr rpos in
      tr' == ifinish_trace mep ltk scalar b_t peer_share tr))
= let (_, tr') = ifinish_run mep ltk scalar b_t peer_share tr rpos in
  assert (tr' == ifinish_trace mep ltk scalar b_t peer_share tr)

let rfinish_structure (mep:T.principal) (a_t key:BT.bytes) (tr:TB.trace) (rpos:nat)
  : Lemma (ensures (
      let (_, tr') = rfinish_run mep a_t key tr rpos in
      tr' == rfinish_trace mep a_t key tr))
= let (_, tr') = rfinish_run mep a_t key tr rpos in
  assert (tr' == rfinish_trace mep a_t key tr)

let inject_structure (sm:sym_msg) (tr:TB.trace)
  : Lemma (ensures (
      let (pos, tr') = inject_run sm tr in
      pos == TB.trace_length tr /\ tr' == inject_trace sm tr))
= let (pos, tr') = inject_run sm tr in
  assert (pos == TB.trace_length tr);
  assert (tr' == inject_trace sm tr)

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

(** ── Segment facts: growth and exact entry positions ────────────────────────*)

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10"

let setup_facts (mep:T.principal) (me_t:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = setup_trace mep me_t tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.RandGen ltk_usage ltk_label ltk_len) /\
      TB.entry_at tr' (n + 1) (T.Event mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n)))) /\
      TB.event_triggered tr' mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n)))))
= let n = TB.trace_length tr in
  grows2 tr (T.RandGen ltk_usage ltk_label ltk_len)
            (T.Event mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n))))

let rng_facts (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = rng_trace tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.RandGen eph_usage eph_label eph_len)))
= let n = TB.trace_length tr in
  TB.grows_snoc tr (T.RandGen eph_usage eph_label eph_len)

let start_facts (mep:T.principal) (me_t peer_t scalar:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = start_trace mep me_t peer_t scalar tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))) /\
      TB.entry_at tr' (n + 1) (T.MsgSent (flatten (SMsg1 me_t (share_term scalar)))) /\
      TB.event_triggered tr' mep tag_initiate (initiate_content me_t peer_t (share_term scalar))))
= let n = TB.trace_length tr in
  let tr' = start_trace mep me_t peer_t scalar tr in
  grows2 tr (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar)))
            (T.MsgSent (flatten (SMsg1 me_t (share_term scalar))));
  assert (TB.entry_at tr' n (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))));
  assert (TB.entry_at tr' (n + 1) (T.MsgSent (flatten (SMsg1 me_t (share_term scalar)))))

let respond_facts (mep:T.principal) (ltk me_t a_t peer_share scalar:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let transcript = transcript_term a_t peer_share (share_term scalar) in
      let tr' = respond_trace mep ltk me_t a_t peer_share scalar tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.Event mep tag_responder_respond transcript) /\
      TB.entry_at tr' (n + 1) (T.RandGen signonce_usage signonce_label signonce_len) /\
      TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript)))) /\
      TB.event_triggered tr' mep tag_responder_respond transcript))
= let n = TB.trace_length tr in
  let transcript = transcript_term a_t peer_share (share_term scalar) in
  let tr' = respond_trace mep ltk me_t a_t peer_share scalar tr in
  grows3 tr (T.Event mep tag_responder_respond transcript)
            (T.RandGen signonce_usage signonce_label signonce_len)
            (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript))));
  assert (TB.entry_at tr' n (T.Event mep tag_responder_respond transcript));
  assert (TB.entry_at tr' (n + 1) (T.RandGen signonce_usage signonce_label signonce_len));
  assert (TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript)))))

let ifinish_facts (mep:T.principal) (ltk scalar b_t peer_share:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let transcript = transcript_term b_t (share_term scalar) peer_share in
      let tr' = ifinish_trace mep ltk scalar b_t peer_share tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.Event mep tag_initiator_finish transcript) /\
      TB.entry_at tr' (n + 1) (T.RandGen signonce_usage signonce_label signonce_len) /\
      TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript)))) /\
      TB.event_triggered tr' mep tag_initiator_finish transcript))
= let n = TB.trace_length tr in
  let transcript = transcript_term b_t (share_term scalar) peer_share in
  let tr' = ifinish_trace mep ltk scalar b_t peer_share tr in
  grows3 tr (T.Event mep tag_initiator_finish transcript)
            (T.RandGen signonce_usage signonce_label signonce_len)
            (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript))));
  assert (TB.entry_at tr' n (T.Event mep tag_initiator_finish transcript));
  assert (TB.entry_at tr' (n + 1) (T.RandGen signonce_usage signonce_label signonce_len));
  assert (TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript)))))

let rfinish_facts (mep:T.principal) (a_t key:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = rfinish_trace mep a_t key tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.Event mep tag_responder_finish (session_content a_t key)) /\
      TB.event_triggered tr' mep tag_responder_finish (session_content a_t key)))
= let n = TB.trace_length tr in
  TB.grows_snoc tr (T.Event mep tag_responder_finish (session_content a_t key))

let inject_facts (sm:sym_msg) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = inject_trace sm tr in
      tr `TB.grows` tr' /\
      TB.entry_at tr' n (T.MsgSent (flatten sm))))
= let n = TB.trace_length tr in
  TB.grows_snoc tr (T.MsgSent (flatten sm))

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
}

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

(** ── Initial product state ──────────────────────────────────────────────────

    Both endpoints' setups run on the ONE shared trace: the initiator's long-term
    key `RandGen`/`Event` at positions 0/1, the responder's at 2/3.  The network
    is empty. *)
let product_initial (a b:principal) : product_state =
  let (ltk_a, tr1) = setup_run init_dy_principal (term_of_principal a) TB.empty_trace in
  let (ltk_b, tr2) = setup_run resp_dy_principal (term_of_principal b) tr1 in
  { ps_sys   = system_initial a b;
    ps_trace = tr2;
    ps_init  = { sh_ltk = ltk_a; sh_pending = None; sh_scalar = None;
                 sh_peer_share = None; sh_key = None };
    ps_resp  = { sh_ltk = ltk_b; sh_pending = None; sh_scalar = None;
                 sh_peer_share = None; sh_key = None };
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
          let (scalar, tr') = rng_run p0.ps_trace in
          Some (tr',
                { p0.ps_init with sh_pending = Some scalar },
                p0.ps_resp, p0.ps_net,
                { rs_owner = Init; rs_term = scalar; rs_pos = n } :: p0.ps_rng))
     | Resp ->
       (match p0.ps_resp.sh_pending with
        | Some _ -> None
        | None ->
          let (scalar, tr') = rng_run p0.ps_trace in
          Some (tr',
                p0.ps_init,
                { p0.ps_resp with sh_pending = Some scalar },
                p0.ps_net,
                { rs_owner = Resp; rs_term = scalar; rs_pos = n } :: p0.ps_rng)))
  | SM.LocalEvent ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       let me  = c0.sys_init.ep_me in
       let met = term_of_principal me in
       let (_, tr') =
         start_run init_dy_principal met (term_of_principal peer) scalar p0.ps_trace in
       let ne = { ne_smsg = SMsg1 met (share_term scalar);
                  ne_pos = n + 1; ne_auth = NoAuth } in
       Some (tr',
             { p0.ps_init with sh_pending = None; sh_scalar = Some scalar },
             p0.ps_resp,
             L.append p0.ps_net [ ne ],
             p0.ps_rng)
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
           let (_, tr') =
            respond_run resp_dy_principal p0.ps_resp.sh_ltk met at peer_share scalar
                        p0.ps_trace ne0.ne_pos in
           let transcript = transcript_term at peer_share (share_term scalar) in
           let ne = {
            ne_smsg = SMsg2 met (share_term scalar)
                        (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
            ne_pos  = n + 2;
            ne_auth = RespAuth at peer_share } in
           Some (tr', p0.ps_init,
                { p0.ps_resp with sh_pending = None; sh_scalar = Some scalar;
                    sh_peer_share = Some peer_share;
                    sh_key = Some (secret_term scalar peer_share) },
                L.append p0.ps_net [ ne ],
                p0.ps_rng))
      | Resp, Msg3 _ ->
        (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
         | Some a, Some key ->
           let me = c0.sys_resp.ep_me in
           let (_, tr') =
             rfinish_run resp_dy_principal (term_of_principal a) key
                         p0.ps_trace ne0.ne_pos in
           Some (tr', p0.ps_init, p0.ps_resp, p0.ps_net, p0.ps_rng)
         | _ -> None)
      | Init, Msg2 b gy _ ->
        (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
         | Some _xc, Some scalar ->
           let me  = c0.sys_init.ep_me in
           let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
           let (_, tr') =
             ifinish_run init_dy_principal p0.ps_init.sh_ltk scalar
                         (term_of_principal b) peer_share p0.ps_trace ne0.ne_pos in
           let transcript = transcript_term (term_of_principal b) (share_term scalar) peer_share in
           let ne = {
             ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk
                               (signonce_term (n + 1)) transcript);
             ne_pos  = n + 2;
             ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share } in
           Some (tr',
                 { p0.ps_init with sh_peer_share = Some peer_share; sh_key = Some (secret_term scalar peer_share) },
                 p0.ps_resp,
                 L.append p0.ps_net [ ne ],
                 p0.ps_rng)
         | _ -> None)
      | _, _ -> None
    end else None
  | SM.LocalEvent (ActInject m) ->
    let (pos, tr') = inject_run (inject_smsg m) p0.ps_trace in
    Some (tr', p0.ps_init, p0.ps_resp,
         L.append p0.ps_net
           [ { ne_smsg = inject_smsg m; ne_pos = pos; ne_auth = NoAuth } ],
         p0.ps_rng)
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

let ltk_coherent_at (mep:T.principal) (me_t:BT.bytes) (tr:TB.trace) (ltk:BT.bytes) (pos:nat) : prop =
  ltk == ltk_term pos /\
  TB.entry_at tr pos (T.RandGen ltk_usage ltk_label ltk_len) /\
  TB.event_triggered tr mep tag_keygen (keygen_content me_t (vkey_term ltk))

let scalar_recorded (tr:TB.trace) (s:BT.bytes) : prop =
  exists (t:nat). s == eph_term t /\ TB.entry_at tr t (T.RandGen eph_usage eph_label eph_len)

(** The concrete and symbolic RNG registries are parallel.  Every symbolic
    representative is exactly the secret Rand at its recorded generation
    position; the concrete registry's `system_rng_wf` supplies no-reuse. *)
let rng_entry_coherent (d:rng_draw) (rs:rng_shadow) (tr:TB.trace) : prop =
  rs.rs_owner == d.rd_owner /\
  rs.rs_term == eph_term rs.rs_pos /\
  TB.entry_at tr rs.rs_pos (T.RandGen eph_usage eph_label eph_len)

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
    (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded tr s)
  | Sent Resp, Msg2 b _ _, SMsg2 b_s gys sgs, RespAuth partner peer_share ->
    b_s == term_of_principal b /\
    (exists (s:BT.bytes). gys == share_term s /\ scalar_recorded tr s) /\
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
  ltk_coherent_at init_dy_principal (term_of_principal c.sys_init.ep_me)
                  p.ps_trace p.ps_init.sh_ltk 0 /\
  ltk_coherent_at resp_dy_principal (term_of_principal c.sys_resp.ep_me)
                  p.ps_trace p.ps_resp.sh_ltk 2

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
  (match p.ps_init.sh_pending with None -> True | Some s -> scalar_recorded p.ps_trace s) /\
  (match p.ps_resp.sh_pending with None -> True | Some s -> scalar_recorded p.ps_trace s) /\
  (match p.ps_init.sh_scalar with None -> True | Some s -> scalar_recorded p.ps_trace s) /\
  (match p.ps_resp.sh_scalar with None -> True | Some s -> scalar_recorded p.ps_trace s)

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
  network_state_coherent p

(** ── Trace-growth persistence of the coherence components ────────────────────

    As the shared trace grows, an established long-term-key coherence and an
    established ephemeral recording persist (their `RandGen` / `Event` entries
    stay on the trace). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let ltk_coherent_grows (mep:T.principal) (me_t:BT.bytes) (tr tr':TB.trace) (ltk:BT.bytes) (pos:nat)
  : Lemma (requires ltk_coherent_at mep me_t tr ltk pos /\ tr `TB.grows` tr')
          (ensures ltk_coherent_at mep me_t tr' ltk pos)
= TB.entry_at_grows tr tr' pos (T.RandGen ltk_usage ltk_label ltk_len);
  TB.event_triggered_grows tr tr' mep tag_keygen (keygen_content me_t (vkey_term ltk))

let scalar_recorded_grows (tr tr':TB.trace) (s:BT.bytes)
  : Lemma (requires scalar_recorded tr s /\ tr `TB.grows` tr')
          (ensures scalar_recorded tr' s)
= eliminate exists (t:nat). s == eph_term t /\ TB.entry_at tr t (T.RandGen eph_usage eph_label eph_len)
  returns scalar_recorded tr' s
  with _.
    TB.entry_at_grows tr tr' t (T.RandGen eph_usage eph_label eph_len)

let rng_entry_coherent_grows (d:rng_draw) (rs:rng_shadow) (tr tr':TB.trace)
  : Lemma
    (requires rng_entry_coherent d rs tr /\ tr `TB.grows` tr')
    (ensures rng_entry_coherent d rs tr')
= TB.entry_at_grows tr tr' rs.rs_pos
    (T.RandGen eph_usage eph_label eph_len)

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
      TB.entry_at tr' pos (T.RandGen eph_usage eph_label eph_len))
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
   | Some s -> scalar_recorded_grows p0.ps_trace p1.ps_trace s
   | None -> ());
  (match p0.ps_resp.sh_pending with
   | Some s -> scalar_recorded_grows p0.ps_trace p1.ps_trace s
   | None -> ());
  (match p0.ps_init.sh_scalar with
   | Some s -> scalar_recorded_grows p0.ps_trace p1.ps_trace s
   | None -> ());
  (match p0.ps_resp.sh_scalar with
   | Some s -> scalar_recorded_grows p0.ps_trace p1.ps_trace s
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
let share_recorded_grows (gxs:BT.bytes) (tr tr':TB.trace)
  : Lemma
    (requires (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded tr s) /\
              tr `TB.grows` tr')
    (ensures (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded tr' s))
= eliminate exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded tr s
  returns (exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded tr' s)
  with _.
    (scalar_recorded_grows tr tr' s;
     introduce exists (s':BT.bytes). gxs == share_term s' /\ scalar_recorded tr' s'
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
  | Sent Init, Msg1 _ _, SMsg1 _ gxs, NoAuth -> share_recorded_grows gxs tr tr'
  | Sent Resp, Msg2 _ _ _, SMsg2 _ gys _, RespAuth _ _ ->
    share_recorded_grows gys tr tr'
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
        scalar_recorded tr s /\ pos < TB.trace_length tr /\
        TB.entry_at tr pos (T.MsgSent (flatten (SMsg1 (term_of_principal a) (share_term s)))))
      (ensures net_entry_coherent init_ltk resp_ltk
                 ({ pk_msg = Msg1 a gx; pk_origin = Sent Init })
                 ({ ne_smsg = SMsg1 (term_of_principal a) (share_term s);
                   ne_pos = pos; ne_auth = NoAuth }) tr)
= reveal_opaque (`%smsg_provenance) smsg_provenance;
  introduce exists (s':BT.bytes). share_term s == share_term s' /\ scalar_recorded tr s'
  with s and ()

let coherent_sent_msg2
  (init_ltk resp_ltk:BT.bytes)
  (b:principal) (gy:dh_share) (sigB:signature)
  (s partner peer_share:BT.bytes) (pos:nat) (tr:TB.trace)
  : Lemma
      (requires
        scalar_recorded tr s /\ pos < TB.trace_length tr /\
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
  introduce exists (s':BT.bytes). share_term s == share_term s' /\ scalar_recorded tr s'
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
        scalar_recorded tr' s /\ pos < TB.trace_length tr' /\
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
        scalar_recorded tr' s /\ pos < TB.trace_length tr' /\
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
  lemma_role_principals_distinct ();
  let tr0 = TB.empty_trace in
  setup_structure init_dy_principal (term_of_principal a) tr0;
  setup_facts init_dy_principal (term_of_principal a) tr0;
  let (_, tr1) = setup_run init_dy_principal (term_of_principal a) tr0 in
  setup_structure resp_dy_principal (term_of_principal b) tr1;
  setup_facts resp_dy_principal (term_of_principal b) tr1

(** Non-vacuity of the supported profile: a well-formed product state exists. *)
let lemma_wf_inhabited (a b:principal)
  : Lemma (ensures (exists (p:product_state). wf p))
= lemma_product_initial_wf a b

#pop-options
