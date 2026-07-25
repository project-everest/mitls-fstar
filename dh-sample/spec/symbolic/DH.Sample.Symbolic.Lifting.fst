module DH.Sample.Symbolic.Lifting

(**
  DH.Sample.Symbolic.Lifting — the simulation that lifts every concrete execution
  of the WHOLE composed system (DH.Sample.System) to a symbolic PRODUCT execution
  that projects back onto it EXACTLY.

  This module depends ONLY on the DY* CORE library, the neutral Common.StateMachine
  framework, the standalone dh-sample pure specification (including the composed
  `DH.Sample.System`) and DH.Sample.Symbolic.{Terms,Product}.  It never imports,
  opens or reuses any DY* example, and never references an example module.

  Contents
  --------
    * `lift_next` / `lift_transition` / `lift_execution` / `lift_final`: TOTAL
      functions constructing the product transition(s) from the concrete system
      transition(s) and the CURRENT product state alone (via `sym_extend`).  No
      caller supplies any symbolic realization, successor, binding, provenance
      witness, or final symbolic state.

    * `lemma_lift_step`: the exhaustive ONE-STEP lift, read off `system_step`
      (whose completion boundary `ideal_completion_link_ok` is opaque and never
      inspected here).  It establishes the product step, the exact
      before/action/after/output projection, and preserves the coherence
      invariant `wf`.

    * `lemma_lift_execution`: induction over `Common.StateMachine.trace_reaches`
      lifting a whole system execution.

    * `lemma_lift_system_execution`: the HEADLINE simulation theorem.  Its caller
      supplies ONLY concrete data: the two identities, the concrete system
      transition list, the concrete final system state, and the concrete
      reachability fact.

    * `lemma_honest_system_run`: the full, honest, three-message run of the
      composed system is reachable AND lifts to a product execution that projects
      onto it exactly (the non-vacuity / completeness witness).
*)

module SM   = Common.StateMachine
module Sys  = DH.Sample.System
module Cr   = DH.Sample.Crypto
module B    = DY.Core.Bytes
module BT   = DY.Core.Bytes.Type
module TB   = DY.Core.Trace.Base
module T    = DY.Core.Trace.Type
module L    = FStar.List.Tot

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.System
open DH.Sample.Symbolic.Terms
open DH.Sample.Symbolic.Product

(** ── Total lift of one concrete system transition ───────────────────────────

    Every symbolic field is a total, canonical function of the previous product
    state and the concrete transition, computed by `sym_extend` (which RUNS the
    genuine DY* trace-monad segment).  For a shape-legal event the lift takes the
    `Some` branch; the `None` fallback (only reached at ill-shaped events, which
    never satisfy `system_step`) merely re-projects the concrete after-state. *)
let lift_next (p0:product_state) (ctr:Sys.system_transition) : product_state =
  match sym_extend p0 ctr.SM.tr_event with
  | Some (tr', i', r', net', rng') ->
    { ps_sys = ctr.SM.tr_next_state; ps_trace = tr'; ps_init = i';
      ps_resp = r'; ps_net = net'; ps_rng = rng' }
  | None -> { p0 with ps_sys = ctr.SM.tr_next_state }

type product_transition = SM.transition product_state dh_message sys_action local_output

let lift_transition (p0:product_state) (ctr:Sys.system_transition) : product_transition = {
  SM.tr_event      = ctr.SM.tr_event;
  SM.tr_next_state = lift_next p0 ctr;
  SM.tr_output     = ctr.SM.tr_output;
}

let rec lift_execution (p0:product_state) (ct:list Sys.system_transition)
  : Tot (list product_transition) (decreases ct) =
  match ct with
  | [] -> []
  | ctr :: rest -> lift_transition p0 ctr :: lift_execution (lift_next p0 ctr) rest

let rec lift_final (p0:product_state) (ct:list Sys.system_transition)
  : Tot product_state (decreases ct) =
  match ct with
  | [] -> p0
  | ctr :: rest -> lift_final (lift_next p0 ctr) rest

(** ── Exact projection: transitions and explicit before/after frames ──────────*)

let project_transition (ptr:product_transition) : Sys.system_transition = {
  SM.tr_event      = ptr.SM.tr_event;
  SM.tr_next_state = proj ptr.SM.tr_next_state;
  SM.tr_output     = ptr.SM.tr_output;
}

let execution_projects_exactly (ct:list Sys.system_transition) (pt:list product_transition) : prop =
  ct == L.map project_transition pt

(** An observable frame records BOTH endpoints of a step (before AND after). *)
noeq
type obs_frame = {
  ofr_before : system_state;
  ofr_event  : sys_event;
  ofr_after  : system_state;
  ofr_output : sys_output;
}

let concrete_frame (c0:system_state) (ctr:Sys.system_transition) : obs_frame = {
  ofr_before = c0;
  ofr_event  = ctr.SM.tr_event;
  ofr_after  = ctr.SM.tr_next_state;
  ofr_output = ctr.SM.tr_output;
}

let product_frame (p0:product_state) (ptr:product_transition) : obs_frame = {
  ofr_before = proj p0;
  ofr_event  = ptr.SM.tr_event;
  ofr_after  = proj ptr.SM.tr_next_state;
  ofr_output = ptr.SM.tr_output;
}

let step_projects_exactly
  (p0:product_state) (ptr:product_transition) (c0:system_state) (ctr:Sys.system_transition) : prop =
  product_frame p0 ptr == concrete_frame c0 ctr

let rec product_frames (p0:product_state) (pt:list product_transition)
  : Tot (list obs_frame) (decreases pt) =
  match pt with
  | [] -> []
  | ptr :: rest -> product_frame p0 ptr :: product_frames ptr.SM.tr_next_state rest

let rec concrete_frames (c0:system_state) (ct:list Sys.system_transition)
  : Tot (list obs_frame) (decreases ct) =
  match ct with
  | [] -> []
  | ctr :: rest -> concrete_frame c0 ctr :: concrete_frames ctr.SM.tr_next_state rest

let execution_frames_project_exactly
  (c0:system_state) (p0:product_state)
  (ct:list Sys.system_transition) (pt:list product_transition) : prop =
  proj p0 == c0 /\ product_frames p0 pt == concrete_frames c0 ct

let product_execution
  (psm:SM.state_machine product_state dh_message sys_action local_output)
  (p0:product_state) (pt:list product_transition) (p1:product_state) : GTot prop =
  SM.trace_reaches psm p0 pt p1

(** ── The exhaustive one-step lift ────────────────────────────────────────────

    Whenever the concrete composed system takes a step from a well-formed product
    state, the product takes the corresponding (stuttering) product step to the
    lifted next state, which projects EXACTLY onto the concrete next state (same
    before, event, after, output) and preserves the coherence invariant `wf`. *)
(** The complete conclusion of the one-step lift, factored out so each per-case
    helper lemma and the top-level dispatcher share exactly one statement.  It is
    the verbatim conjunction proven by `lemma_lift_step` below.  Marked `unfold`
    so each helper's `ensures` inlines to the explicit conjunction and the SMT
    solver splits the postcondition into independent per-conjunct sub-goals (each
    with its own rlimit budget), instead of one monolithic query. *)
unfold
let lift_step_ensures (p0:product_state) (ctr:Sys.system_transition) : GTot prop =
  let p1 = lift_next p0 ctr in
  product_step p0 ctr.SM.tr_event p1 ctr.SM.tr_output /\
  proj p1 == ctr.SM.tr_next_state /\
  wf p1 /\
  project_transition (lift_transition p0 ctr) == ctr /\
  step_projects_exactly p0 (lift_transition p0 ctr) (proj p0) ctr

(** Scalar-recording facts, isolated so the existential witnessing and the
    `grows` persistence run in a tiny context.  The per-case lemmas below only
    RECALL these `ensures` (a cheap match against an already-proven hypothesis),
    which keeps their heavy VCs (product step, network coherence) under rlimit. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let scalars_persist (p0:product_state) (tr':TB.trace)
  : Lemma
    (requires wf p0 /\ p0.ps_trace `TB.grows` tr')
    (ensures
      (match p0.ps_init.sh_scalar with None -> True | Some s -> scalar_recorded_for Init tr' s) /\
      (match p0.ps_resp.sh_scalar with None -> True | Some s -> scalar_recorded_for Resp tr' s) /\
      (match p0.ps_init.sh_pending with None -> True | Some s -> scalar_recorded_for Init tr' s) /\
      (match p0.ps_resp.sh_pending with None -> True | Some s -> scalar_recorded_for Resp tr' s))
= (match p0.ps_init.sh_scalar with Some s -> scalar_recorded_for_grows Init p0.ps_trace tr' s | None -> ());
  (match p0.ps_resp.sh_scalar with Some s -> scalar_recorded_for_grows Resp p0.ps_trace tr' s | None -> ());
  (match p0.ps_init.sh_pending with Some s -> scalar_recorded_for_grows Init p0.ps_trace tr' s | None -> ());
  (match p0.ps_resp.sh_pending with Some s -> scalar_recorded_for_grows Resp p0.ps_trace tr' s | None -> ())

(** The OTHER role's stored-state pointer survives a step that only refreshes
    THIS role's state: its `SetState` entry stays on the (grown) trace. *)
let state_pos_persists (who:endpoint_id) (sh:endpoint_shadow) (tr tr':TB.trace)
  : Lemma
    (requires state_pos_coherent who sh tr /\ tr `TB.grows` tr')
    (ensures state_pos_coherent who sh tr')
= TB.trace_length_grows tr tr';
  TB.entry_at_grows tr tr' sh.sh_state_pos
    (T.SetState (role_dy_principal who) (role_state_id who) (shadow_snapshot sh))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let new_scalar_recorded (who:endpoint_id) (tr':TB.trace) (newsc:BT.bytes) (n:nat)
  : Lemma
    (requires newsc == eph_term n /\
              TB.entry_at tr' n (T.RandGen eph_usage (eph_label who) eph_len))
    (ensures scalar_recorded_for who tr' newsc)
= introduce exists (t:nat). newsc == eph_term t /\
            TB.entry_at tr' t (T.RandGen eph_usage (eph_label who) eph_len)
  with n and ()
#pop-options

(** Rewrite the send-position-derived signing nonce in a tiny context before
    invoking the generic network append lemma.  This avoids making the full
    initiator-finish state-machine context participate in that rewrite. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let net_coherent_append_msg3_with_nonce
  (net:list packet) (sh:list net_entry) (tr tr':TB.trace)
  (init_ltk resp_ltk:BT.bytes)
  (sigA:signature) (partner my_share peer_share:BT.bytes)
  (nonce_pos pos:nat)
  : Lemma
    (requires
      net_coherent net sh tr init_ltk resp_ltk /\
      tr `TB.grows` tr' /\
      auth_nonce_pos pos == nonce_pos /\
      pos < TB.trace_length tr' /\
      TB.entry_at tr' pos
        (T.MsgSent (flatten (SMsg3
          (sig_term init_ltk (signonce_term nonce_pos)
            (transcript_term partner my_share peer_share))))))
    (ensures
      net_coherent
        (L.append net [ { pk_msg = Msg3 sigA; pk_origin = Sent Init } ])
        (L.append sh [ {
          ne_smsg = SMsg3
            (sig_term init_ltk (signonce_term nonce_pos)
              (transcript_term partner my_share peer_share));
          ne_pos = pos;
          ne_auth = InitAuth partner my_share peer_share } ])
        tr' init_ltk resp_ltk)
= net_coherent_append_sent_msg3 net sh tr tr' init_ltk resp_ltk sigA
     partner my_share peer_share pos
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let ifinish_net_coherent
  (net:list packet) (sh:list net_entry) (tr:TB.trace)
  (init_ltk resp_ltk:BT.bytes) (sigA:signature)
  (partner scalar peer_share content:BT.bytes)
  : Lemma
    (requires net_coherent net sh tr init_ltk resp_ltk)
    (ensures (
      let n = TB.trace_length tr in
      let tr' = ifinish_trace init_ltk scalar partner peer_share content tr in
      net_coherent
        (L.append net [ { pk_msg = Msg3 sigA; pk_origin = Sent Init } ])
        (L.append sh [ {
          ne_smsg = SMsg3
            (sig_term init_ltk (signonce_term (n + 1))
              (transcript_term partner (share_term scalar) peer_share));
          ne_pos = n + 2;
          ne_auth = InitAuth partner (share_term scalar) peer_share } ])
        tr' init_ltk resp_ltk))
= let n = TB.trace_length tr in
  ifinish_facts init_ltk scalar partner peer_share content tr;
  lemma_auth_nonce_pos_succ (n + 1);
  net_coherent_append_msg3_with_nonce net sh tr
    (ifinish_trace init_ltk scalar partner peer_share content tr)
    init_ltk resp_ltk sigA partner (share_term scalar) peer_share
    (n + 1) (n + 2)
#pop-options

(** ── Per-case one-step lifts ─────────────────────────────────────────────────

    Each concrete step shape is lifted by its own focused lemma, so the SMT query
    for each case sees only that case's hypotheses (small context, low rlimit).
    In every SENDING case the network grows by exactly one packet, discharged by
    an origin-specific `net_coherent_append_sent_msg*` (or `_injected`) lemma on
    the concrete packet `system_step` appends and the exact shadow `sym_extend`
    records; in the responder-finish, injection and COMPROMISE cases the network
    is unchanged, discharged by `net_coherent_grows`.  Long-term-key coherence,
    ephemeral recordings and the two roles' stored-state pointers persist across
    the segment's `grows` fact; the role whose live material changed gets a FRESH
    stored-state pointer from its segment's trailing `SetState`. *)

(** Explicit honest/internal RNG draw.  This is the ONLY case that creates an
    ephemeral Rand; protocol steps merely consume a pending draw.  It also
    REFRESHES the drawing role's stored state, so the new pending secret is
    inside the snapshot a later compromise of that role would hand over. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_rng
      (p0:product_state) (ctr:Sys.system_transition)
      (owner:endpoint_id) (x:dh_scalar)
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActRng owner x))
    (ensures lift_step_ensures p0 ctr)
= let c0 = p0.ps_sys in
  let n  = TB.trace_length p0.ps_trace in
  let scalar = eph_term n in
  match owner with
  | Init ->
    (match p0.ps_init.sh_pending with
     | Some _ -> ()
     | None ->
       let i' = { p0.ps_init with sh_pending = Some scalar; sh_state_pos = n + 1 } in
       let content = shadow_snapshot i' in
       rng_structure Init content p0.ps_trace;
       rng_facts Init content p0.ps_trace;
       let tr' = rng_trace Init content p0.ps_trace in
       ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                          p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
       ltk_coherent_grows Resp (term_of_principal c0.sys_resp.ep_me)
                          p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
       scalars_persist p0 tr';
       new_scalar_recorded Init tr' scalar n;
       rng_coherent_cons c0.sys_rng p0.ps_rng p0.ps_trace tr' Init x scalar n;
       state_pos_persists Resp p0.ps_resp p0.ps_trace tr';
       net_coherent_grows c0.sys_net p0.ps_net p0.ps_trace tr'
         p0.ps_init.sh_ltk p0.ps_resp.sh_ltk)
  | Resp ->
    (match p0.ps_resp.sh_pending with
     | Some _ -> ()
     | None ->
       let r' = { p0.ps_resp with sh_pending = Some scalar; sh_state_pos = n + 1 } in
       let content = shadow_snapshot r' in
       rng_structure Resp content p0.ps_trace;
       rng_facts Resp content p0.ps_trace;
       let tr' = rng_trace Resp content p0.ps_trace in
       ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                          p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
       ltk_coherent_grows Resp (term_of_principal c0.sys_resp.ep_me)
                          p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
       scalars_persist p0 tr';
       new_scalar_recorded Resp tr' scalar n;
       rng_coherent_cons c0.sys_rng p0.ps_rng p0.ps_trace tr' Resp x scalar n;
       state_pos_persists Init p0.ps_init p0.ps_trace tr';
       net_coherent_grows c0.sys_net p0.ps_net p0.ps_trace tr'
         p0.ps_init.sh_ltk p0.ps_resp.sh_ltk)
#pop-options

(** Initiator start consumes its pending RNG draw, sends message 1, and refreshes
    its stored state (which now holds the live ephemeral scalar). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_start (p0:product_state) (ctr:Sys.system_transition)
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent Sys.ActStart)
    (ensures lift_step_ensures p0 ctr)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  let me  = c0.sys_init.ep_me in
  let met = term_of_principal me in
  match c0.sys_init.ep_peer, c0.sys_init_pending, p0.ps_init.sh_pending with
  | Some peer, Some x, Some scalar ->
    let i' = { p0.ps_init with sh_pending = None; sh_scalar = Some scalar;
                               sh_state_pos = n + 2 } in
    let content = shadow_snapshot i' in
    start_structure met (term_of_principal peer) scalar content p0.ps_trace;
    start_facts     met (term_of_principal peer) scalar content p0.ps_trace;
    let tr' = start_trace met (term_of_principal peer) scalar content p0.ps_trace in
    ltk_coherent_grows Init met p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
    ltk_coherent_grows Resp (term_of_principal c0.sys_resp.ep_me)
                       p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
    rng_coherent_grows c0.sys_rng p0.ps_rng p0.ps_trace tr';
    scalars_persist p0 tr';
    scalar_recorded_for_grows Init p0.ps_trace tr' scalar;
    state_pos_persists Resp p0.ps_resp p0.ps_trace tr';
    assert (ctr.SM.tr_next_state.sys_net ==
            L.append c0.sys_net
              [ { pk_msg = Msg1 me (Cr.dh_exp x);
                  pk_origin = Sent Init } ]);
    net_coherent_append_sent_msg1 c0.sys_net p0.ps_net p0.ps_trace tr'
      p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
      me (Cr.dh_exp x) scalar (n + 1)
  | _, _, _ -> ()
#pop-options

(** Responder receives message 1, consumes its pending draw, sends Msg2, and
    refreshes its stored state (scalar, received peer share AND session key). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_resp_msg1
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      Msg1? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures lift_step_ensures p0 ctr)
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = L.index p0.ps_net idx in
  let cmsg = (L.index c0.sys_net idx).pk_msg in
  match cmsg, p0.ps_resp.sh_pending with
  | Msg1 a gx, Some scalar ->
    let me  = c0.sys_resp.ep_me in
    let met = term_of_principal me in
    let at = term_of_principal a in
    let peer_share =
      (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
    let r' = { p0.ps_resp with sh_pending = None; sh_scalar = Some scalar;
                 sh_peer_share = Some peer_share;
                 sh_key = Some (secret_term scalar peer_share);
                 sh_state_pos = n + 3 } in
    let content = shadow_snapshot r' in
    respond_structure p0.ps_resp.sh_ltk met at peer_share scalar content
                      p0.ps_trace ne0.ne_pos;
    respond_facts p0.ps_resp.sh_ltk met at peer_share scalar content p0.ps_trace;
    let tr' = respond_trace p0.ps_resp.sh_ltk met at peer_share scalar content p0.ps_trace in
    let transcript = transcript_term at peer_share (share_term scalar) in
    let ne = {
      ne_smsg = SMsg2 met (share_term scalar)
        (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
      ne_pos  = n + 2;
      ne_auth = RespAuth at peer_share } in
    assert (sym_extend p0 ctr.SM.tr_event ==
            Some (tr', p0.ps_init, r', L.append p0.ps_net [ ne ], p0.ps_rng));
    ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                      p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
    ltk_coherent_grows Resp met
                      p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
    rng_coherent_grows c0.sys_rng p0.ps_rng p0.ps_trace tr';
    scalars_persist p0 tr';
    scalar_recorded_for_grows Resp p0.ps_trace tr' scalar;
    state_pos_persists Init p0.ps_init p0.ps_trace tr';
    lemma_auth_nonce_pos_succ (n + 1);
    (match ctr.SM.tr_next_state.sys_resp.ep_scalar with
     | Some yc ->
      assert (ctr.SM.tr_next_state.sys_net ==
              L.append c0.sys_net
                [ { pk_msg = Msg2 me (Cr.dh_exp yc) (Cr.sign me (Cr.transcript a gx (Cr.dh_exp yc)));
                    pk_origin = Sent Resp } ]);
      net_coherent_append_sent_msg2 c0.sys_net p0.ps_net p0.ps_trace tr'
        p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
        me (Cr.dh_exp yc) (Cr.sign me (Cr.transcript a gx (Cr.dh_exp yc)))
        scalar at peer_share (n + 2)
     | None -> ())
  | _, _ -> ()
#pop-options

(** Responder receives message 3: completes, emits no wire packet (network
    unchanged) and stores no new state — its PHASE changes, its live key material
    does not (the session key was already retained at its Msg1 delivery). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_resp_msg3
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      Msg3? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures lift_step_ensures p0 ctr)
= let c0  = p0.ps_sys in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = L.index p0.ps_net idx in
  let cmsg = (L.index c0.sys_net idx).pk_msg in
  match cmsg with
  | Msg3 sigA ->
    (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
     | Some a, Some key ->
       let me = c0.sys_resp.ep_me in
       rfinish_structure (term_of_principal a) key p0.ps_trace ne0.ne_pos;
       rfinish_facts (term_of_principal a) key p0.ps_trace;
       let tr' = rfinish_trace (term_of_principal a) key p0.ps_trace in
       ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                          p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
       ltk_coherent_grows Resp (term_of_principal me)
                          p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
       rng_coherent_grows c0.sys_rng p0.ps_rng p0.ps_trace tr';
       scalars_persist p0 tr';
       state_pos_persists Init p0.ps_init p0.ps_trace tr';
       state_pos_persists Resp p0.ps_resp p0.ps_trace tr';
       L.append_l_nil c0.sys_net;
       assert (ctr.SM.tr_next_state.sys_net == c0.sys_net);
       assert (p0.ps_trace `TB.grows` tr');
       assert (net_coherent c0.sys_net p0.ps_net p0.ps_trace
                 p0.ps_init.sh_ltk p0.ps_resp.sh_ltk);
       net_coherent_grows c0.sys_net p0.ps_net p0.ps_trace tr'
         p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
     | _, _ -> ())
  | _ -> ()
#pop-options

(** The endpoint-representation half of the initiator's completion, in a context
    that carries ONLY the endpoint coherence of `p0` (never the network / key /
    state-pointer coherence, nor the trace segment), so the five-way `init_repr` /
    `resp_repr` matches are re-established in a small query. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_lift_step_init_msg2_repr
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net /\ idx < L.length p0.ps_net})
  : Lemma
    (requires
      endpoint_state_coherent p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures endpoint_state_coherent (lift_next p0 ctr))
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  let ne0  = L.index p0.ps_net idx in
  match (L.index c0.sys_net idx).pk_msg with
  | Msg2 b gy sigB ->
    (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
     | Some xc, Some scalar ->
       let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
       init_repr_finish c0.sys_init p0.ps_init xc gy scalar peer_share (n + 3)
     | _, _ -> ())
  | _ -> ()
#pop-options

(** Initiator receives message 2: completes, sends message 3 (packet with origin
    `Sent Init`) and refreshes its stored state (received peer share AND session
    key).  NOTE this case is admissible EITHER on an honest `Sent Resp` packet
    with a matching run link OR — after `ActCorrupt Resp` — on a FORGED injected
    packet; the lift is oblivious to which, since `Sys.system_step` already
    decided admissibility.

    The `wf` obligation is discharged one COMPONENT at a time (endpoint
    representation, long-term keys + stored-state pointers, RNG registry, network),
    each in its own small query; the assembling lemma below then only has to
    conjoin four already-proven facts. *)

(** Long-term-key coherence and the two stored-state pointers.  The initiator's
    pointer is the FRESH `SetState` this segment appended (position n+3, holding
    the new snapshot with the peer share and session key); the responder's old
    pointer persists under trace growth. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_init_msg2_keys
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures
      key_state_coherent (lift_next p0 ctr) /\
      state_state_coherent (lift_next p0 ctr))
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = L.index p0.ps_net idx in
  match (L.index c0.sys_net idx).pk_msg with
  | Msg2 b gy sigB ->
    (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
     | Some xc, Some scalar ->
       let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
       let i' = { p0.ps_init with sh_peer_share = Some peer_share;
                    sh_key = Some (secret_term scalar peer_share);
                    sh_state_pos = n + 3 } in
       let content = shadow_snapshot i' in
       ifinish_structure p0.ps_init.sh_ltk scalar
                         (term_of_principal b) peer_share content p0.ps_trace ne0.ne_pos;
       ifinish_facts p0.ps_init.sh_ltk scalar
                     (term_of_principal b) peer_share content p0.ps_trace;
       let tr' = ifinish_trace p0.ps_init.sh_ltk scalar
                               (term_of_principal b) peer_share content p0.ps_trace in
       ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                          p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
       ltk_coherent_grows Resp (term_of_principal c0.sys_resp.ep_me)
                          p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
       state_pos_persists Resp p0.ps_resp p0.ps_trace tr'
     | _, _ -> ())
  | _ -> ()
#pop-options

(** The RNG registry: unchanged by this step (no draw is made or consumed), so it
    only has to survive trace growth. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_init_msg2_rng
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures rng_state_coherent (lift_next p0 ctr))
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = L.index p0.ps_net idx in
  match (L.index c0.sys_net idx).pk_msg with
  | Msg2 b gy sigB ->
    (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
     | Some xc, Some scalar ->
       let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
       let i' = { p0.ps_init with sh_peer_share = Some peer_share;
                    sh_key = Some (secret_term scalar peer_share);
                    sh_state_pos = n + 3 } in
       let content = shadow_snapshot i' in
       ifinish_structure p0.ps_init.sh_ltk scalar
                         (term_of_principal b) peer_share content p0.ps_trace ne0.ne_pos;
       ifinish_facts p0.ps_init.sh_ltk scalar
                     (term_of_principal b) peer_share content p0.ps_trace;
       rng_state_coherent_grows_to p0 (lift_next p0 ctr)
     | _, _ -> ())
  | _ -> ()
#pop-options

(** The network: exactly one new packet — the initiator's `Sent Init` Msg3 —
    paired with the structured `Sign` shadow the segment put on the wire. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_init_msg2_net
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures network_state_coherent (lift_next p0 ctr))
= let c0  = p0.ps_sys in
  let n   = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0  = L.index p0.ps_net idx in
  match (L.index c0.sys_net idx).pk_msg with
  | Msg2 b gy sigB ->
    (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
     | Some xc, Some scalar ->
       let me  = c0.sys_init.ep_me in
       let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
       let i' = { p0.ps_init with sh_peer_share = Some peer_share;
                    sh_key = Some (secret_term scalar peer_share);
                    sh_state_pos = n + 3 } in
       let content = shadow_snapshot i' in
       ifinish_structure p0.ps_init.sh_ltk scalar
                         (term_of_principal b) peer_share content p0.ps_trace ne0.ne_pos;
       ifinish_facts p0.ps_init.sh_ltk scalar
                     (term_of_principal b) peer_share content p0.ps_trace;
       assert (c0.sys_init.ep_my_share == Some (Cr.dh_exp xc));
       assert (ctr.SM.tr_next_state.sys_net ==
               L.append c0.sys_net
                 [ { pk_msg = Msg3 (Cr.sign me (Cr.transcript b (Cr.dh_exp xc) gy)); pk_origin = Sent Init } ]);
       ifinish_net_coherent c0.sys_net p0.ps_net p0.ps_trace
         p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
         (Cr.sign me (Cr.transcript b (Cr.dh_exp xc) gy))
         (term_of_principal b) scalar peer_share content
     | _, _ -> ())
  | _ -> ()
#pop-options

(** Assembling the four components into `wf` of the lifted state. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_lift_step_init_msg2_wf
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures wf (lift_next p0 ctr))
= net_coherent_length p0.ps_sys.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  lemma_lift_step_init_msg2_repr p0 ctr idx;
  lemma_lift_step_init_msg2_keys p0 ctr idx;
  lemma_lift_step_init_msg2_rng  p0 ctr idx;
  lemma_lift_step_init_msg2_net  p0 ctr idx
#pop-options

(** The operational/projection half is definitional once `sym_extend` is known
    to take the Msg2 branch.  Keeping it separate prevents the much richer
    network/RNG well-formedness proof above from sharing one SMT query. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_init_msg2_operational
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures (
      let p1 = lift_next p0 ctr in
      product_step p0 ctr.SM.tr_event p1 ctr.SM.tr_output /\
      proj p1 == ctr.SM.tr_next_state /\
      project_transition (lift_transition p0 ctr) == ctr /\
      step_projects_exactly p0 (lift_transition p0 ctr) (proj p0) ctr))
= net_coherent_length p0.ps_sys.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_lift_step_init_msg2
      (p0:product_state) (ctr:Sys.system_transition)
      (idx:nat{idx < L.length p0.ps_sys.sys_net})
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      Msg2? (L.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures lift_step_ensures p0 ctr)
= lemma_lift_step_init_msg2_wf p0 ctr idx;
  lemma_lift_step_init_msg2_operational p0 ctr idx
#pop-options

(** Attacker injection: puts an all-literal packet (origin `Injected`) on the
    network. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_lift_step_inject (p0:product_state) (ctr:Sys.system_transition) (m:dh_message)
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActInject m))
    (ensures lift_step_ensures p0 ctr)
= let c0  = p0.ps_sys in
  inject_structure (inject_smsg m) p0.ps_trace;
  inject_facts     (inject_smsg m) p0.ps_trace;
  let (pos, tr') = inject_run (inject_smsg m) p0.ps_trace in
  ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                     p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
  ltk_coherent_grows Resp (term_of_principal c0.sys_resp.ep_me)
                     p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
  rng_coherent_grows c0.sys_rng p0.ps_rng p0.ps_trace tr';
  scalars_persist p0 tr';
  state_pos_persists Init p0.ps_init p0.ps_trace tr';
  state_pos_persists Resp p0.ps_resp p0.ps_trace tr';
  net_coherent_append_injected c0.sys_net p0.ps_net p0.ps_trace tr'
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk m pos
#pop-options

(** DYNAMIC COMPROMISE: appends exactly one `Corrupt` entry pointing at the
    target role's CURRENT stored state.  Nothing else moves — no shadow, no
    packet, no RNG entry, no stored-state pointer — so every coherence component
    is preserved purely by trace growth. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_lift_step_corrupt
      (p0:product_state) (ctr:Sys.system_transition) (who:endpoint_id)
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output /\
      ctr.SM.tr_event == SM.LocalEvent (Sys.ActCorrupt who))
    (ensures lift_step_ensures p0 ctr)
= let c0  = p0.ps_sys in
  let sh = (match who with Init -> p0.ps_init | Resp -> p0.ps_resp) in
  corrupt_structure sh.sh_state_pos p0.ps_trace;
  corrupt_facts sh.sh_state_pos p0.ps_trace;
  let tr' = corrupt_trace sh.sh_state_pos p0.ps_trace in
  ltk_coherent_grows Init (term_of_principal c0.sys_init.ep_me)
                     p0.ps_trace tr' p0.ps_init.sh_ltk (role_ltk_pos Init);
  ltk_coherent_grows Resp (term_of_principal c0.sys_resp.ep_me)
                     p0.ps_trace tr' p0.ps_resp.sh_ltk (role_ltk_pos Resp);
  rng_coherent_grows c0.sys_rng p0.ps_rng p0.ps_trace tr';
  scalars_persist p0 tr';
  state_pos_persists Init p0.ps_init p0.ps_trace tr';
  state_pos_persists Resp p0.ps_resp p0.ps_trace tr';
  net_coherent_grows c0.sys_net p0.ps_net p0.ps_trace tr'
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
#pop-options

(** The exhaustive one-step lift: dispatch on the concrete event shape to the
    matching per-case helper.  The non-transition shapes (a `WireEvent`, or a
    delivery whose (destination, message) pair fires no endpoint step) make the
    `system_step` hypothesis `False`, so the conclusion holds vacuously. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_lift_step (p0:product_state) (ctr:Sys.system_transition)
  : Lemma
    (requires
      wf p0 /\
      Sys.system_step p0.ps_sys ctr.SM.tr_event ctr.SM.tr_next_state ctr.SM.tr_output)
    (ensures (
      let p1 = lift_next p0 ctr in
      product_step p0 ctr.SM.tr_event p1 ctr.SM.tr_output /\
      proj p1 == ctr.SM.tr_next_state /\
      wf p1 /\
      project_transition (lift_transition p0 ctr) == ctr /\
      step_projects_exactly p0 (lift_transition p0 ctr) (proj p0) ctr))
= let c0 = p0.ps_sys in
  match ctr.SM.tr_event with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_lift_step_rng p0 ctr owner x
  | SM.LocalEvent Sys.ActStart -> lemma_lift_step_start p0 ctr
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    assert (idx < L.length c0.sys_net);
    let cmsg = (L.index c0.sys_net idx).pk_msg in
    (match dst, cmsg with
     | Resp, Msg1 _ _   -> lemma_lift_step_resp_msg1 p0 ctr idx
     | Resp, Msg3 _     -> lemma_lift_step_resp_msg3 p0 ctr idx
     | Init, Msg2 _ _ _ -> lemma_lift_step_init_msg2 p0 ctr idx
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActInject m) -> lemma_lift_step_inject p0 ctr m
  | SM.LocalEvent (Sys.ActCorrupt who) -> lemma_lift_step_corrupt p0 ctr who
  | _ -> ()
#pop-options

(** ── Whole-execution lift, by induction on `trace_reaches` ───────────────────*)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec lemma_lift_execution
  (a b:principal) (p0:product_state)
  (ct:list Sys.system_transition) (final:system_state)
  : Lemma
    (requires
      wf p0 /\
      SM.trace_reaches (Sys.system_state_machine a b) p0.ps_sys ct final)
    (ensures (
      let pt     = lift_execution p0 ct in
      let pfinal = lift_final p0 ct in
      SM.trace_reaches (product_sm a b) p0 pt pfinal /\
      pfinal.ps_sys == final /\
      execution_projects_exactly ct pt /\
      product_frames p0 pt == concrete_frames p0.ps_sys ct /\
      wf pfinal))
    (decreases ct)
= match ct with
  | [] -> ()
  | ctr :: rest ->
    lemma_lift_step p0 ctr;
    let p1 = lift_next p0 ctr in
    lemma_lift_execution a b p1 rest final
#pop-options

(** ── The headline simulation theorem ─────────────────────────────────────────

    For EVERY concrete execution of the composed system state machine there is a
    product execution of the product state machine that projects onto it EXACTLY —
    transition-for-transition AND at the explicit before/after frame level — and
    ends in a product state whose concrete projection is the concrete final state.

    The caller supplies ONLY: the two identities, the concrete transition list, the
    concrete final system state, and the concrete reachability fact.  No symbolic
    realization, successor, binding, provenance witness, hygiene premise or final
    symbolic state is required of the caller. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
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
        execution_frames_project_exactly (proj (product_initial a b)) (product_initial a b) ct pt /\
        proj pfinal == final))
= let p0 = product_initial a b in
  lemma_product_initial_wf a b;
  lemma_lift_execution a b p0 ct final;
  introduce exists (pt:list product_transition) (pfinal:product_state).
      product_execution (product_sm a b) p0 pt pfinal /\
      execution_projects_exactly ct pt /\
      execution_frames_project_exactly (proj p0) p0 ct pt /\
      proj pfinal == final
  with (lift_execution p0 ct) (lift_final p0 ct)
  and ()
#pop-options

(** ── The full honest three-message run (non-vacuity / completeness) ──────────

    The composed system's honest three-message run (both endpoints complete,
    agreeing on the key) is a genuine reachable execution AND lifts to a product
    execution that projects onto it exactly.  This exercises every completion
    transition, so no completion is hidden or vacuous. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_honest_system_run (a b:principal) (x y:dh_scalar)
  : Lemma
    (requires x =!= y)
    (ensures (
      let ct    = Sys.honest_run a b x y in
      let final = Sys.h_s4 a b x y in
      Cons? ct /\
      SM.trace_reaches (Sys.system_state_machine a b) (Sys.system_initial a b) ct final /\
      final.sys_init.ep_phase == Init_Done /\
      final.sys_resp.ep_phase == Resp_Done /\
      Sys.system_rng_wf final /\
      Sys.rng_has Init x final.sys_rng /\
      Sys.rng_has Resp y final.sys_rng /\
      Sys.hikey x y == Sys.hrkey x y /\
      (exists (pt:list product_transition) (pfinal:product_state).
         product_execution (product_sm a b) (product_initial a b) pt pfinal /\
         execution_projects_exactly ct pt /\
         proj pfinal == final)))
= Sys.lemma_honest_run_reaches a b x y;
  lemma_lift_system_execution a b (Sys.honest_run a b x y) (Sys.h_s4 a b x y)
#pop-options
