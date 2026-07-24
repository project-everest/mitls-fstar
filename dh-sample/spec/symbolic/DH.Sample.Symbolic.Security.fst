module DH.Sample.Symbolic.Security

(**
  DH.Sample.Symbolic.Security — the genuine SECURITY CONSEQUENCES the installed
  product invariant buys, for the DH sample.

  This module depends ONLY on the DY* CORE library and on the standalone
  dh-sample symbolic development (Terms, Product, Provenance, Lifting,
  Invariant).  It never imports, opens or reuses any DY* example, and never
  references an example module.

  It is the fourth symbolic milestone.  The first three established:

    * DH.Sample.Symbolic.Lifting — every concrete execution of the composed
      system lifts to an EXACT symbolic product execution;
    * DH.Sample.Symbolic.Invariant — `ideal_product_invariant` holds initially
      and is preserved by every `product_step`, hence at every reachable state,
      with NO hygiene premise.

  This module turns `ideal_product_invariant` into real, non-tautological
  security guarantees.  Everything below is derived FROM the installed invariant
  and the DY* CORE crypto/label/attacker API; nothing assumes the desired
  authentication event, a matching session, or non-knowledge.

  ────────────────────────────────────────────────────────────────────────────
  What is a genuine security consequence here (and what is NOT assumed)
  ────────────────────────────────────────────────────────────────────────────
  The headline theorems quantify over ARBITRARY reachable product executions —
  `product_execution (product_sm a b) (product_initial a b) pt pfinal` — under
  exactly three explicitly named boundaries, and NOTHING else:

    (I)   the installed IDEAL PROFILE `ideal_product_invariant` (coherence `wf`
          + `trace_invariant` + no `Corrupt` trace entry), which
          DH.Sample.Symbolic.Invariant proves holds at every reachable state;
    (N)   NO-CORRUPTION: a conjunct of the ideal profile (`product_no_corruption`
          = `trace_has_no_corrupt`);
    (E)   the ideal ENVIRONMENT boundaries of `DH.Sample.System`: the packet
          origin metadata (`deliver_origin_ok`, restricting the two COMPLETION
          messages to an honest sender) AND the run/session-link completion
          boundary (`ideal_completion_link_ok`, requiring sender/receiver flights
          linked to the SAME Msg1 index) — see dh-sample/SYMBOLIC_SECURITY.md
          §"Ideal boundaries".  Msg1 delivery is NOT restricted: an injected Msg1
          may drive the responder to `Resp_Wait3`, for which no honest secrecy or
          agreement is claimed.

  The authentication core does NOT rest on the origin metadata alone.  Per the
  audit, "packet-origin metadata cannot itself be the whole authentication
  proof": the actual authorization is extracted with the DY* CORE trace
  invariant — a signature that appears (inside a `MsgSent`) on a
  `trace_invariant` trace is `bytes_invariant`, and its signing key is the fixed
  role long-term key carrying the DY* bottom (`secret`) label, which never flows
  to `public`; hence the honest (`dh_sign_pred`) disjunct of the signature bytes
  invariant holds, pinning the EXACT prior authorization `Event` of the signer.
  The completion identity/share agreement is then DERIVED from the run link (the
  two Msg1-index invariants + immutable packet provenance), never stated by a
  guard.

  A separate honest-run witness (`lemma_secure_honest_run`) shows every headline
  is non-vacuous; `lemma_attacker_injected_msg1_nonvacuous` shows the injected-Msg1
  attack is a genuine reachable execution that cannot complete.
*)

module B    = DY.Core.Bytes
module BT   = DY.Core.Bytes.Type
module L    = DY.Core.Label
module LT   = DY.Core.Label.Type
module T    = DY.Core.Trace.Type
module TB   = DY.Core.Trace.Base
module TI   = DY.Core.Trace.Invariant
module AK   = DY.Core.Attacker.Knowledge
module SM   = Common.StateMachine
module Sys  = DH.Sample.System
module Lst  = FStar.List.Tot
open DY.Core.Trace.Manipulation

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.System
open DH.Sample.Symbolic.Terms
open DH.Sample.Symbolic.Product
open DH.Sample.Symbolic.Provenance
open DH.Sample.Symbolic.Lifting
open DH.Sample.Symbolic.Invariant

(** ═══════════════════════════════════════════════════════════════════════════
    Part 1 — The cryptographic authentication-extraction core
    ═══════════════════════════════════════════════════════════════════════════

    The single crypto step every authentication theorem uses: a signature term
    that is `bytes_invariant` on a trace, whose signing key is secret-labelled,
    must satisfy the honest `dh_sign_pred` disjunct — which pins the signer's
    exact prior authorization event.  This is the DY* CORE EUF-CMA idealization,
    NOT the toy digest. *)

(** A term carrying the DY* bottom (`secret`) label never flows to `public`:
    `flow_to_public_eq` turns flow-to-public into corruption, and `secret` is
    unconditionally non-corrupt (`is_corrupt_secret`). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_secret_not_public (tr:TB.trace)
  : Lemma (ensures ~(L.secret `L.can_flow tr` L.public))
= ()

(** The two fixed role long-term signing keys are secret-labelled: a `RandGen`
    with the `secret` label at the key's position gives its `get_label`, which is
    `L.secret`, so it never flows to public. *)
let lemma_ltk_not_public (tr:TB.trace) (pos:nat)
  : Lemma
    (requires TB.entry_at tr pos (T.RandGen ltk_usage ltk_label ltk_len))
    (ensures ~((B.get_label #dh_sample_crypto_usages tr (ltk_term pos)) `L.can_flow tr` L.public))
= lemma_rand_usage_label_of_entry tr ltk_usage ltk_label ltk_len pos
#pop-options

(** The subterms of a `bytes_invariant` signature term are themselves
    `bytes_invariant`.  Read off the `Sign` arm of the (revealed) bytes
    invariant — plain conjuncts, no existential. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_sign_parts_invariant (tr:TB.trace) (sk nonce msg:BT.bytes)
  : Lemma
    (requires B.bytes_invariant #dh_sample_crypto_invariants tr (sig_term sk nonce msg))
    (ensures
      B.bytes_invariant #dh_sample_crypto_invariants tr sk /\
      B.bytes_invariant #dh_sample_crypto_invariants tr nonce /\
      B.bytes_invariant #dh_sample_crypto_invariants tr msg)
= reveal_opaque (`%B.sign) B.sign;
  assert (sig_term sk nonce msg == BT.Sign sk nonce msg);
  reveal_opaque (`%B.bytes_invariant) (B.bytes_invariant #dh_sample_crypto_invariants)
#pop-options

(** The EUF-CMA extraction, via the DY* CORE forward lemma `bytes_invariant_verify`.
    A signature `sig_term (ltk_term pos) nonce msg` that is `bytes_invariant` on
    `tr`, whose signing key is the fixed role long-term key recorded (secret) at
    `pos`, must satisfy the honest `dh_sign_pred` disjunct — the attacker
    disjunct (`get_signkey_label (vk sk) can_flow public`) reduces to the signing
    key flowing to `public`, which is excluded because the key is secret.  This
    recovers the signer's EXACT prior authorization event; the toy digest plays
    no part. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_ltk_sig_authorized (tr:TB.trace) (pos:nat) (nonce msg:BT.bytes)
  : Lemma
    (requires
      TB.entry_at tr pos (T.RandGen ltk_usage ltk_label ltk_len) /\
      B.bytes_invariant #dh_sample_crypto_invariants tr (sig_term (ltk_term pos) nonce msg))
    (ensures dh_sign_pred_fun tr ltk_usage (vkey_term (ltk_term pos)) msg)
= let sk = ltk_term pos in
  lemma_sign_parts_invariant tr sk nonce msg;
  lemma_rand_usage_label_of_entry tr ltk_usage ltk_label ltk_len pos;
  B.bytes_invariant_vk #dh_sample_crypto_invariants tr sk;
  B.has_signkey_usage_vk #dh_sample_crypto_usages tr sk ltk_usage;
  B.verify_sign sk nonce msg;
  B.bytes_invariant_verify #dh_sample_crypto_invariants tr (vkey_term sk) ltk_usage msg
    (sig_term sk nonce msg);
  B.get_signkey_label_vk #dh_sample_crypto_usages tr sk;
  lemma_ltk_not_public tr pos
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 2 — Network-level authentication (single lemmas, no induction)
    ═══════════════════════════════════════════════════════════════════════════

    For ANY reachable product state under `product_invariant`, an honestly-sent
    (`Sent Resp` Msg2 / `Sent Init` Msg3) packet's SIGNATURE — a genuine `Sign`
    term on the shared trace — pins the signer's EXACT prior authorization event.
    This is the crypto core of authentication: the origin metadata only tells us
    the shadow is a genuine structured `Sign` (never a literal); the actual
    authorization is recovered from the trace invariant, NOT from the origin and
    NOT from the toy digest. *)

(** A `MsgSent` term on a `trace_invariant` trace is `bytes_invariant`
    (`msg_sent_on_network_are_publishable` + `is_publishable` ⇒ `bytes_invariant`). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_msgsent_bytes_invariant (tr:TB.trace) (i:nat) (m:BT.bytes)
  : Lemma
    (requires
      TI.trace_invariant #dh_sample_protocol_invariants tr /\
      TB.entry_at tr i (T.MsgSent m))
    (ensures B.bytes_invariant #dh_sample_crypto_invariants tr m)
= introduce exists (j:T.timestamp). TB.entry_at tr j (T.MsgSent m) with i and ();
  TI.msg_sent_on_network_are_publishable #dh_sample_protocol_invariants tr m
#pop-options

(** The signature field of a Msg2 wire term is a `bytes_invariant` subterm
    (`flatten (SMsg2 b gy sig) = concat b (concat gy sig)`, split twice). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_msg2_sig_bytes_invariant (tr:TB.trace) (bt gyt sgt:BT.bytes)
  : Lemma
    (requires B.bytes_invariant #dh_sample_crypto_invariants tr (flatten (SMsg2 bt gyt sgt)))
    (ensures B.bytes_invariant #dh_sample_crypto_invariants tr sgt)
= assert (flatten (SMsg2 bt gyt sgt) == B.concat bt (B.concat gyt sgt));
  B.split_concat bt (B.concat gyt sgt);
  B.bytes_invariant_split #dh_sample_crypto_invariants tr
    (B.concat bt (B.concat gyt sgt)) (B.length bt);
  B.split_concat gyt sgt;
  B.bytes_invariant_split #dh_sample_crypto_invariants tr (B.concat gyt sgt) (B.length gyt)
#pop-options

(** The signature field of a Msg3 wire term IS the whole term
    (`flatten (SMsg3 sig) = sig`). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_msg3_sig_bytes_invariant (tr:TB.trace) (sgt:BT.bytes)
  : Lemma
    (requires B.bytes_invariant #dh_sample_crypto_invariants tr (flatten (SMsg3 sgt)))
    (ensures B.bytes_invariant #dh_sample_crypto_invariants tr sgt)
= assert (flatten (SMsg3 sgt) == sgt)
#pop-options

(** The two fixed verification keys are distinct terms (`Vk (Rand ltk_len 0)` vs
    `Vk (Rand ltk_len 2)`), so `dh_sign_pred_fun`'s two disjuncts are mutually
    exclusive on the key — the responder key can only satisfy the responder
    disjunct, the initiator key only the initiator disjunct. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let lemma_vkey_positions_distinct ()
  : Lemma (ensures vkey_term (ltk_term 0) =!= vkey_term (ltk_term 2))
= normalize_term_spec B.vk;
  assert (vkey_term (ltk_term 0) == BT.Vk (BT.Rand ltk_len 0));
  assert (vkey_term (ltk_term 2) == BT.Vk (BT.Rand ltk_len 2))
#pop-options

(** NETWORK RESPONDER AUTHENTICATION.  In any reachable state under
    `product_invariant`, every honestly-sent (`Sent Resp`) Msg2 packet's shadow
    is the responder's genuine `Sign` term over an exact transcript `(partner,
    gx, gy)`, and the RESPONDER role principal has triggered
    `tag_responder_respond` with EXACTLY that transcript on the trace.  The gy
    field is a trace-recorded honest DH share.  Derived purely from the trace
    invariant + `dh_sign_pred`; the origin only fixes that the shadow is a
    structured `Sign`, never a literal. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_net_responder_authorized (p:product_state) (j:nat)
  : Lemma
    (requires
      product_invariant p /\
      j < Lst.length p.ps_sys.sys_net /\
      (Lst.index p.ps_sys.sys_net j).pk_origin == Sent Resp /\
      Msg2? (Lst.index p.ps_sys.sys_net j).pk_msg)
    (ensures (
      j < Lst.length p.ps_net /\
      (let ne = Lst.index p.ps_net j in
       let pk = Lst.index p.ps_sys.sys_net j in
       (match pk.pk_msg, ne.ne_smsg, ne.ne_auth with
        | Msg2 b _ _, SMsg2 b_t gy_t sig_t, RespAuth partner gx_t ->
          b_t == term_of_principal b /\
          (exists (s:BT.bytes). gy_t == share_term s /\ scalar_recorded p.ps_trace s) /\
          TB.event_triggered p.ps_trace resp_dy_principal tag_responder_respond
            (transcript_term partner gx_t gy_t)
        | _, _, _ -> False))))
= let c = p.ps_sys in
  let tr = p.ps_trace in
  let init_ltk = p.ps_init.sh_ltk in
  let resp_ltk = p.ps_resp.sh_ltk in
  net_coherent_length c.sys_net p.ps_net tr init_ltk resp_ltk;
  let pk = Lst.index c.sys_net j in
  let ne = Lst.index p.ps_net j in
  net_coherent_index c.sys_net p.ps_net tr init_ltk resp_ltk j;
  lemma_sent_resp_msg2_exact p.ps_init p.ps_resp pk ne tr;
  lemma_msgsent_bytes_invariant tr ne.ne_pos (flatten ne.ne_smsg);
  (match pk.pk_msg, ne.ne_smsg, ne.ne_auth with
   | Msg2 _ _ _, SMsg2 b_t gy_t sig_t, RespAuth partner gx_t ->
     lemma_msg2_sig_bytes_invariant tr b_t gy_t sig_t;
     let nonce = signonce_term (auth_nonce_pos ne.ne_pos) in
     let transcript = transcript_term partner gx_t gy_t in
     assert (resp_ltk == ltk_term 2);
     assert (sig_t == sig_term (ltk_term 2) nonce transcript);
     lemma_ltk_sig_authorized tr 2 nonce transcript;
     lemma_vkey_positions_distinct ()
   | _, _, _ -> ())
#pop-options

(** NETWORK INITIATOR AUTHENTICATION.  Symmetric: every honestly-sent
    (`Sent Init`) Msg3 packet's shadow is the initiator's genuine `Sign` term
    over an exact transcript `(partner, gx, gy)`, and the INITIATOR role
    principal has triggered `tag_initiator_finish` with EXACTLY that transcript
    on the trace. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_net_initiator_authorized (p:product_state) (j:nat)
  : Lemma
    (requires
      product_invariant p /\
      j < Lst.length p.ps_sys.sys_net /\
      (Lst.index p.ps_sys.sys_net j).pk_origin == Sent Init /\
      Msg3? (Lst.index p.ps_sys.sys_net j).pk_msg)
    (ensures (
      j < Lst.length p.ps_net /\
      (let ne = Lst.index p.ps_net j in
       (match ne.ne_smsg, ne.ne_auth with
        | SMsg3 sig_t, InitAuth partner gx_t gy_t ->
          TB.event_triggered p.ps_trace init_dy_principal tag_initiator_finish
            (transcript_term partner gx_t gy_t)
        | _, _ -> False))))
= let c = p.ps_sys in
  let tr = p.ps_trace in
  let init_ltk = p.ps_init.sh_ltk in
  let resp_ltk = p.ps_resp.sh_ltk in
  net_coherent_length c.sys_net p.ps_net tr init_ltk resp_ltk;
  let pk = Lst.index c.sys_net j in
  let ne = Lst.index p.ps_net j in
  net_coherent_index c.sys_net p.ps_net tr init_ltk resp_ltk j;
  lemma_sent_init_msg3_exact p.ps_init p.ps_resp pk ne tr;
  lemma_msgsent_bytes_invariant tr ne.ne_pos (flatten ne.ne_smsg);
  (match ne.ne_smsg, ne.ne_auth with
   | SMsg3 sig_t, InitAuth partner gx_t gy_t ->
     lemma_msg3_sig_bytes_invariant tr sig_t;
     let nonce = signonce_term (auth_nonce_pos ne.ne_pos) in
     let transcript = transcript_term partner gx_t gy_t in
     assert (init_ltk == ltk_term 0);
     assert (sig_t == sig_term (ltk_term 0) nonce transcript);
     lemma_ltk_sig_authorized tr 0 nonce transcript;
     lemma_vkey_positions_distinct ()
   | _, _ -> ())
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 3 — Completion authentication (an inductive security invariant)
    ═══════════════════════════════════════════════════════════════════════════

    The network theorems above are about packets; the reachability deliverable is
    about ENDPOINT COMPLETION.  We install a small extra invariant, conjoined
    with the ideal profile, recording — for a COMPLETED endpoint — BOTH:

      * the CONCRETE full matching of the two endpoints' identities and both DH
        shares — DERIVED at completion from the run link `sys_resp_msg1_idx ==
        sys_init_msg1_idx` (`ideal_completion_link_ok`) plus the immutable Msg1
        packet provenance, never stated by the guard — AND
      * the SYMBOLIC authorization event of the PEER, whose own contributed DH
        share is exactly the share this endpoint holds (established at completion
        by the network authentication theorem above, i.e. by the trace invariant
        + `dh_sign_pred`, NOT by the toy digest).

    Both facts PERSIST (events are monotone; a completed endpoint's fields, and
    its already-responded peer's fields, are frozen).  See
    dh-sample/SYMBOLIC_SECURITY.md §"What is and isn't matching" for why the
    peer's view of the OTHER share stays symbolically a peer-chosen term. *)

(** ── Auditable signed-transcript provenance binding (the connective tissue) ───

    The audit requires that the authorization `Event` recovered (below) from an
    endpoint's OWN delivered signature be connected — as exactly as this model
    can HONESTLY support — to the identities AND both DH shares of the completion.
    A prior UNRELATED authorization event must not be enough.

    The events themselves are recovered ONLY from the genuine `Sign` term via
    `TI.trace_invariant` + the signature `bytes_invariant` + `dh_sign_pred`
    (`lemma_ltk_sig_authorized`, used in `lemma_net_{responder,initiator}_authorized`).
    Provenance metadata MAY link the exact transcript but CANNOT replace that
    signature extraction.  These two predicates are exactly such auditable
    provenance metadata: they pin the symbolic transcript INPUTS the sender
    recorded (`net_auth`, plus the sender's own contributed `share_term`) to the
    sender's CURRENT completed state.  Combined at each completion with the run
    link (`ideal_completion_link_ok` + the two Msg1 packet invariants, which relate
    the sender's frozen state to the RECEIVER's), they upgrade the recovered
    event from "some transcript" to "the transcript of THIS completion".

    `resp_send_authbind`: every network shadow that carries the responder's
    authorization metadata (`RespAuth partner peer_share`, produced only by the
    responder's Msg2 send) has
      * `partner`     == `term_of_principal` of the responder's recorded peer,
      * `peer_share`  == the responder's recorded (received) peer share, and
      * its own-share component == `share_term` of the responder's own ephemeral.
    The guard `RespAuth? ne_auth` references ONLY the immutable symbolic shadow,
    so preservation is a pure list/append argument; the responder having produced
    such a shadow forces it into `Resp_Wait3`/`Resp_Done`.

    Each is stated per-entry (`*_authbind_entry`) and quantified over the shared
    network so the append preservation is a clean list argument. *)
let resp_authbind_entry (p:product_state) (ne:net_entry) : prop =
  match ne.ne_auth with
  | RespAuth partner peer_share ->
    (p.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/ p.ps_sys.sys_resp.ep_phase == Resp_Done) /\
    Some? p.ps_sys.sys_resp.ep_peer /\
    Some? p.ps_resp.sh_peer_share /\
    Some? p.ps_resp.sh_scalar /\
    partner == term_of_principal (Some?.v p.ps_sys.sys_resp.ep_peer) /\
    peer_share == Some?.v p.ps_resp.sh_peer_share /\
    (match ne.ne_smsg with
     | SMsg2 _ gy _ -> gy == share_term (Some?.v p.ps_resp.sh_scalar)
     | _ -> True)
  | _ -> True

let resp_send_authbind (p:product_state) : prop =
  forall (j:nat). j < Lst.length p.ps_net ==> resp_authbind_entry p (Lst.index p.ps_net j)

(** `init_send_authbind`: symmetric for the initiator's Msg3 send.  Every network
    shadow carrying `InitAuth partner my_share peer_share` (produced only by the
    initiator's finish) has
      * `partner`    == `term_of_principal` of the initiator's fixed peer,
      * `my_share`   == `share_term` of the initiator's OWN ephemeral, and
      * `peer_share` == the initiator's recorded (received) peer share;
    and the initiator has finished (`Init_Done`). *)
let init_authbind_entry (p:product_state) (ne:net_entry) : prop =
  match ne.ne_auth with
  | InitAuth partner my_share peer_share ->
    p.ps_sys.sys_init.ep_phase == Init_Done /\
    Some? p.ps_sys.sys_init.ep_peer /\
    Some? p.ps_init.sh_scalar /\
    Some? p.ps_init.sh_peer_share /\
    partner == term_of_principal (Some?.v p.ps_sys.sys_init.ep_peer) /\
    my_share == share_term (Some?.v p.ps_init.sh_scalar) /\
    peer_share == Some?.v p.ps_init.sh_peer_share
  | _ -> True

let init_send_authbind (p:product_state) : prop =
  forall (j:nat). j < Lst.length p.ps_net ==> init_authbind_entry p (Lst.index p.ps_net j)

(** `init_msg1_send_authbind` is the auditable symbolic provenance binding for
    the initiator's unsigned first flight.  Any Msg1 shadow whose share is an
    honest structured `share_term` (rather than an injected `Literal`) is tied
    to the initiator's CURRENT recorded scalar.  The implication is
    deliberately quantified over the possible scalar: injected Msg1 shadows are
    all-literal and discharge it via `literal_neq_share`, while the
    origin-sensitive `lemma_sent_init_msg1_exact` supplies the witness for a
    `Sent Init` packet.

    This is the crucial symbolic bridge used at responder COMPLETION (via the run
    link).  It does NOT infer a term equality from any concrete share equality;
    it obtains the exact `share_term` from the immutable network shadow (the
    initiator's honest Msg1, selected by the run-link index) and this inductive
    binding. *)
let init_msg1_authbind_entry (p:product_state) (ne:net_entry) : prop =
  match ne.ne_smsg with
  | SMsg1 a_t gx_t ->
    forall (s:BT.bytes). gx_t == share_term s ==>
      Some? p.ps_init.sh_scalar /\
      gx_t == share_term (Some?.v p.ps_init.sh_scalar)
  | _ -> True

let init_msg1_send_authbind (p:product_state) : prop =
  forall (j:nat). j < Lst.length p.ps_net ==>
    init_msg1_authbind_entry p (Lst.index p.ps_net j)

(** ═══════════════════════════════════════════════════════════════════════════
    The CONCRETE run/session-link invariants (DY-free, about `p.ps_sys`)
    ═══════════════════════════════════════════════════════════════════════════

    These four invariants are pure facts about the concrete composed system
    state: the frozen initiator→responder targeting, the two auditable Msg1
    indices' packet provenance, and the responder's own Msg2 packet provenance.
    They hold at every reachable state (preserved by every `product_step`).  At a
    completion delivery the guard `ideal_completion_link_ok` supplies the index
    EQUALITY `sys_resp_msg1_idx == sys_init_msg1_idx`; combined with the two
    immutable Msg1 packet invariants this DERIVES the concrete identity/share
    agreement — the guard never states it (audit requirement #4). *)

(** C1.  The initiator always targets the responder (frozen from `system_initial`;
    neither `ep_peer` of the initiator nor `ep_me` of the responder ever change). *)
let id_link_invariant (p:product_state) : prop =
  p.ps_sys.sys_init.ep_peer == Some p.ps_sys.sys_resp.ep_me

(** C2.  The initiator's own Msg1 packet, at the recorded `sys_init_msg1_idx`.
    Set once at `ActStart` to the honest `Sent Init` packet the initiator emits;
    the append-only network keeps it immutable. *)
let init_msg1_pkt_invariant (p:product_state) : prop =
  let c = p.ps_sys in
  match c.sys_init_msg1_idx with
  | None -> c.sys_init.ep_phase == Init_Start
  | Some k ->
    (c.sys_init.ep_phase == Init_Wait2 \/ c.sys_init.ep_phase == Init_Done) /\
    Some? c.sys_init.ep_my_share /\
    k < Lst.length c.sys_net /\
    Lst.index c.sys_net k ==
      ({ pk_msg = Msg1 c.sys_init.ep_me (Some?.v c.sys_init.ep_my_share);
         pk_origin = Sent Init })

(** C3.  The Msg1 packet the responder actually consumed, at `sys_resp_msg1_idx`.
    Set once at the responder's Msg1 delivery (from ANY origin — the attacker may
    have injected it).  It records only that the consumed packet's fields ARE the
    responder's recorded peer/peer-share; it makes NO honesty claim. *)
let resp_msg1_pkt_invariant (p:product_state) : prop =
  let c = p.ps_sys in
  match c.sys_resp_msg1_idx with
  | None -> c.sys_resp.ep_phase == Resp_Start
  | Some k ->
    (c.sys_resp.ep_phase == Resp_Wait3 \/ c.sys_resp.ep_phase == Resp_Done) /\
    Some? c.sys_resp.ep_peer /\ Some? c.sys_resp.ep_peer_share /\
    k < Lst.length c.sys_net /\
    (Lst.index c.sys_net k).pk_msg ==
      Msg1 (Some?.v c.sys_resp.ep_peer) (Some?.v c.sys_resp.ep_peer_share)

(** C4.  Every honestly-sent (`Sent Resp`) Msg2 packet carries the responder's own
    identity and own DH share.  The responder sends Msg2 exactly once (its Msg1
    delivery), so this pins the initiator's received `gy` to the responder's own
    share regardless of the run — even when the responder answered an injected
    Msg1.  Stated per packet and quantified over `sys_net` for clean append
    preservation. *)
let resp_msg2_pkt_entry (p:product_state) (pk:packet) : prop =
  match pk.pk_origin, pk.pk_msg with
  | Sent Resp, Msg2 b gy _ ->
    (p.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/ p.ps_sys.sys_resp.ep_phase == Resp_Done) /\
    Some? p.ps_sys.sys_resp.ep_my_share /\
    b == p.ps_sys.sys_resp.ep_me /\
    p.ps_sys.sys_resp.ep_my_share == Some gy
  | _, _ -> True

let resp_msg2_pkt_invariant (p:product_state) : prop =
  forall (j:nat). j < Lst.length p.ps_sys.sys_net ==>
    resp_msg2_pkt_entry p (Lst.index p.ps_sys.sys_net j)

(** The SYMBOLIC responder peer-share link (valid also for an attacker Msg1).
    After the responder consumes its Msg1, its symbolic peer share is EXACTLY the
    `gxs` field of the network shadow at `sys_resp_msg1_idx`.  For an injected
    Msg1 that `gxs` is a public `Literal` (no honesty claimed); only the run link
    at completion upgrades it to the initiator's `share_term`. *)
let resp_shadow_link (p:product_state) : prop =
  (p.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/
   p.ps_sys.sys_resp.ep_phase == Resp_Done) ==>
    Some? p.ps_sys.sys_resp_msg1_idx /\
    (let k = Some?.v p.ps_sys.sys_resp_msg1_idx in
     k < Lst.length p.ps_net /\
     Some? p.ps_resp.sh_peer_share /\
     (match (Lst.index p.ps_net k).ne_smsg with
      | SMsg1 _ gxs -> p.ps_resp.sh_peer_share == Some gxs
      | _ -> False))

(** Once the responder COMPLETES (`Resp_Done` — never merely `Resp_Wait3`), its
    symbolic peer share is exactly the initiator's trace-recorded ephemeral share.
    This is the model fact from which unconditional responder secrecy and
    completed-session key agreement are derived; it is DERIVED at responder
    completion from the run-link equality selecting the initiator's exact honest
    Msg1 shadow (via `resp_shadow_link` + `init_msg1_pkt_invariant` +
    `init_msg1_send_authbind`), with NO concrete-byte-to-symbolic inference.  It is
    deliberately NOT claimed at `Resp_Wait3`: an attacker-started `Resp_Wait3`
    (answering an injected Msg1) does not satisfy honest peer-share secrecy. *)
let responder_peer_share_invariant (p:product_state) : prop =
  (p.ps_sys.sys_resp.ep_phase == Resp_Done) ==>
    Some? p.ps_init.sh_scalar /\
    scalar_recorded p.ps_trace (Some?.v p.ps_init.sh_scalar) /\
    p.ps_resp.sh_peer_share ==
      Some (share_term (Some?.v p.ps_init.sh_scalar))

(** Initiator completion.  Under the ideal profile, once the initiator completes:
      * the CONCRETE full matching of identities and both shares, DERIVED (not
        stated) from the run link: the responder's recorded consumed-Msg1 index
        equals the initiator's own-Msg1 index, so (by `init_msg1_pkt_invariant` +
        `resp_msg1_pkt_invariant`, and the append-only network) the responder's
        peer/peer-share ARE the initiator's identity/share; the responder's own
        share is the initiator's received `gy` by `resp_msg2_pkt_invariant`; and
      * a CONNECTED responder authorization event — the responder role principal
        triggered `tag_responder_respond` over a transcript whose
          - identity component is EXACTLY `term_of_principal ini.ep_me` (this
            initiator), pinned via `resp_send_authbind` + the run link;
          - initiator-share component is EXACTLY the responder's recorded peer
            share `Some?.v p.ps_resp.sh_peer_share` (which the concrete matching
            equates, byte-for-byte, to the initiator's own share); and
          - responder-share component is EXACTLY the share the initiator now holds
            `Some?.v p.ps_init.sh_peer_share`.
    None of the three transcript components is left unconnected.  Additionally the
    initiator's peer share is EXACTLY the responder's genuine own ephemeral share
    `share_term (Some?.v p.ps_resp.sh_scalar)` — the symbolic matching of the
    completed initiator endpoint used for key agreement. *)
let init_completed_auth (p:product_state) : prop =
  (p.ps_sys.sys_init.ep_phase == Init_Done) ==>
    (let ini = p.ps_sys.sys_init in
     let res = p.ps_sys.sys_resp in
     (res.ep_phase == Resp_Wait3 \/ res.ep_phase == Resp_Done) /\
     res.ep_peer == Some ini.ep_me /\
     res.ep_peer_share == ini.ep_my_share /\
     res.ep_my_share == ini.ep_peer_share /\
     Some? p.ps_init.sh_peer_share /\
     Some? p.ps_resp.sh_peer_share /\
     Some? p.ps_resp.sh_scalar /\
     Some?.v p.ps_init.sh_peer_share == share_term (Some?.v p.ps_resp.sh_scalar) /\
     (exists (s:BT.bytes).
        Some?.v p.ps_init.sh_peer_share == share_term s /\ scalar_recorded p.ps_trace s) /\
     TB.event_triggered p.ps_trace resp_dy_principal tag_responder_respond
       (transcript_term (term_of_principal ini.ep_me)
                        (Some?.v p.ps_resp.sh_peer_share)
                        (Some?.v p.ps_init.sh_peer_share)))

(** Responder completion.  Once the responder completes:
      * the CONCRETE full matching of identities and both shares, DERIVED (not
        stated) from the run link at the Msg3 completion plus the persisted
        initiator completion: `id_link_invariant` gives `ini.ep_peer == Some
        res.ep_me`; the run link + the two Msg1 packet invariants give
        `ini.ep_my_share == res.ep_peer_share`; and the initiator's own completion
        (`init_completed_auth`, available because the guard requires `Init_Done`)
        gives `ini.ep_peer_share == res.ep_my_share`; and
      * a CONNECTED initiator authorization event — the initiator role principal
        triggered `tag_initiator_finish` over a transcript whose
          - identity component is EXACTLY `term_of_principal res.ep_me` (this
            responder), pinned via `init_send_authbind` + the run link;
          - initiator-share component is EXACTLY the initiator's genuine own
            ephemeral share `share_term (Some?.v p.ps_init.sh_scalar)`; and
          - responder-share component is EXACTLY the initiator's recorded peer
            share `Some?.v p.ps_init.sh_peer_share` (which the concrete matching
            equates, byte-for-byte, to the responder's own share).
    Msg3 carries no shares on the wire, but the auditable provenance still pins
    all three transcript components — none is left unconnected. *)
let resp_completed_auth (p:product_state) : prop =
  (p.ps_sys.sys_resp.ep_phase == Resp_Done) ==>
    (let ini = p.ps_sys.sys_init in
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
     TB.event_triggered p.ps_trace init_dy_principal tag_initiator_finish
       (transcript_term (term_of_principal res.ep_me)
                        (share_term (Some?.v p.ps_init.sh_scalar))
                        (Some?.v p.ps_init.sh_peer_share)))

(** The combined security invariant: the ideal profile, the concrete run/session
    link invariants (C1–C4), the symbolic Msg1/completion provenance bindings, the
    responder shadow link, PLUS the two completion facts. *)
let security_invariant (p:product_state) : prop =
  ideal_product_invariant p /\
  id_link_invariant p /\
  init_msg1_pkt_invariant p /\
  resp_msg1_pkt_invariant p /\
  resp_msg2_pkt_invariant p /\
  init_msg1_send_authbind p /\
  resp_shadow_link p /\
  responder_peer_share_invariant p /\
  resp_send_authbind p /\
  init_send_authbind p /\
  init_completed_auth p /\
  resp_completed_auth p

(** Every product step grows the shared trace (each `sym_extend` case only appends
    trace entries).  Dispatch mirrors `sym_extend`; the per-segment `*_facts`
    lemmas each deliver the `grows` fact. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_product_step_grows
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_step p0 ev p1 out)
    (ensures p0.ps_trace `TB.grows` p1.ps_trace)
= let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> rng_facts p0.ps_trace
  | SM.LocalEvent Sys.ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       start_facts init_dy_principal (term_of_principal c0.sys_init.ep_me)
                   (term_of_principal peer) scalar p0.ps_trace
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net && idx < Lst.length p0.ps_net then begin
      let ne0  = Lst.index p0.ps_net idx in
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg1 a gx ->
        (match p0.ps_resp.sh_pending with
         | Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
           respond_facts resp_dy_principal p0.ps_resp.sh_ltk
             (term_of_principal c0.sys_resp.ep_me) (term_of_principal a) peer_share scalar p0.ps_trace
         | None -> ())
      | Resp, Msg3 _ ->
        (match c0.sys_resp.ep_peer, p0.ps_resp.sh_key with
         | Some a, Some key -> rfinish_facts resp_dy_principal (term_of_principal a) key p0.ps_trace
         | _ -> ())
      | Init, Msg2 b gy _ ->
        (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
         | Some _xc, Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
           ifinish_facts init_dy_principal p0.ps_init.sh_ltk scalar
             (term_of_principal b) peer_share p0.ps_trace
         | _ -> ())
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) -> inject_facts (inject_smsg m) p0.ps_trace
  | _ -> ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 3a — Preserving the auditable provenance bindings
    ═══════════════════════════════════════════════════════════════════════════

    The two `*_send_authbind` predicates are inductive: initially vacuous (empty
    network), and preserved by every `product_step`.  Every non-sending step
    leaves the sender's fields frozen and either leaves the network unchanged or
    appends a shadow that does NOT carry that sender's auth metadata; the sender's
    own send establishes the one new bound entry. *)

(** The completion run/session link is a hypothesis of every delivery step (it
    sits, opaquely, inside `system_step`); expose it by revealing the guard. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_deliver_completion_link
  (p0 p1:product_state) (out:sys_output) (idx:nat) (dst:endpoint_id)
  : Lemma
    (requires
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx dst)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net)
    (ensures Sys.ideal_completion_link_ok p0.ps_sys dst (Lst.index p0.ps_sys.sys_net idx).pk_msg)
= reveal_opaque (`%Sys.ideal_completion_link_ok) Sys.ideal_completion_link_ok
#pop-options

(** ── The concrete run-link consequence.  When the responder's recorded
    consumed-Msg1 index equals the initiator's own-Msg1 index, the two Msg1 packet
    invariants force the packet at that index to be BOTH the initiator's honest
    `Msg1 ini.ep_me ini.ep_my_share` and the responder's consumed
    `Msg1 res.ep_peer res.ep_peer_share`.  Immutability of that one packet then
    yields the concrete identity/peer-share agreement — DERIVED, never stated by
    the guard. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_runlink_concrete_match (p:product_state)
  : Lemma
    (requires
       init_msg1_pkt_invariant p /\ resp_msg1_pkt_invariant p /\
       Some? p.ps_sys.sys_resp_msg1_idx /\
       p.ps_sys.sys_resp_msg1_idx == p.ps_sys.sys_init_msg1_idx)
    (ensures
       Some? p.ps_sys.sys_init.ep_my_share /\
       Some? p.ps_sys.sys_resp.ep_peer /\ Some? p.ps_sys.sys_resp.ep_peer_share /\
       (p.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/ p.ps_sys.sys_resp.ep_phase == Resp_Done) /\
       (p.ps_sys.sys_init.ep_phase == Init_Wait2 \/ p.ps_sys.sys_init.ep_phase == Init_Done) /\
       p.ps_sys.sys_resp.ep_peer == Some p.ps_sys.sys_init.ep_me /\
       p.ps_sys.sys_resp.ep_peer_share == p.ps_sys.sys_init.ep_my_share)
= let c = p.ps_sys in
  let k = Some?.v c.sys_resp_msg1_idx in
  assert (c.sys_init_msg1_idx == Some k);
  assert (Lst.index c.sys_net k ==
            ({ pk_msg = Msg1 c.sys_init.ep_me (Some?.v c.sys_init.ep_my_share);
               pk_origin = Sent Init }));
  assert ((Lst.index c.sys_net k).pk_msg ==
            Msg1 (Some?.v c.sys_resp.ep_peer) (Some?.v c.sys_resp.ep_peer_share))
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 3a — Preserving Msg1 provenance and responder peer-share agreement
    ═══════════════════════════════════════════════════════════════════════════ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_init_msg1_authbind_entry_mono
  (p0 p1:product_state) (ne:net_entry)
  : Lemma
    (requires
       init_msg1_authbind_entry p0 ne /\
       p1.ps_init.sh_scalar == p0.ps_init.sh_scalar)
    (ensures init_msg1_authbind_entry p1 ne)
= ()
#pop-options

(** Preserve every old Msg1 binding when the network is unchanged. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_init_msg1_authbind_stable (p0 p1:product_state)
  : Lemma
    (requires
       init_msg1_send_authbind p0 /\
       p1.ps_net == p0.ps_net /\
       p1.ps_init.sh_scalar == p0.ps_init.sh_scalar)
    (ensures init_msg1_send_authbind p1)
= introduce forall (j:nat).
    j < Lst.length p1.ps_net ==>
      init_msg1_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _. lemma_init_msg1_authbind_entry_mono p0 p1 (Lst.index p0.ps_net j)

(** Preserve the old prefix and append one already-bound entry. *)
let lemma_init_msg1_authbind_snoc
  (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       init_msg1_send_authbind p0 /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       init_msg1_authbind_entry p1 ne_new /\
       p1.ps_init.sh_scalar == p0.ps_init.sh_scalar)
    (ensures init_msg1_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat).
    j < Lst.length p1.ps_net ==>
      init_msg1_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      lemma_init_msg1_authbind_entry_mono p0 p1 (Lst.index p0.ps_net j)
    end else begin
      index_app_right p0.ps_net [ne_new] j;
      assert (Lst.index p1.ps_net j == ne_new)
    end
#pop-options

(** At `ActStart`, the scalar changes from `None` to `Some scalar`.  The old
    prefix cannot contain an honest structured Msg1: applying its old binding
    would imply `Some? None`.  Thus the old prefix remains vacuous, and the one
    fresh entry establishes the binding. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_init_msg1_authbind_start_snoc
  (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       init_msg1_send_authbind p0 /\
       p0.ps_init.sh_scalar == None /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       init_msg1_authbind_entry p1 ne_new)
    (ensures init_msg1_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat).
    j < Lst.length p1.ps_net ==>
      init_msg1_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      let ne = Lst.index p0.ps_net j in
      assert (init_msg1_authbind_entry p0 ne);
      (match ne.ne_smsg with
       | SMsg1 a_t gx_t ->
         introduce forall (s:BT.bytes). gx_t == share_term s ==>
           Some? p1.ps_init.sh_scalar /\
           gx_t == share_term (Some?.v p1.ps_init.sh_scalar)
         with introduce _ ==> _
         with _. assert (Some? p0.ps_init.sh_scalar)
       | _ -> ())
    end else begin
      index_app_right p0.ps_net [ne_new] j;
      assert (Lst.index p1.ps_net j == ne_new)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_init_msg1_authbind_new
  (p1:product_state) (ne_new:net_entry) (a_t scalar:BT.bytes)
  : Lemma
    (requires
       ne_new.ne_smsg == SMsg1 a_t (share_term scalar) /\
       p1.ps_init.sh_scalar == Some scalar)
    (ensures init_msg1_authbind_entry p1 ne_new)
= ()

(** An injected Msg1 contains a `Literal`, never a `share_term`; hence it does
    not acquire honest Msg1 provenance even if its concrete bytes equal an honest
    share's bytes. *)
let lemma_injected_msg1_authbind_entry
  (p:product_state) (m:dh_message) (ne:net_entry)
  : Lemma
    (requires ne.ne_smsg == inject_smsg m)
    (ensures init_msg1_authbind_entry p ne)
= match m with
  | Msg1 a gx ->
    introduce forall (s:BT.bytes). term_of_blob gx == share_term s ==>
      Some? p.ps_init.sh_scalar /\
      term_of_blob gx == share_term (Some?.v p.ps_init.sh_scalar)
    with introduce _ ==> _
    with _. literal_neq_share gx s
  | _ -> ()
#pop-options

(** Isolate the initiator-completion case from the case-exhaustive dispatcher.
    This keeps unfolding of the Msg2 `sym_extend` arm out of the quantified
    list-preservation query. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_msg1_send_authbind_init_msg2
  (p0 p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
       product_invariant p0 /\
       init_msg1_send_authbind p0 /\
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx Init)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net /\
       Msg2? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures init_msg1_send_authbind p1)
= let c0 = p0.ps_sys in
  let n = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace
    p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  assert (idx < Lst.length p0.ps_net);
  let ne0 = Lst.index p0.ps_net idx in
  match (Lst.index c0.sys_net idx).pk_msg,
        c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
  | Msg2 b gy _, Some _xc, Some scalar ->
    let peer_share =
      (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
    let transcript =
      transcript_term (term_of_principal b) (share_term scalar) peer_share in
    let ne_new = {
      ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk
                        (signonce_term (n + 1)) transcript);
      ne_pos = n + 2;
      ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share } in
    assert (p1.ps_net == Lst.append p0.ps_net [ne_new]);
    assert (init_msg1_authbind_entry p1 ne_new);
    assert (p1.ps_init.sh_scalar == p0.ps_init.sh_scalar);
    lemma_init_msg1_authbind_snoc p0 p1 ne_new
  | _, _, _ -> ()
#pop-options

(** One-step preservation of the initiator's Msg1 send binding. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_msg1_send_authbind_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires
       product_invariant p0 /\
       init_msg1_send_authbind p0 /\
       product_step p0 ev p1 out)
    (ensures init_msg1_send_authbind p1)
= let c0 = p0.ps_sys in
  let n  = TB.trace_length p0.ps_trace in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) ->
    assert (p1.ps_net == p0.ps_net);
    assert (p1.ps_init.sh_scalar == p0.ps_init.sh_scalar);
    lemma_init_msg1_authbind_stable p0 p1
  | SM.LocalEvent Sys.ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       let ne_new = {
         ne_smsg = SMsg1 (term_of_principal c0.sys_init.ep_me) (share_term scalar);
         ne_pos = n + 1; ne_auth = NoAuth } in
       assert (p0.ps_init.sh_scalar == None);
       assert (p1.ps_net == Lst.append p0.ps_net [ne_new]);
       assert (p1.ps_init.sh_scalar == Some scalar);
       lemma_init_msg1_authbind_new p1 ne_new
         (term_of_principal c0.sys_init.ep_me) scalar;
       lemma_init_msg1_authbind_start_snoc p0 p1 ne_new
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net && idx < Lst.length p0.ps_net then begin
      let ne0  = Lst.index p0.ps_net idx in
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg1 a gx ->
        (match p0.ps_resp.sh_pending with
         | Some scalar ->
           let peer_share =
             (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
           let transcript =
             transcript_term (term_of_principal a) peer_share (share_term scalar) in
           let ne_new = {
             ne_smsg = SMsg2 (term_of_principal c0.sys_resp.ep_me) (share_term scalar)
                         (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
             ne_pos = n + 2;
             ne_auth = RespAuth (term_of_principal a) peer_share } in
           assert (p1.ps_net == Lst.append p0.ps_net [ne_new]);
           assert (init_msg1_authbind_entry p1 ne_new);
           assert (p1.ps_init.sh_scalar == p0.ps_init.sh_scalar);
           lemma_init_msg1_authbind_snoc p0 p1 ne_new
         | None -> ())
      | Resp, Msg3 _ ->
        assert (p1.ps_net == p0.ps_net);
        assert (p1.ps_init.sh_scalar == p0.ps_init.sh_scalar);
        lemma_init_msg1_authbind_stable p0 p1
      | Init, Msg2 _ _ _ ->
        lemma_init_msg1_send_authbind_init_msg2 p0 p1 out idx
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) ->
    let ne_new = { ne_smsg = inject_smsg m; ne_pos = n; ne_auth = NoAuth } in
    lemma_injected_msg1_authbind_entry p1 m ne_new;
    assert (p1.ps_net == Lst.append p0.ps_net [ne_new]);
    assert (p1.ps_init.sh_scalar == p0.ps_init.sh_scalar);
    lemma_init_msg1_authbind_snoc p0 p1 ne_new
  | _ -> ()
#pop-options

(** Establish the responder peer-share invariant at COMPLETION (`Resp_Wait3 ->
    Resp_Done`, the Msg3 delivery).  The completion guard supplies the run link
    `sys_resp_msg1_idx == sys_init_msg1_idx`; `init_msg1_pkt_invariant` makes the
    packet at that shared index the initiator's honest `Sent Init` Msg1;
    `net_entry_coherent` + `lemma_sent_init_msg1_exact` expose that packet's exact
    structured shadow; `resp_shadow_link` says the responder's symbolic peer share
    IS that shadow's `gxs`; and `init_msg1_send_authbind` ties `gxs` to the
    initiator scalar.  No concrete-byte-to-symbolic inference is used. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_responder_peer_share_establish
  (p0 p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
       security_invariant p0 /\
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx Resp)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net /\
       Msg3? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures responder_peer_share_invariant p1)
= let c0 = p0.ps_sys in
  lemma_product_step_grows p0 (SM.LocalEvent (Sys.ActDeliver idx Resp)) p1 out;
  reveal_opaque (`%Sys.ideal_completion_link_ok) Sys.ideal_completion_link_ok;
  lemma_deliver_completion_link p0 p1 out idx Resp;
  lemma_delivery_projects_local c0 p1.ps_sys idx Resp out;
  assert (c0.sys_resp.ep_phase == Resp_Wait3);
  assert (wf p0);
  assert (resp_repr c0.sys_resp p0.ps_resp);
  (* the Msg3 delivery leaves both shadows unchanged and advances the responder *)
  assert (p1.ps_init == p0.ps_init);
  assert (p1.ps_resp == p0.ps_resp);
  assert (p1.ps_sys.sys_resp.ep_phase == Resp_Done);
  assert (Some? c0.sys_resp_msg1_idx /\ c0.sys_resp_msg1_idx == c0.sys_init_msg1_idx);
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let k = Some?.v c0.sys_resp_msg1_idx in
  (* resp_shadow_link (Resp_Wait3): the shadow at k carries the responder peer share *)
  assert (k < Lst.length p0.ps_net /\ Some? p0.ps_resp.sh_peer_share);
  (* C2: the honest Sent Init Msg1 packet at k *)
  assert (c0.sys_init_msg1_idx == Some k);
  let pk = Lst.index c0.sys_net k in
  assert (pk == ({ pk_msg = Msg1 c0.sys_init.ep_me (Some?.v c0.sys_init.ep_my_share);
                   pk_origin = Sent Init }));
  let ne0 = Lst.index p0.ps_net k in
  net_coherent_index c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk k;
  lemma_sent_init_msg1_exact p0.ps_init p0.ps_resp pk ne0 p0.ps_trace;
  assert (init_msg1_authbind_entry p0 ne0);
  (match ne0.ne_smsg with
   | SMsg1 a_t gxs ->
     assert (p0.ps_resp.sh_peer_share == Some gxs);
     eliminate exists (s:BT.bytes). gxs == share_term s /\ scalar_recorded p0.ps_trace s
     returns responder_peer_share_invariant p1
     with _pf.
       (assert (Some? p0.ps_init.sh_scalar);
        assert (gxs == share_term (Some?.v p0.ps_init.sh_scalar));
        assert (scalar_recorded p0.ps_trace (Some?.v p0.ps_init.sh_scalar));
        scalar_recorded_grows p0.ps_trace p1.ps_trace (Some?.v p0.ps_init.sh_scalar);
        assert (p1.ps_init.sh_scalar == p0.ps_init.sh_scalar);
        assert (p1.ps_resp.sh_peer_share == Some gxs);
        assert (p1.ps_sys.sys_resp.ep_phase == Resp_Done))
   | _ -> ())
#pop-options

(** Persistence.  Once completed, the responder's peer share and the initiator
    scalar are frozen and events persist; the invariant is only claimed at
    `Resp_Done`, so the frozen-field hypotheses are needed only there. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_responder_peer_share_persist (p0 p1:product_state)
  : Lemma
    (requires
       responder_peer_share_invariant p0 /\
       (p1.ps_sys.sys_resp.ep_phase == Resp_Done ==>
          (p0.ps_sys.sys_resp.ep_phase == Resp_Done /\
           p1.ps_init.sh_scalar == p0.ps_init.sh_scalar /\
           p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share)) /\
       p0.ps_trace `TB.grows` p1.ps_trace)
    (ensures responder_peer_share_invariant p1)
= if p1.ps_sys.sys_resp.ep_phase = Resp_Done
   then scalar_recorded_grows p0.ps_trace p1.ps_trace (Some?.v p0.ps_init.sh_scalar)
   else ()
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_responder_peer_share_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires security_invariant p0 /\ product_step p0 ev p1 out)
    (ensures responder_peer_share_invariant p1)
= lemma_product_step_grows p0 ev p1 out;
  let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActDeliver idx Resp) ->
    if idx < Lst.length c0.sys_net then
      (match (Lst.index c0.sys_net idx).pk_msg with
       | Msg3 _ -> lemma_responder_peer_share_establish p0 p1 out idx
       | Msg1 _ _ ->
         (* responder becomes Resp_Wait3; the Resp_Done invariant is vacuous *)
         lemma_delivery_projects_local c0 p1.ps_sys idx Resp out;
         assert (p1.ps_sys.sys_resp.ep_phase == Resp_Wait3);
         lemma_responder_peer_share_persist p0 p1
       | _ -> lemma_responder_peer_share_persist p0 p1)
    else ()
  | SM.LocalEvent Sys.ActStart ->
    (* at ActStart the initiator is Init_Start, so its scalar shadow is None;
       hence (by responder_peer_share_invariant p0) the responder is not Resp_Done,
       and it is unchanged, so p1 is not Resp_Done either — vacuous *)
    assert (c0.sys_init.ep_phase == Init_Start);
    assert (init_repr c0.sys_init p0.ps_init);
    assert (p0.ps_init.sh_scalar == None);
    lemma_responder_peer_share_persist p0 p1
  | _ -> lemma_responder_peer_share_persist p0 p1
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 3a′ — Preserving the concrete run/session-link invariants (C1–C4)
    ═══════════════════════════════════════════════════════════════════════════ *)

(** C1.  `sys_init.ep_peer` and `sys_resp.ep_me` are frozen by every step, so the
    initiator→responder targeting persists. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_frozen_peer_me (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_step p0 ev p1 out)
    (ensures
       p1.ps_sys.sys_init.ep_peer == p0.ps_sys.sys_init.ep_peer /\
       p1.ps_sys.sys_resp.ep_me == p0.ps_sys.sys_resp.ep_me)
= let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent Sys.ActStart -> lemma_start_projects_local c0 p1.ps_sys out
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net then lemma_delivery_projects_local c0 p1.ps_sys idx dst out else ()
  | _ -> ()

let lemma_id_link_step (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires id_link_invariant p0 /\ product_step p0 ev p1 out)
    (ensures id_link_invariant p1)
= lemma_frozen_peer_me p0 ev p1 out
#pop-options

(** C2.  The initiator's own Msg1 packet provenance.  `ActStart` establishes it;
    every later step freezes `sys_init.ep_me`/`ep_my_share` and `sys_init_msg1_idx`
    and leaves the packet at that index unchanged (append-only network). *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_msg1_pkt_step (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires init_msg1_pkt_invariant p0 /\ product_step p0 ev p1 out)
    (ensures init_msg1_pkt_invariant p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  match ev with
  | SM.LocalEvent Sys.ActStart ->
    lemma_start_projects_local c0 c1 out;
    (* the initiator advances to Init_Wait2, sets ep_my_share, and appends its
       own Sent Init Msg1 at index (length c0.sys_net) *)
    let pkt = { pk_msg = Msg1 c1.sys_init.ep_me (Some?.v c1.sys_init.ep_my_share);
                pk_origin = Sent Init } in
    assert (out.SM.so_wire_outputs == [ Msg1 c1.sys_init.ep_me (Some?.v c1.sys_init.ep_my_share) ]);
    assert (c1.sys_net == Lst.append c0.sys_net [ pkt ]);
    append_length_l c0.sys_net [ pkt ];
    index_app_right c0.sys_net [ pkt ] (Lst.length c0.sys_net);
    assert (c1.sys_init_msg1_idx == Some (Lst.length c0.sys_net));
    assert (Lst.index c1.sys_net (Lst.length c0.sys_net) == pkt)
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    (match c0.sys_init_msg1_idx with
     | None ->
       (* init is Init_Start; it stays Init_Start unless dst = Init (impossible from
          Init_Start), so the None case persists *)
       if idx < Lst.length c0.sys_net then lemma_delivery_projects_local c0 c1 idx dst out else ()
     | Some k ->
       lemma_frozen_peer_me p0 ev p1 out;
       assert (c1.sys_init_msg1_idx == Some k);
       assert (k < Lst.length c0.sys_net);
       (* net is either unchanged (Resp Msg3) or an append; in all cases the packet
          at k < length c0.sys_net is preserved *)
       (match dst with
        | Init ->
          lemma_delivery_projects_local c0 c1 idx Init out;
          assert (c1.sys_net == append_honest c0.sys_net Init out.SM.so_wire_outputs);
          index_app_left c0.sys_net (sent_packets Init out.SM.so_wire_outputs) k
        | Resp ->
          (match (Lst.index c0.sys_net idx).pk_msg with
           | Msg1 _ _ ->
             assert (c1.sys_net == append_honest c0.sys_net Resp out.SM.so_wire_outputs);
             index_app_left c0.sys_net (sent_packets Resp out.SM.so_wire_outputs) k
           | _ ->
             assert (c1.sys_net == append_honest c0.sys_net Resp out.SM.so_wire_outputs);
             index_app_left c0.sys_net (sent_packets Resp out.SM.so_wire_outputs) k)))
  | SM.LocalEvent (Sys.ActInject m) ->
    (match c0.sys_init_msg1_idx with
     | None -> ()
     | Some k ->
       assert (c1.sys_net == Lst.append c0.sys_net [ { pk_msg = m; pk_origin = Injected } ]);
       index_app_left c0.sys_net [ { pk_msg = m; pk_origin = Injected } ] k)
  | _ -> ()
#pop-options

(** C3.  The responder's consumed Msg1 packet provenance.  The Msg1 delivery
    establishes it; every later step freezes `sys_resp.ep_peer`/`ep_peer_share` and
    `sys_resp_msg1_idx` and preserves the packet at that index. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_msg1_pkt_step (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires resp_msg1_pkt_invariant p0 /\ product_step p0 ev p1 out)
    (ensures resp_msg1_pkt_invariant p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActDeliver idx Resp) ->
    if idx < Lst.length c0.sys_net then begin
      lemma_delivery_projects_local c0 c1 idx Resp out;
      match (Lst.index c0.sys_net idx).pk_msg with
      | Msg1 a gx ->
        (* establish: consumed packet is at idx, responder records a / gx *)
        assert (c1.sys_resp_msg1_idx == Some idx);
        assert (c1.sys_net == append_honest c0.sys_net Resp out.SM.so_wire_outputs);
        index_app_left c0.sys_net (sent_packets Resp out.SM.so_wire_outputs) idx;
        assert (Lst.index c1.sys_net idx == Lst.index c0.sys_net idx);
        assert (c1.sys_resp.ep_peer == Some a);
        assert (c1.sys_resp.ep_peer_share == Some gx)
      | _ ->
        (* Msg3: responder was Resp_Wait3 (so idx invariant Some k) -> Resp_Done;
           net unchanged, peer/peer_share/idx frozen *)
        (match c0.sys_resp_msg1_idx with
         | None -> ()
         | Some k ->
           assert (c1.sys_resp_msg1_idx == Some k);
           assert (c1.sys_net == c0.sys_net \/
                   c1.sys_net == append_honest c0.sys_net Resp out.SM.so_wire_outputs);
           assert (k < Lst.length c0.sys_net);
           index_app_left c0.sys_net (sent_packets Resp out.SM.so_wire_outputs) k)
    end else ()
  | SM.LocalEvent Sys.ActStart ->
    (match c0.sys_resp_msg1_idx with
     | None -> ()
     | Some k ->
       lemma_start_projects_local c0 c1 out;
       assert (c1.sys_net == append_honest c0.sys_net Init out.SM.so_wire_outputs);
       index_app_left c0.sys_net (sent_packets Init out.SM.so_wire_outputs) k)
  | SM.LocalEvent (Sys.ActDeliver idx Init) ->
    (match c0.sys_resp_msg1_idx with
     | None -> ()
     | Some k ->
       lemma_delivery_projects_local c0 c1 idx Init out;
       assert (c1.sys_net == append_honest c0.sys_net Init out.SM.so_wire_outputs);
       index_app_left c0.sys_net (sent_packets Init out.SM.so_wire_outputs) k)
  | SM.LocalEvent (Sys.ActInject m) ->
    (match c0.sys_resp_msg1_idx with
     | None -> ()
     | Some k ->
       index_app_left c0.sys_net [ { pk_msg = m; pk_origin = Injected } ] k)
  | _ -> ()
#pop-options

(** C4.  Every honestly-sent Msg2 packet carries the responder's own identity/share.
    A per-entry monotone lemma, plus stable / snoc / establish, mirroring the
    symbolic authbind machinery but on concrete packets. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_resp_msg2_pkt_entry_mono (p0 p1:product_state) (pk:packet)
  : Lemma
    (requires
       resp_msg2_pkt_entry p0 pk /\
       p1.ps_sys.sys_resp.ep_me == p0.ps_sys.sys_resp.ep_me /\
       p1.ps_sys.sys_resp.ep_my_share == p0.ps_sys.sys_resp.ep_my_share /\
       (p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase \/
        p1.ps_sys.sys_resp.ep_phase == Resp_Done))
    (ensures resp_msg2_pkt_entry p1 pk)
= ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_msg2_pkt_stable (p0 p1:product_state)
  : Lemma
    (requires
       resp_msg2_pkt_invariant p0 /\
       p1.ps_sys.sys_net == p0.ps_sys.sys_net /\
       p1.ps_sys.sys_resp.ep_me == p0.ps_sys.sys_resp.ep_me /\
       p1.ps_sys.sys_resp.ep_my_share == p0.ps_sys.sys_resp.ep_my_share /\
       (p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase \/
        p1.ps_sys.sys_resp.ep_phase == Resp_Done))
    (ensures resp_msg2_pkt_invariant p1)
= introduce forall (j:nat). j < Lst.length p1.ps_sys.sys_net ==>
    resp_msg2_pkt_entry p1 (Lst.index p1.ps_sys.sys_net j)
  with introduce _ ==> _
  with _. lemma_resp_msg2_pkt_entry_mono p0 p1 (Lst.index p0.ps_sys.sys_net j)

(** Append a packet that is NOT a Sent Resp Msg2 (Msg1/Msg3/injected). *)
let lemma_resp_msg2_pkt_snoc (p0 p1:product_state) (pkt:packet)
  : Lemma
    (requires
       resp_msg2_pkt_invariant p0 /\
       p1.ps_sys.sys_net == Lst.append p0.ps_sys.sys_net [pkt] /\
       ~(pkt.pk_origin == Sent Resp /\ Msg2? pkt.pk_msg) /\
       p1.ps_sys.sys_resp.ep_me == p0.ps_sys.sys_resp.ep_me /\
       p1.ps_sys.sys_resp.ep_my_share == p0.ps_sys.sys_resp.ep_my_share /\
       (p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase \/
        p1.ps_sys.sys_resp.ep_phase == Resp_Done))
    (ensures resp_msg2_pkt_invariant p1)
= append_length_l p0.ps_sys.sys_net [pkt];
  introduce forall (j:nat). j < Lst.length p1.ps_sys.sys_net ==>
    resp_msg2_pkt_entry p1 (Lst.index p1.ps_sys.sys_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_sys.sys_net then begin
      index_app_left p0.ps_sys.sys_net [pkt] j;
      lemma_resp_msg2_pkt_entry_mono p0 p1 (Lst.index p0.ps_sys.sys_net j)
    end else index_app_right p0.ps_sys.sys_net [pkt] j
#pop-options

(** Establish at the responder's Msg1 delivery: it appends its own Sent Resp Msg2,
    over its own share; before this step the responder was Resp_Start, so no prior
    Sent Resp Msg2 existed (else `resp_msg2_pkt_entry p0` would force `Resp_Wait3`/
    `Resp_Done`).  The list argument is factored into a small-context core lemma. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_resp_msg2_pkt_establish_core (p0 p1:product_state) (pkt:packet)
  : Lemma
    (requires
       resp_msg2_pkt_invariant p0 /\
       p0.ps_sys.sys_resp.ep_phase == Resp_Start /\
       p1.ps_sys.sys_net == Lst.append p0.ps_sys.sys_net [pkt] /\
       resp_msg2_pkt_entry p1 pkt)
    (ensures resp_msg2_pkt_invariant p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  append_length_l c0.sys_net [ pkt ];
  introduce forall (j:nat). j < Lst.length c1.sys_net ==>
    resp_msg2_pkt_entry p1 (Lst.index c1.sys_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length c0.sys_net then begin
      index_app_left c0.sys_net [ pkt ] j;
      (* the old packet is not a Sent Resp Msg2 (responder was Resp_Start),
         so its p1-entry is the vacuous branch *)
      assert (resp_msg2_pkt_entry p0 (Lst.index c0.sys_net j))
    end else begin
      index_app_right c0.sys_net [ pkt ] j;
      assert (j == Lst.length c0.sys_net);
      assert (Lst.index c1.sys_net j == pkt)
    end
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_msg2_pkt_establish (p0 p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
       resp_msg2_pkt_invariant p0 /\
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx Resp)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net /\
       Msg1? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures resp_msg2_pkt_invariant p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  lemma_delivery_projects_local c0 c1 idx Resp out;
  assert (c0.sys_resp.ep_phase == Resp_Start);
  assert (c1.sys_resp.ep_phase == Resp_Wait3);
  assert (c1.sys_net == append_honest c0.sys_net Resp out.SM.so_wire_outputs);
  (match (Lst.index c0.sys_net idx).pk_msg, out.SM.so_wire_outputs with
   | Msg1 a gx, [ Msg2 b gy sigB ] ->
     let pkt = { pk_msg = Msg2 b gy sigB; pk_origin = Sent Resp } in
     (* responder_step: it signs with its own identity and own fresh share *)
     assert (b == c1.sys_resp.ep_me);
     assert (c1.sys_resp.ep_my_share == Some gy);
     assert (c1.sys_net == Lst.append c0.sys_net [ pkt ]);
     assert (resp_msg2_pkt_entry p1 pkt);
     lemma_resp_msg2_pkt_establish_core p0 p1 pkt
   | _, _ -> ())
#pop-options

(** One-step preservation of C4, dispatched on the step shape. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_msg2_pkt_step (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires resp_msg2_pkt_invariant p0 /\ product_step p0 ev p1 out)
    (ensures resp_msg2_pkt_invariant p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_resp_msg2_pkt_stable p0 p1
  | SM.LocalEvent Sys.ActStart ->
    lemma_start_projects_local c0 c1 out;
    (match out.SM.so_wire_outputs with
     | [ m ] -> lemma_resp_msg2_pkt_snoc p0 p1 { pk_msg = m; pk_origin = Sent Init }
     | _ -> ())
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net then begin
      lemma_delivery_projects_local c0 c1 idx dst out;
      match dst, (Lst.index c0.sys_net idx).pk_msg with
      | Resp, Msg1 _ _ -> lemma_resp_msg2_pkt_establish p0 p1 out idx
      | Resp, Msg3 _   ->
        Lst.append_l_nil c0.sys_net;
        assert (c1.sys_net == c0.sys_net);
        lemma_resp_msg2_pkt_stable p0 p1
      | Init, Msg2 _ _ _ ->
        (match out.SM.so_wire_outputs with
         | [ m ] -> lemma_resp_msg2_pkt_snoc p0 p1 { pk_msg = m; pk_origin = Sent Init }
         | _ -> ())
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) ->
    lemma_resp_msg2_pkt_snoc p0 p1 { pk_msg = m; pk_origin = Injected }
  | _ -> ()
#pop-options

(** The responder shadow link.  Established at the responder's Msg1 delivery (its
    symbolic peer share is the shadow's `gxs` at `sys_resp_msg1_idx`), and
    persisted afterwards (index frozen, share frozen, append-only network). *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_shadow_link_establish (p0 p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
       product_invariant p0 /\
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx Resp)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net /\
       Msg1? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures resp_shadow_link p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  let n = TB.trace_length p0.ps_trace in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  net_coherent_index c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk idx;
  lemma_net_entry_coherent_tag p0.ps_init.sh_ltk p0.ps_resp.sh_ltk
    (Lst.index c0.sys_net idx) (Lst.index p0.ps_net idx) p0.ps_trace;
  let ne0 = Lst.index p0.ps_net idx in
  (match (Lst.index c0.sys_net idx).pk_msg, p0.ps_resp.sh_pending with
   | Msg1 a gx, Some scalar ->
     let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
     let transcript = transcript_term (term_of_principal a) peer_share (share_term scalar) in
     let ne_new : net_entry = {
       ne_smsg = SMsg2 (term_of_principal c0.sys_resp.ep_me) (share_term scalar)
                   (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
       ne_pos  = n + 2;
       ne_auth = RespAuth (term_of_principal a) peer_share } in
     assert (c1.sys_resp_msg1_idx == Some idx);
     assert (p1.ps_resp.sh_peer_share == Some peer_share);
     assert (c1.sys_resp.ep_phase == Resp_Wait3);
     assert (p1.ps_net == Lst.append p0.ps_net [ ne_new ]);
     append_length_l p0.ps_net [ ne_new ];
     index_app_left p0.ps_net [ ne_new ] idx;
     assert (Lst.index p1.ps_net idx == ne0)
   | _, _ -> ())
#pop-options

(** Persistence of the shadow link when the shared network prefix is preserved
    (net unchanged or extended by one entry) and the responder shadow is frozen. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_resp_shadow_link_persist (p0 p1:product_state)
  : Lemma
    (requires
       resp_shadow_link p0 /\
       p1.ps_sys.sys_resp_msg1_idx == p0.ps_sys.sys_resp_msg1_idx /\
       p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share /\
       ((p1.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/
         p1.ps_sys.sys_resp.ep_phase == Resp_Done) ==>
        (p0.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/
         p0.ps_sys.sys_resp.ep_phase == Resp_Done)) /\
       Lst.length p0.ps_net <= Lst.length p1.ps_net /\
       (forall (i:nat). i < Lst.length p0.ps_net ==>
          Lst.index p1.ps_net i == Lst.index p0.ps_net i))
    (ensures resp_shadow_link p1)
= ()
#pop-options

(** The one-entry-append prefix-preservation used by `lemma_resp_shadow_link_persist`. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_net_append_prefix (p0 p1:product_state) (ne:net_entry)
  : Lemma
    (requires p1.ps_net == Lst.append p0.ps_net [ne])
    (ensures
       Lst.length p0.ps_net <= Lst.length p1.ps_net /\
       (forall (i:nat). i < Lst.length p0.ps_net ==>
          Lst.index p1.ps_net i == Lst.index p0.ps_net i))
= append_length_l p0.ps_net [ne];
  introduce forall (i:nat). i < Lst.length p0.ps_net ==>
    Lst.index p1.ps_net i == Lst.index p0.ps_net i
  with introduce _ ==> _
  with _. index_app_left p0.ps_net [ne] i
#pop-options

(** One-step preservation of the shadow link. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_shadow_link_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_invariant p0 /\ resp_shadow_link p0 /\ product_step p0 ev p1 out)
    (ensures resp_shadow_link p1)
= let c0 = p0.ps_sys in
  let c1 = p1.ps_sys in
  let n  = TB.trace_length p0.ps_trace in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_resp_shadow_link_persist p0 p1
  | SM.LocalEvent Sys.ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       lemma_net_append_prefix p0 p1
         { ne_smsg = SMsg1 (term_of_principal c0.sys_init.ep_me) (share_term scalar);
           ne_pos = n + 1; ne_auth = NoAuth };
       lemma_resp_shadow_link_persist p0 p1
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net && idx < Lst.length p0.ps_net then begin
      let ne0  = Lst.index p0.ps_net idx in
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg1 _ _ -> lemma_resp_shadow_link_establish p0 p1 out idx
      | Resp, Msg3 _ -> lemma_resp_shadow_link_persist p0 p1
      | Init, Msg2 b gy _ ->
        (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
         | Some _xc, Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
           let transcript = transcript_term (term_of_principal b) (share_term scalar) peer_share in
           lemma_net_append_prefix p0 p1
             { ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk (signonce_term (n + 1)) transcript);
               ne_pos = n + 2;
               ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share };
           lemma_resp_shadow_link_persist p0 p1
         | _, _ -> ())
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) ->
    lemma_net_append_prefix p0 p1 { ne_smsg = inject_smsg m; ne_pos = n; ne_auth = NoAuth };
    lemma_resp_shadow_link_persist p0 p1
  | _ -> ()
#pop-options

(** A single provenance entry's predicate is monotone under freezing the sender's
    fields (its phase may only advance `Resp_Wait3 -> Resp_Done`). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_resp_authbind_entry_mono (p0 p1:product_state) (ne:net_entry)
  : Lemma
    (requires
       resp_authbind_entry p0 ne /\
       p1.ps_sys.sys_resp.ep_peer == p0.ps_sys.sys_resp.ep_peer /\
       p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share /\
       p1.ps_resp.sh_scalar == p0.ps_resp.sh_scalar /\
       (p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase \/
        p1.ps_sys.sys_resp.ep_phase == Resp_Done))
    (ensures resp_authbind_entry p1 ne)
= ()

let lemma_init_authbind_entry_mono (p0 p1:product_state) (ne:net_entry)
  : Lemma
    (requires
       init_authbind_entry p0 ne /\
       p1.ps_sys.sys_init.ep_phase == p0.ps_sys.sys_init.ep_phase /\
       p1.ps_sys.sys_init.ep_peer == p0.ps_sys.sys_init.ep_peer /\
       p1.ps_init.sh_scalar == p0.ps_init.sh_scalar /\
       p1.ps_init.sh_peer_share == p0.ps_init.sh_peer_share)
    (ensures init_authbind_entry p1 ne)
= ()
#pop-options

(** Preservation when the network is UNCHANGED and the sender's fields are frozen
    (used by the RNG draw and the responder-finish / would-be no-ops). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_resp_authbind_stable (p0 p1:product_state)
  : Lemma
    (requires
       resp_send_authbind p0 /\
       p1.ps_net == p0.ps_net /\
       p1.ps_sys.sys_resp.ep_peer == p0.ps_sys.sys_resp.ep_peer /\
       p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share /\
       p1.ps_resp.sh_scalar == p0.ps_resp.sh_scalar /\
       (p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase \/
        p1.ps_sys.sys_resp.ep_phase == Resp_Done))
    (ensures resp_send_authbind p1)
= introduce forall (j:nat). j < Lst.length p1.ps_net ==> resp_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _. lemma_resp_authbind_entry_mono p0 p1 (Lst.index p0.ps_net j)

let lemma_init_authbind_stable (p0 p1:product_state)
  : Lemma
    (requires
       init_send_authbind p0 /\
       p1.ps_net == p0.ps_net /\
       p1.ps_sys.sys_init.ep_phase == p0.ps_sys.sys_init.ep_phase /\
       p1.ps_sys.sys_init.ep_peer == p0.ps_sys.sys_init.ep_peer /\
       p1.ps_init.sh_scalar == p0.ps_init.sh_scalar /\
       p1.ps_init.sh_peer_share == p0.ps_init.sh_peer_share)
    (ensures init_send_authbind p1)
= introduce forall (j:nat). j < Lst.length p1.ps_net ==> init_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _. lemma_init_authbind_entry_mono p0 p1 (Lst.index p0.ps_net j)
#pop-options

(** Preservation when the network APPENDS a single shadow that does NOT carry the
    sender's auth metadata, and the sender's fields are frozen (used by every
    honest send / injection that is not the sender's own completion send). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_resp_authbind_snoc (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       resp_send_authbind p0 /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       ~(RespAuth? ne_new.ne_auth) /\
       p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase /\
       p1.ps_sys.sys_resp.ep_peer == p0.ps_sys.sys_resp.ep_peer /\
       p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share /\
       p1.ps_resp.sh_scalar == p0.ps_resp.sh_scalar)
    (ensures resp_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat). j < Lst.length p1.ps_net ==> resp_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      lemma_resp_authbind_entry_mono p0 p1 (Lst.index p0.ps_net j)
    end else index_app_right p0.ps_net [ne_new] j

let lemma_init_authbind_snoc (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       init_send_authbind p0 /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       ~(InitAuth? ne_new.ne_auth) /\
       p1.ps_sys.sys_init.ep_phase == p0.ps_sys.sys_init.ep_phase /\
       p1.ps_sys.sys_init.ep_peer == p0.ps_sys.sys_init.ep_peer /\
       p1.ps_init.sh_scalar == p0.ps_init.sh_scalar /\
       p1.ps_init.sh_peer_share == p0.ps_init.sh_peer_share)
    (ensures init_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat). j < Lst.length p1.ps_net ==> init_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      lemma_init_authbind_entry_mono p0 p1 (Lst.index p0.ps_net j)
    end else index_app_right p0.ps_net [ne_new] j

(** Preservation of `init_send_authbind` when the initiator itself changes phase
    but has NOT yet finished (its `ActStart`): there can be no prior `InitAuth`
    shadow, so every entry — old and the fresh non-`InitAuth` Msg1 — is vacuous. *)
let lemma_init_authbind_novac (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       init_send_authbind p0 /\
       p0.ps_sys.sys_init.ep_phase =!= Init_Done /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       ~(InitAuth? ne_new.ne_auth))
    (ensures init_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat). j < Lst.length p1.ps_net ==> init_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      assert (init_authbind_entry p0 (Lst.index p0.ps_net j));
      assert (~(InitAuth? (Lst.index p0.ps_net j).ne_auth))
    end else index_app_right p0.ps_net [ne_new] j
#pop-options

(** ── Establishing the responder's provenance binding: its Msg2 send.  The fresh
    `RespAuth` shadow pins `partner`/`peer_share`/own-share to the just-updated
    responder state; no earlier `RespAuth` can exist (the responder was in
    `Resp_Start`), so the old prefix is vacuous. *)

(** The freshly-appended auth-carrying shadow satisfies its per-entry binding —
    isolated so the entry predicate is discharged with minimal context. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_resp_authbind_new_entry
  (p1:product_state) (ne_new:net_entry) (a:principal) (scalar peer_share:BT.bytes)
  : Lemma
    (requires
       ne_new.ne_auth == RespAuth (term_of_principal a) peer_share /\
       (match ne_new.ne_smsg with SMsg2 _ gy _ -> gy == share_term scalar | _ -> True) /\
       (p1.ps_sys.sys_resp.ep_phase == Resp_Wait3 \/ p1.ps_sys.sys_resp.ep_phase == Resp_Done) /\
       p1.ps_sys.sys_resp.ep_peer == Some a /\
       p1.ps_resp.sh_peer_share == Some peer_share /\
       p1.ps_resp.sh_scalar == Some scalar)
    (ensures resp_authbind_entry p1 ne_new)
= ()

let lemma_init_authbind_new_entry
  (p1:product_state) (ne_new:net_entry) (b:principal) (scalar peer_share:BT.bytes)
  : Lemma
    (requires
       ne_new.ne_auth == InitAuth (term_of_principal b) (share_term scalar) peer_share /\
       p1.ps_sys.sys_init.ep_phase == Init_Done /\
       p1.ps_sys.sys_init.ep_peer == Some b /\
       p1.ps_init.sh_scalar == Some scalar /\
       p1.ps_init.sh_peer_share == Some peer_share)
    (ensures init_authbind_entry p1 ne_new)
= ()
#pop-options

(** Snoc of a FRESH auth-carrying shadow onto a prefix that carries NO auth of
    this role (the sender was pre-completion): the whole binding follows from the
    prefix being auth-free and the new entry satisfying its binding.  The append
    index reasoning is done here, in ISOLATION from the heavy establish context. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_resp_authbind_snoc_fresh (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       (forall (j:nat). j < Lst.length p0.ps_net ==> ~(RespAuth? (Lst.index p0.ps_net j).ne_auth)) /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       resp_authbind_entry p1 ne_new)
    (ensures resp_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat). j < Lst.length p1.ps_net ==> resp_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      assert (~(RespAuth? (Lst.index p0.ps_net j).ne_auth))
    end else begin
      index_app_right p0.ps_net [ne_new] j;
      assert (Lst.index p1.ps_net j == ne_new)
    end

let lemma_init_authbind_snoc_fresh (p0 p1:product_state) (ne_new:net_entry)
  : Lemma
    (requires
       (forall (j:nat). j < Lst.length p0.ps_net ==> ~(InitAuth? (Lst.index p0.ps_net j).ne_auth)) /\
       p1.ps_net == Lst.append p0.ps_net [ne_new] /\
       init_authbind_entry p1 ne_new)
    (ensures init_send_authbind p1)
= append_length_l p0.ps_net [ne_new];
  introduce forall (j:nat). j < Lst.length p1.ps_net ==> init_authbind_entry p1 (Lst.index p1.ps_net j)
  with introduce _ ==> _
  with _.
    if j < Lst.length p0.ps_net then begin
      index_app_left p0.ps_net [ne_new] j;
      assert (~(InitAuth? (Lst.index p0.ps_net j).ne_auth))
    end else begin
      index_app_right p0.ps_net [ne_new] j;
      assert (Lst.index p1.ps_net j == ne_new)
    end
#pop-options

(** ── Establishing the responder's provenance binding: its Msg2 send.  The fresh
    `RespAuth` shadow pins `partner`/`peer_share`/own-share to the just-updated
    responder state; no earlier `RespAuth` can exist (the responder was in
    `Resp_Start`), so the old prefix is vacuous. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_authbind_establish
  (p0 p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
       product_invariant p0 /\ resp_send_authbind p0 /\
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx Resp)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net /\
       Msg1? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures resp_send_authbind p1)
= let c0 = p0.ps_sys in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  lemma_delivery_projects_local c0 p1.ps_sys idx Resp out;
  assert (idx < Lst.length p0.ps_net);
  let ne0 = Lst.index p0.ps_net idx in
  let n   = TB.trace_length p0.ps_trace in
  (match (Lst.index c0.sys_net idx).pk_msg, p0.ps_resp.sh_pending with
   | Msg1 a gx, Some scalar ->
     let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
     let transcript = transcript_term (term_of_principal a) peer_share (share_term scalar) in
     let ne_new : net_entry = {
       ne_smsg = SMsg2 (term_of_principal c0.sys_resp.ep_me) (share_term scalar)
                   (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
       ne_pos  = n + 2;
       ne_auth = RespAuth (term_of_principal a) peer_share } in
     assert (c0.sys_resp.ep_phase == Resp_Start);
     assert (p1.ps_net == Lst.append p0.ps_net [ne_new]);
     assert (p1.ps_sys.sys_resp.ep_phase == Resp_Wait3);
     assert (p1.ps_sys.sys_resp.ep_peer == Some a);
     assert (p1.ps_resp.sh_peer_share == Some peer_share);
     assert (p1.ps_resp.sh_scalar == Some scalar);
     (* the old prefix carries no RespAuth (responder was Resp_Start) *)
     introduce forall (j:nat). j < Lst.length p0.ps_net ==> ~(RespAuth? (Lst.index p0.ps_net j).ne_auth)
     with introduce _ ==> _
     with _. assert (resp_authbind_entry p0 (Lst.index p0.ps_net j));
     lemma_resp_authbind_new_entry p1 ne_new a scalar peer_share;
     lemma_resp_authbind_snoc_fresh p0 p1 ne_new
   | _, _ -> ())
#pop-options

(** ── Establishing the initiator's provenance binding: its Msg3 (finish) send. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_authbind_establish
  (p0 p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
       product_invariant p0 /\ init_send_authbind p0 /\
       product_step p0 (SM.LocalEvent (Sys.ActDeliver idx Init)) p1 out /\
       idx < Lst.length p0.ps_sys.sys_net /\
       Msg2? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures init_send_authbind p1)
= let c0 = p0.ps_sys in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  lemma_delivery_projects_local c0 p1.ps_sys idx Init out;
  assert (idx < Lst.length p0.ps_net);
  let ne0 = Lst.index p0.ps_net idx in
  let n   = TB.trace_length p0.ps_trace in
  (match (Lst.index c0.sys_net idx).pk_msg, p0.ps_init.sh_scalar with
   | Msg2 b gy sigB, Some scalar ->
     let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
     let transcript = transcript_term (term_of_principal b) (share_term scalar) peer_share in
     let ne_new : net_entry = {
       ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk (signonce_term (n + 1)) transcript);
       ne_pos  = n + 2;
       ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share } in
     assert (c0.sys_init.ep_phase == Init_Wait2);
     assert (p1.ps_net == Lst.append p0.ps_net [ne_new]);
     assert (p1.ps_sys.sys_init.ep_phase == Init_Done);
     assert (p1.ps_sys.sys_init.ep_peer == Some b);
     assert (p1.ps_init.sh_scalar == Some scalar);
     assert (p1.ps_init.sh_peer_share == Some peer_share);
     (* the old prefix carries no InitAuth (initiator was Init_Wait2) *)
     introduce forall (j:nat). j < Lst.length p0.ps_net ==> ~(InitAuth? (Lst.index p0.ps_net j).ne_auth)
     with introduce _ ==> _
     with _. assert (init_authbind_entry p0 (Lst.index p0.ps_net j));
     lemma_init_authbind_new_entry p1 ne_new b scalar peer_share;
     lemma_init_authbind_snoc_fresh p0 p1 ne_new
   | _, _ -> ())
#pop-options

(** One-step preservation of `resp_send_authbind`: dispatch mirrors `sym_extend`.
    The responder's own Msg2 delivery establishes a fresh binding; every other
    step freezes the responder and either keeps or non-`RespAuth`-extends the
    network. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_send_authbind_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_invariant p0 /\ resp_send_authbind p0 /\ product_step p0 ev p1 out)
    (ensures resp_send_authbind p1)
= let c0 = p0.ps_sys in
  let n  = TB.trace_length p0.ps_trace in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_resp_authbind_stable p0 p1
  | SM.LocalEvent Sys.ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       lemma_resp_authbind_snoc p0 p1
         { ne_smsg = SMsg1 (term_of_principal c0.sys_init.ep_me) (share_term scalar);
           ne_pos = n + 1; ne_auth = NoAuth }
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net && idx < Lst.length p0.ps_net then begin
      let ne0  = Lst.index p0.ps_net idx in
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg1 a gx -> lemma_resp_authbind_establish p0 p1 out idx
      | Resp, Msg3 _    -> lemma_resp_authbind_stable p0 p1
      | Init, Msg2 b gy _ ->
        (match c0.sys_init.ep_scalar, p0.ps_init.sh_scalar with
         | Some _xc, Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg2 _ gys _ -> gys | _ -> term_of_blob gy) in
           let transcript = transcript_term (term_of_principal b) (share_term scalar) peer_share in
           lemma_resp_authbind_snoc p0 p1
             { ne_smsg = SMsg3 (sig_term p0.ps_init.sh_ltk (signonce_term (n + 1)) transcript);
               ne_pos = n + 2;
               ne_auth = InitAuth (term_of_principal b) (share_term scalar) peer_share }
         | _, _ -> ())
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) ->
    lemma_resp_authbind_snoc p0 p1 { ne_smsg = inject_smsg m; ne_pos = n; ne_auth = NoAuth }
  | _ -> ()
#pop-options

(** One-step preservation of `init_send_authbind`. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_send_authbind_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires product_invariant p0 /\ init_send_authbind p0 /\ product_step p0 ev p1 out)
    (ensures init_send_authbind p1)
= let c0 = p0.ps_sys in
  let n  = TB.trace_length p0.ps_trace in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_init_authbind_stable p0 p1
  | SM.LocalEvent Sys.ActStart ->
    (match c0.sys_init.ep_peer, p0.ps_init.sh_pending with
     | Some peer, Some scalar ->
       lemma_init_authbind_novac p0 p1
         { ne_smsg = SMsg1 (term_of_principal c0.sys_init.ep_me) (share_term scalar);
           ne_pos = n + 1; ne_auth = NoAuth }
     | _, _ -> ())
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net && idx < Lst.length p0.ps_net then begin
      let ne0  = Lst.index p0.ps_net idx in
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Init, Msg2 _ _ _ -> lemma_init_authbind_establish p0 p1 out idx
      | Resp, Msg3 _     -> lemma_init_authbind_stable p0 p1
      | Resp, Msg1 a gx ->
        (match p0.ps_resp.sh_pending with
         | Some scalar ->
           let peer_share = (match ne0.ne_smsg with SMsg1 _ gxs -> gxs | _ -> term_of_blob gx) in
           let transcript = transcript_term (term_of_principal a) peer_share (share_term scalar) in
           lemma_init_authbind_snoc p0 p1
             { ne_smsg = SMsg2 (term_of_principal c0.sys_resp.ep_me) (share_term scalar)
                           (sig_term p0.ps_resp.sh_ltk (signonce_term (n + 1)) transcript);
               ne_pos = n + 2;
               ne_auth = RespAuth (term_of_principal a) peer_share }
         | _ -> ())
      | _, _ -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) ->
    lemma_init_authbind_snoc p0 p1 { ne_smsg = inject_smsg m; ne_pos = n; ne_auth = NoAuth }
  | _ -> ()
#pop-options

(** ── Establishing case: the initiator completes on delivering the responder's
    Msg2.  The concrete matching is DERIVED from the run link — `lemma_deliver_
    completion_link` exposes `sys_resp_msg1_idx == sys_init_msg1_idx`, and
    `lemma_runlink_concrete_match` turns it into `res.ep_peer`/`ep_peer_share`
    agreement; `resp_msg2_pkt_invariant` gives `res.ep_my_share == Some gy`.  The
    responder's symbolic authorization over the exact `gy` the initiator now holds
    is read off the network authentication theorem applied to the delivered
    Sent-Resp Msg2. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_auth_establish
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
      security_invariant p0 /\ product_step p0 ev p1 out /\
      ev == SM.LocalEvent (Sys.ActDeliver idx Init) /\
      idx < Lst.length p0.ps_sys.sys_net /\
      Msg2? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures init_completed_auth p1)
= let c0 = p0.ps_sys in
  let pk = Lst.index c0.sys_net idx in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0 = Lst.index p0.ps_net idx in
  lemma_product_step_grows p0 ev p1 out;
  assert (pk.pk_origin == Sent Resp);
  lemma_net_responder_authorized p0 idx;
  (* run link: expose the guard, then derive the concrete peer/peer-share match *)
  reveal_opaque (`%Sys.ideal_completion_link_ok) Sys.ideal_completion_link_ok;
  lemma_deliver_completion_link p0 p1 out idx Init;
  assert (Some? c0.sys_resp_msg1_idx /\ c0.sys_resp_msg1_idx == c0.sys_init_msg1_idx);
  lemma_runlink_concrete_match p0;
  assert (c0.sys_resp.ep_peer == Some c0.sys_init.ep_me);
  assert (c0.sys_resp.ep_peer_share == c0.sys_init.ep_my_share);
  (* responder's own share matches the delivered gy (C4) *)
  assert (resp_msg2_pkt_entry p0 pk);
  (* the sender's own recorded provenance for this exact delivered Msg2 shadow *)
  assert (resp_authbind_entry p0 ne0);
  (match pk.pk_msg, ne0.ne_smsg, ne0.ne_auth with
   | Msg2 b gy sigB, SMsg2 b_t gy_t sig_t, RespAuth partner gx_t ->
     assert (TB.event_triggered p0.ps_trace resp_dy_principal tag_responder_respond
               (transcript_term partner gx_t gy_t));
     (* CONNECT the recovered event to THIS completion.  From `resp_send_authbind`:
        partner is the responder's recorded peer, gx_t its recorded peer share,
        gy_t its own genuine ephemeral share.  From the run link: the responder's
        recorded peer IS this initiator. *)
     assert (partner == term_of_principal (Some?.v c0.sys_resp.ep_peer));
     assert (gx_t == Some?.v p0.ps_resp.sh_peer_share);
     assert (gy_t == share_term (Some?.v p0.ps_resp.sh_scalar));
     assert (partner == term_of_principal c0.sys_init.ep_me);
     assert (p1.ps_sys.sys_init.ep_me == c0.sys_init.ep_me);
     assert (p1.ps_sys.sys_resp == c0.sys_resp);
     assert (p1.ps_init.sh_peer_share == Some gy_t);
     assert (Some?.v p1.ps_init.sh_peer_share == gy_t);
     assert (p1.ps_sys.sys_init.ep_peer_share == Some gy);
     assert (c0.sys_resp.ep_my_share == Some gy);      (* from resp_msg2_pkt_entry *)
     (* the connected event, at p1's trace, over p1's connected fields *)
     assert (transcript_term partner gx_t gy_t ==
             transcript_term (term_of_principal p1.ps_sys.sys_init.ep_me)
                             (Some?.v p1.ps_resp.sh_peer_share)
                             (Some?.v p1.ps_init.sh_peer_share));
     TB.event_triggered_grows p0.ps_trace p1.ps_trace resp_dy_principal
       tag_responder_respond (transcript_term partner gx_t gy_t);
     (* the initiator's peer share is the responder's genuine own ephemeral share *)
     assert (Some?.v p1.ps_init.sh_peer_share == share_term (Some?.v p1.ps_resp.sh_scalar));
     (* ... hence a genuine recorded DH share *)
     eliminate exists (s:BT.bytes). gy_t == share_term s /\ scalar_recorded p0.ps_trace s
     returns
       (exists (s:BT.bytes).
          Some?.v p1.ps_init.sh_peer_share == share_term s /\ scalar_recorded p1.ps_trace s)
     with _pf.
       (scalar_recorded_grows p0.ps_trace p1.ps_trace s;
        introduce exists (s':BT.bytes).
          Some?.v p1.ps_init.sh_peer_share == share_term s' /\ scalar_recorded p1.ps_trace s'
        with s and ())
   | _, _, _ -> ())
#pop-options

(** ── Establishing case: the responder completes on delivering the initiator's
    Msg3.  The concrete matching is DERIVED: `id_link_invariant` gives `ini.ep_peer
    == Some res.ep_me`; the run link (`lemma_runlink_concrete_match`) gives
    `ini.ep_my_share == res.ep_peer_share`; the persisted `init_completed_auth`
    gives `ini.ep_peer_share == res.ep_my_share`; and
    `lemma_responder_peer_share_establish` supplies the completed responder's
    honest peer-share equality.  The initiator's symbolic authorization comes from
    the network authentication theorem on the delivered Sent-Init Msg3. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_auth_establish
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output) (idx:nat)
  : Lemma
    (requires
      security_invariant p0 /\ product_step p0 ev p1 out /\
      ev == SM.LocalEvent (Sys.ActDeliver idx Resp) /\
      idx < Lst.length p0.ps_sys.sys_net /\
      Msg3? (Lst.index p0.ps_sys.sys_net idx).pk_msg)
    (ensures resp_completed_auth p1)
= let c0 = p0.ps_sys in
  let pk = Lst.index c0.sys_net idx in
  net_coherent_length c0.sys_net p0.ps_net p0.ps_trace p0.ps_init.sh_ltk p0.ps_resp.sh_ltk;
  let ne0 = Lst.index p0.ps_net idx in
  lemma_product_step_grows p0 ev p1 out;
  assert (pk.pk_origin == Sent Init);
  lemma_net_initiator_authorized p0 idx;
  (* run link + the honest completed responder peer share *)
  reveal_opaque (`%Sys.ideal_completion_link_ok) Sys.ideal_completion_link_ok;
  lemma_deliver_completion_link p0 p1 out idx Resp;
  assert (Some? c0.sys_resp_msg1_idx /\ c0.sys_resp_msg1_idx == c0.sys_init_msg1_idx);
  assert (c0.sys_init.ep_phase == Init_Done);
  lemma_runlink_concrete_match p0;
  assert (c0.sys_resp.ep_peer_share == c0.sys_init.ep_my_share);
  lemma_responder_peer_share_establish p0 p1 out idx;
  (* the initiator's own recorded provenance for this exact delivered Msg3 shadow *)
  assert (init_authbind_entry p0 ne0);
  (match ne0.ne_smsg, ne0.ne_auth with
   | SMsg3 sig_t, InitAuth partner gx_t gy_t ->
     assert (TB.event_triggered p0.ps_trace init_dy_principal tag_initiator_finish
               (transcript_term partner gx_t gy_t));
     (* CONNECT: `init_send_authbind` pins partner to the initiator's fixed peer,
        gx_t to the initiator's OWN genuine share, gy_t to the initiator's received
        peer share; `id_link_invariant` says that fixed peer IS this responder. *)
     assert (partner == term_of_principal (Some?.v c0.sys_init.ep_peer));
     assert (gx_t == share_term (Some?.v p0.ps_init.sh_scalar));
     assert (gy_t == Some?.v p0.ps_init.sh_peer_share);
     assert (c0.sys_init.ep_peer == Some c0.sys_resp.ep_me);
     assert (partner == term_of_principal c0.sys_resp.ep_me);
     assert (p1.ps_sys.sys_init == c0.sys_init);
     assert (p1.ps_sys.sys_resp.ep_me == c0.sys_resp.ep_me);
     assert (p1.ps_sys.sys_resp.ep_peer_share == c0.sys_resp.ep_peer_share);
     assert (p1.ps_sys.sys_resp.ep_my_share == c0.sys_resp.ep_my_share);
     assert (transcript_term partner gx_t gy_t ==
             transcript_term (term_of_principal p1.ps_sys.sys_resp.ep_me)
                             (share_term (Some?.v p1.ps_init.sh_scalar))
                             (Some?.v p1.ps_init.sh_peer_share));
     TB.event_triggered_grows p0.ps_trace p1.ps_trace init_dy_principal
       tag_initiator_finish (transcript_term partner gx_t gy_t)
   | _, _ -> ())
#pop-options

(** ── Persistence: once an endpoint has completed, its own fields and its
    (already-responded) peer's data are frozen, and events persist, so the
    completion facts carry across any further step.  Stated generically over the
    frozen-field hypotheses each non-completing step discharges. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_init_auth_persist_generic (p0 p1:product_state)
  : Lemma
    (requires
      init_completed_auth p0 /\
      p1.ps_sys.sys_init == p0.ps_sys.sys_init /\
      p1.ps_sys.sys_resp.ep_peer == p0.ps_sys.sys_resp.ep_peer /\
      p1.ps_sys.sys_resp.ep_peer_share == p0.ps_sys.sys_resp.ep_peer_share /\
      p1.ps_sys.sys_resp.ep_my_share == p0.ps_sys.sys_resp.ep_my_share /\
      (p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase \/
       p1.ps_sys.sys_resp.ep_phase == Resp_Done) /\
      p1.ps_init.sh_peer_share == p0.ps_init.sh_peer_share /\
      p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share /\
      p1.ps_resp.sh_scalar == p0.ps_resp.sh_scalar /\
      p0.ps_trace `TB.grows` p1.ps_trace)
    (ensures init_completed_auth p1)
= if p1.ps_sys.sys_init.ep_phase = Init_Done then begin
    let ini0 = p0.ps_sys.sys_init in
    (* the connected event is a SPECIFIC term over frozen fields — just persist it *)
    TB.event_triggered_grows p0.ps_trace p1.ps_trace resp_dy_principal
      tag_responder_respond
      (transcript_term (term_of_principal ini0.ep_me)
                       (Some?.v p0.ps_resp.sh_peer_share)
                       (Some?.v p0.ps_init.sh_peer_share));
    eliminate exists (s:BT.bytes).
        Some?.v p0.ps_init.sh_peer_share == share_term s /\ scalar_recorded p0.ps_trace s
    returns
      (exists (s:BT.bytes).
        Some?.v p1.ps_init.sh_peer_share == share_term s /\ scalar_recorded p1.ps_trace s)
    with _pf.
      (scalar_recorded_grows p0.ps_trace p1.ps_trace s;
       introduce exists (s':BT.bytes).
         Some?.v p1.ps_init.sh_peer_share == share_term s' /\ scalar_recorded p1.ps_trace s'
       with s and ())
  end else ()

let lemma_resp_auth_persist_generic (p0 p1:product_state)
  : Lemma
    (requires
      resp_completed_auth p0 /\
      p1.ps_sys.sys_resp.ep_phase == p0.ps_sys.sys_resp.ep_phase /\
      p1.ps_sys.sys_resp.ep_me == p0.ps_sys.sys_resp.ep_me /\
      p1.ps_sys.sys_resp.ep_peer_share == p0.ps_sys.sys_resp.ep_peer_share /\
      p1.ps_sys.sys_resp.ep_my_share == p0.ps_sys.sys_resp.ep_my_share /\
      p1.ps_sys.sys_init == p0.ps_sys.sys_init /\
      p1.ps_init.sh_scalar == p0.ps_init.sh_scalar /\
      p1.ps_init.sh_peer_share == p0.ps_init.sh_peer_share /\
      p1.ps_resp.sh_scalar == p0.ps_resp.sh_scalar /\
      p1.ps_resp.sh_peer_share == p0.ps_resp.sh_peer_share /\
      p0.ps_trace `TB.grows` p1.ps_trace)
    (ensures resp_completed_auth p1)
= if p1.ps_sys.sys_resp.ep_phase = Resp_Done then begin
    let res0 = p0.ps_sys.sys_resp in
    TB.event_triggered_grows p0.ps_trace p1.ps_trace init_dy_principal
      tag_initiator_finish
      (transcript_term (term_of_principal res0.ep_me)
                       (share_term (Some?.v p0.ps_init.sh_scalar))
                       (Some?.v p0.ps_init.sh_peer_share))
  end else ()
#pop-options

(** One-step preservation of `init_completed_auth`: the Msg2 delivery establishes
    it; the responder-finish and environment steps persist it (init frozen);
    every other step leaves the initiator un-completed (vacuous). *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_init_completed_auth_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires security_invariant p0 /\ product_step p0 ev p1 out)
    (ensures init_completed_auth p1)
= lemma_product_step_grows p0 ev p1 out;
  let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_init_auth_persist_generic p0 p1
  | SM.LocalEvent Sys.ActStart -> ()
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net then begin
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Init, Msg2 _ _ _ -> lemma_init_auth_establish p0 ev p1 out idx
      | Resp, Msg3 _     -> lemma_init_auth_persist_generic p0 p1
      | _, _             -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) -> lemma_init_auth_persist_generic p0 p1
  | _ -> ()
#pop-options

(** One-step preservation of `resp_completed_auth`: the Msg3 delivery establishes
    it; the environment steps persist it; every other step leaves the responder
    un-completed (vacuous). *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_resp_completed_auth_step
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires security_invariant p0 /\ product_step p0 ev p1 out)
    (ensures resp_completed_auth p1)
= lemma_product_step_grows p0 ev p1 out;
  let c0 = p0.ps_sys in
  match ev with
  | SM.LocalEvent (Sys.ActRng owner x) -> lemma_resp_auth_persist_generic p0 p1
  | SM.LocalEvent Sys.ActStart -> ()
  | SM.LocalEvent (Sys.ActDeliver idx dst) ->
    if idx < Lst.length c0.sys_net then begin
      let cmsg = (Lst.index c0.sys_net idx).pk_msg in
      match dst, cmsg with
      | Resp, Msg3 _     -> lemma_resp_auth_establish p0 ev p1 out idx
      | _, _             -> ()
    end else ()
  | SM.LocalEvent (Sys.ActInject m) -> lemma_resp_auth_persist_generic p0 p1
  | _ -> ()
#pop-options

(** The combined one-step preservation of the whole security invariant. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_security_step_preserves
  (p0:product_state) (ev:sys_event) (p1:product_state) (out:sys_output)
  : Lemma
    (requires security_invariant p0 /\ product_step p0 ev p1 out)
    (ensures security_invariant p1)
= ideal_product_step_preserves_invariant p0 ev p1 out;
  lemma_id_link_step p0 ev p1 out;
  lemma_init_msg1_pkt_step p0 ev p1 out;
  lemma_resp_msg1_pkt_step p0 ev p1 out;
  lemma_resp_msg2_pkt_step p0 ev p1 out;
  lemma_init_msg1_send_authbind_step p0 ev p1 out;
  lemma_resp_shadow_link_step p0 ev p1 out;
  lemma_responder_peer_share_step p0 ev p1 out;
  lemma_resp_send_authbind_step p0 ev p1 out;
  lemma_init_send_authbind_step p0 ev p1 out;
  lemma_init_completed_auth_step p0 ev p1 out;
  lemma_resp_completed_auth_step p0 ev p1 out
#pop-options

(** The security invariant holds at the initial product state: the ideal profile
    (already established) plus the concrete link invariants and completion facts,
    which are vacuous because both endpoints start un-completed (Init_Start /
    Resp_Start), the network is empty, and both Msg1 indices are `None`. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_security_initial (a b:principal)
  : Lemma (ensures security_invariant (product_initial a b))
= lemma_product_initial_ideal_invariant a b
#pop-options

(** Execution induction: every state reachable from a `security_invariant` state
    still satisfies it. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let rec lemma_security_reaches
  (a b:principal) (p0:product_state) (pt:list product_transition) (p1:product_state)
  : Lemma
    (requires security_invariant p0 /\ SM.trace_reaches (product_sm a b) p0 pt p1)
    (ensures security_invariant p1)
    (decreases pt)
= match pt with
  | [] -> ()
  | ptr :: rest ->
    lemma_security_step_preserves p0 ptr.SM.tr_event ptr.SM.tr_next_state ptr.SM.tr_output;
    lemma_security_reaches a b ptr.SM.tr_next_state rest p1
#pop-options

(** HEADLINE reachability: EVERY product execution from `product_initial a b`
    ends in a state satisfying `security_invariant` — the ideal profile PLUS the
    two completion-authentication facts.  Caller supplies ONLY the identities,
    the transition list, and the final state. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let product_reaches_security_invariant
  (a b:principal) (pt:list product_transition) (pfinal:product_state)
  : Lemma
    (requires product_execution (product_sm a b) (product_initial a b) pt pfinal)
    (ensures security_invariant pfinal)
= lemma_security_initial a b;
  lemma_security_reaches a b (product_initial a b) pt pfinal
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 3b — Headline completion-authentication theorems
    ═══════════════════════════════════════════════════════════════════════════

    Surfaced directly from `security_invariant`.  Each says: a completed endpoint
    concretely agrees with its peer on both identities and both DH shares (the
    ideal-environment matching), AND the PEER's role principal has genuinely
    triggered its authorization Event on the shared DY* trace — over a transcript
    whose identity AND both share components are CONNECTED, as exactly as the
    model can honestly support, to this completion.  The event is recovered from
    the peer's genuine `Sign` term via the trace invariant + `dh_sign_pred` (never
    the origin metadata or the toy digest); the auditable provenance bindings +
    the run link then pin its transcript fields to the completion's
    identities and shares. *)

(** INITIATOR AUTHENTICATES RESPONDER.  When the initiator has completed, the
    responder agrees on the initiator's identity and both shares, and the
    RESPONDER role principal triggered `tag_responder_respond` over the EXACT
    transcript
        (this-initiator-identity, responder's-received-peer-share, gy)
    where gy is exactly the responder share the initiator now holds, and the
    initiator-share slot is the responder's recorded peer share — which the
    concrete matching (`res.ep_peer_share == ini.ep_my_share`) equates,
    byte-for-byte, to the initiator's own share.  None of the transcript's three
    components is left unconnected. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let theorem_initiator_authenticates_responder (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_init.ep_phase == Init_Done)
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
      (* the initiator's peer share IS the responder's genuine own ephemeral share *)
      Some?.v p.ps_init.sh_peer_share == share_term (Some?.v p.ps_resp.sh_scalar) /\
      (exists (s:BT.bytes).
         Some?.v p.ps_init.sh_peer_share == share_term s /\ scalar_recorded p.ps_trace s) /\
      (* the CONNECTED responder authorization event — all three transcript
         components pinned, none existential *)
      TB.event_triggered p.ps_trace resp_dy_principal tag_responder_respond
        (transcript_term (term_of_principal ini.ep_me)
                         (Some?.v p.ps_resp.sh_peer_share)
                         (Some?.v p.ps_init.sh_peer_share))))
= ()
#pop-options

(** RESPONDER AUTHENTICATES INITIATOR.  When the responder has completed, the
    initiator has completed too, agrees on the responder's identity and both
    shares, and the INITIATOR role principal triggered `tag_initiator_finish`
    over the EXACT transcript
        (this-responder-identity, initiator's-own-genuine-share, initiator's-peer-share)
    where the responder-share slot (the initiator's received peer share) is
    equated by the concrete matching (`ini.ep_peer_share == res.ep_my_share`),
    byte-for-byte, to the responder's own share.  None of the transcript's three
    components is left unconnected. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let theorem_responder_authenticates_initiator (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_resp.ep_phase == Resp_Done)
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
      TB.event_triggered p.ps_trace init_dy_principal tag_initiator_finish
        (transcript_term (term_of_principal res.ep_me)
                         (share_term (Some?.v p.ps_init.sh_scalar))
                         (Some?.v p.ps_init.sh_peer_share))))
= ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 4 — Session-key secrecy and agreement
    ═══════════════════════════════════════════════════════════════════════════ *)

(** The DH shared secret of two honest (trace-recorded, secret-labelled)
    ephemerals is NOT publishable: its label is `secret join secret`, which is
    never corrupt, so it does not flow to `public`. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let lemma_dh_secret_not_public (tr:TB.trace) (s s':BT.bytes)
  : Lemma
    (requires scalar_recorded tr s /\ scalar_recorded tr s')
    (ensures ~(B.is_publishable #dh_sample_crypto_invariants tr (secret_term s (share_term s'))))
= eliminate exists (t:nat). s == eph_term t /\ TB.entry_at tr t (T.RandGen eph_usage eph_label eph_len)
  returns ~(B.is_publishable #dh_sample_crypto_invariants tr (secret_term s (share_term s')))
  with _pf1.
    eliminate exists (t':nat). s' == eph_term t' /\ TB.entry_at tr t' (T.RandGen eph_usage eph_label eph_len)
    returns ~(B.is_publishable #dh_sample_crypto_invariants tr (secret_term s (share_term s')))
    with _pf2.
      (lemma_rand_usage_label_of_entry tr eph_usage eph_label eph_len t;
       lemma_rand_usage_label_of_entry tr eph_usage eph_label eph_len t';
       B.get_label_dh #dh_sample_crypto_usages tr s (share_term s');
       B.get_dh_label_dh_pk #dh_sample_crypto_usages tr s';
       L.is_corrupt_join tr L.secret L.secret;
       L.is_corrupt_secret tr;
       assert (B.get_label #dh_sample_crypto_usages tr s == L.secret);
       assert (B.get_label #dh_sample_crypto_usages tr s' == L.secret);
       assert (B.get_label #dh_sample_crypto_usages tr (secret_term s (share_term s'))
               == L.secret `L.join` L.secret))
#pop-options

(** Consequently the attacker never knows that shared secret on a
    `trace_invariant` trace (contrapositive of "attacker only knows publishable
    values"). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_dh_not_attacker_known (tr:TB.trace) (s s':BT.bytes)
  : Lemma
    (requires
      scalar_recorded tr s /\ scalar_recorded tr s' /\
      TI.trace_invariant #dh_sample_protocol_invariants tr)
    (ensures ~(AK.attacker_knows tr (secret_term s (share_term s'))))
= lemma_dh_secret_not_public tr s s';
  introduce AK.attacker_knows tr (secret_term s (share_term s')) ==> False
  with _contra.
    AK.attacker_only_knows_publishable_values #dh_sample_protocol_invariants
      tr (secret_term s (share_term s'))
#pop-options

(** INITIATOR SESSION-KEY SECRECY (derived, unconditional under the ideal
    profile).  A completed initiator's session key is a DH secret of its OWN
    recorded ephemeral and a genuine recorded responder share (the latter from
    `init_completed_auth`'s honest-peer-share fact), so the DY* attacker never
    knows it. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let theorem_initiator_key_secret (p:product_state)
  : Lemma
    (requires security_invariant p /\ p.ps_sys.sys_init.ep_phase == Init_Done)
    (ensures
      Some? p.ps_init.sh_key /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key)))
= let tr = p.ps_trace in
  match p.ps_init.sh_scalar, p.ps_init.sh_peer_share, p.ps_init.sh_key with
  | Some s, Some psh, Some k ->
    assert (scalar_recorded tr s);
    assert (k == secret_term s psh);
    eliminate exists (s':BT.bytes).
        Some?.v p.ps_init.sh_peer_share == share_term s' /\ scalar_recorded tr s'
    returns ~(AK.attacker_knows tr (Some?.v p.ps_init.sh_key))
    with _pf.
      (assert (k == secret_term s (share_term s'));
       lemma_dh_not_attacker_known tr s s')
  | _, _, _ -> ()
#pop-options

(** SESSION-KEY AGREEMENT for matching key structures.  This algebraic helper is
    intentionally lower-level; the completed-session theorem below derives both
    structures from `security_invariant` rather than asking its caller for them.
    When the initiator's key has algebraic form `(s_i, g^{s_r})` and the
    responder's has `(s_r, g^{s_i})`, the two shadow keys are the SAME term by
    symbolic DH agreement. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let theorem_matching_key_agreement (p:product_state) (s_i s_r:BT.bytes)
  : Lemma
    (requires
      p.ps_init.sh_key == Some (secret_term s_i (share_term s_r)) /\
      p.ps_resp.sh_key == Some (secret_term s_r (share_term s_i)))
    (ensures p.ps_init.sh_key == p.ps_resp.sh_key)
= lemma_dh_agreement s_i s_r
#pop-options

(** COMPLETED-SESSION KEY AGREEMENT.  Both matching structures are DERIVED from
    the explicit model invariant and endpoint completion.  `init_completed_auth`
    connects the initiator's peer share to the responder scalar;
    `responder_peer_share_invariant` connects the responder's peer share to the
    initiator scalar because completion's run-link equality selects the
    initiator's exact honest Msg1 shadow.  Responder progress itself remains open
    to injected Msg1 packets.  There is no caller-supplied share, key shape, or
    scalar witness. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let theorem_completed_session_key_agreement (p:product_state)
  : Lemma
    (requires
       security_invariant p /\
       p.ps_sys.sys_init.ep_phase == Init_Done /\
       p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
       Some? p.ps_init.sh_key /\ Some? p.ps_resp.sh_key /\
       p.ps_init.sh_key == p.ps_resp.sh_key)
= assert (init_repr p.ps_sys.sys_init p.ps_init);
  assert (resp_repr p.ps_sys.sys_resp p.ps_resp);
  assert (Some? p.ps_init.sh_scalar);
  assert (Some? p.ps_resp.sh_scalar);
  let s_i = Some?.v p.ps_init.sh_scalar in
  let s_r = Some?.v p.ps_resp.sh_scalar in
  (* Both sides are derived from named invariant conjuncts. *)
  assert (p.ps_init.sh_peer_share == Some (share_term s_r));
  assert (p.ps_resp.sh_peer_share == Some (share_term s_i));
  assert (Some? p.ps_init.sh_key);
  assert (Some? p.ps_resp.sh_key);
  assert (Some?.v p.ps_init.sh_key == secret_term s_i (share_term s_r));
  assert (Some?.v p.ps_resp.sh_key == secret_term s_r (share_term s_i));
  lemma_dh_agreement s_i s_r
#pop-options

(** RESPONDER SESSION-KEY SECRECY.  A completed responder consumed the actual
    initiator Msg1, so `responder_peer_share_invariant` derives that its peer
    share is the initiator's trace-recorded `share_term`.  Endpoint coherence
    supplies the responder's own recorded scalar and exact key structure.  The
    caller supplies no matching share, key structure, or scalar witness. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let theorem_responder_key_secret (p:product_state)
  : Lemma
    (requires
      security_invariant p /\
      p.ps_sys.sys_resp.ep_phase == Resp_Done)
    (ensures
      Some? p.ps_resp.sh_key /\
      ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key)))
= assert (resp_repr p.ps_sys.sys_resp p.ps_resp);
  assert (Some? p.ps_resp.sh_scalar);
  assert (Some? p.ps_init.sh_scalar);
  assert (Some? p.ps_resp.sh_key);
  let s_r = Some?.v p.ps_resp.sh_scalar in
  let s_i = Some?.v p.ps_init.sh_scalar in
  assert (scalar_recorded p.ps_trace s_r);
  assert (scalar_recorded p.ps_trace s_i);
  assert (p.ps_resp.sh_peer_share == Some (share_term s_i));
  assert (Some?.v p.ps_resp.sh_key == secret_term s_r (share_term s_i));
  lemma_dh_not_attacker_known p.ps_trace s_r s_i
#pop-options

(** The meaningful endpoint consequences exposed by the no-witness concrete
    theorem below.  Authentication is represented by the exact connected
    `*_completed_auth` predicates defined above; secrecy and agreement are stated
    directly. *)
let endpoint_security_consequences (p:product_state) : prop =
  (p.ps_sys.sys_init.ep_phase == Init_Done ==>
     init_completed_auth p /\
     Some? p.ps_init.sh_key /\
     ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_init.sh_key))) /\
  (p.ps_sys.sys_resp.ep_phase == Resp_Done ==>
     resp_completed_auth p /\
     Some? p.ps_resp.sh_key /\
     ~(AK.attacker_knows p.ps_trace (Some?.v p.ps_resp.sh_key))) /\
  ((p.ps_sys.sys_init.ep_phase == Init_Done /\
    p.ps_sys.sys_resp.ep_phase == Resp_Done) ==>
     Some? p.ps_init.sh_key /\
     Some? p.ps_resp.sh_key /\
     p.ps_init.sh_key == p.ps_resp.sh_key)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
let lemma_security_invariant_endpoint_consequences (p:product_state)
  : Lemma
    (requires security_invariant p)
    (ensures endpoint_security_consequences p)
= if p.ps_sys.sys_init.ep_phase = Init_Done then begin
     theorem_initiator_authenticates_responder p;
     theorem_initiator_key_secret p
   end;
   if p.ps_sys.sys_resp.ep_phase = Resp_Done then begin
     theorem_responder_authenticates_initiator p;
     theorem_responder_key_secret p
   end;
   if p.ps_sys.sys_init.ep_phase = Init_Done /\
      p.ps_sys.sys_resp.ep_phase = Resp_Done
   then theorem_completed_session_key_agreement p
#pop-options

(** Direct arbitrary-reachability endpoint theorems.  Callers provide a product
    execution and completion only; these lemmas derive the invariant internally
    and return authentication / secrecy / agreement consequences directly. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10 --split_queries always"
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
= product_reaches_security_invariant a b pt p;
  theorem_initiator_authenticates_responder p;
  theorem_initiator_key_secret p

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
= product_reaches_security_invariant a b pt p;
  theorem_responder_authenticates_initiator p;
  theorem_responder_key_secret p

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
= product_reaches_security_invariant a b pt p;
  theorem_initiator_authenticates_responder p;
  theorem_responder_authenticates_initiator p;
  theorem_initiator_key_secret p;
  theorem_responder_key_secret p;
  theorem_completed_session_key_agreement p
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 5 — End-to-end theorem from a CONCRETE system execution
    ═══════════════════════════════════════════════════════════════════════════

    The caller supplies ONLY a concrete execution of `DH.Sample.System`'s state
    machine (`SM.trace_reaches` from the concrete initial state) — NO symbolic
    witnesses, trace, product state, realization, or invariant.  We invoke the
    total lift (`lemma_lift_system_execution`) to obtain the exact symbolic
    product execution, then the security-invariant reachability
    (`product_reaches_security_invariant`), and package the result: a symbolic
    product execution projecting EXACTLY onto the concrete execution, at whose
    final state the whole `security_invariant` holds AND
    `endpoint_security_consequences` directly exposes completion authentication,
    key secrecy, and completed-session agreement.  The concrete matching facts
    are also read directly off the concrete final state. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
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
        (cfinal.sys_init.ep_phase == Init_Done ==>
           cfinal.sys_resp.ep_peer == Some cfinal.sys_init.ep_me /\
           cfinal.sys_resp.ep_peer_share == cfinal.sys_init.ep_my_share /\
           cfinal.sys_resp.ep_my_share == cfinal.sys_init.ep_peer_share) /\
        (cfinal.sys_resp.ep_phase == Resp_Done ==>
           cfinal.sys_init.ep_phase == Init_Done /\
           cfinal.sys_init.ep_peer == Some cfinal.sys_resp.ep_me /\
           cfinal.sys_init.ep_my_share == cfinal.sys_resp.ep_peer_share /\
           cfinal.sys_init.ep_peer_share == cfinal.sys_resp.ep_my_share)))
= lemma_lift_system_execution a b ct cfinal;
  eliminate exists (pt:list product_transition) (pfinal:product_state).
      product_execution (product_sm a b) (product_initial a b) pt pfinal /\
      execution_projects_exactly ct pt /\
      execution_frames_project_exactly (proj (product_initial a b)) (product_initial a b) ct pt /\
      proj pfinal == cfinal
  returns (
    exists (pt':list product_transition) (pfinal':product_state).
      product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
      proj pfinal' == cfinal /\
      security_invariant pfinal' /\
      endpoint_security_consequences pfinal' /\
      (cfinal.sys_init.ep_phase == Init_Done ==>
         cfinal.sys_resp.ep_peer == Some cfinal.sys_init.ep_me /\
         cfinal.sys_resp.ep_peer_share == cfinal.sys_init.ep_my_share /\
         cfinal.sys_resp.ep_my_share == cfinal.sys_init.ep_peer_share) /\
      (cfinal.sys_resp.ep_phase == Resp_Done ==>
         cfinal.sys_init.ep_phase == Init_Done /\
         cfinal.sys_init.ep_peer == Some cfinal.sys_resp.ep_me /\
         cfinal.sys_init.ep_my_share == cfinal.sys_resp.ep_peer_share /\
         cfinal.sys_init.ep_peer_share == cfinal.sys_resp.ep_my_share))
  with _pf.
    (product_reaches_security_invariant a b pt pfinal;
     lemma_security_invariant_endpoint_consequences pfinal;
     introduce exists (pt':list product_transition) (pfinal':product_state).
       product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
       proj pfinal' == cfinal /\
       security_invariant pfinal' /\
       endpoint_security_consequences pfinal' /\
       (cfinal.sys_init.ep_phase == Init_Done ==>
          cfinal.sys_resp.ep_peer == Some cfinal.sys_init.ep_me /\
          cfinal.sys_resp.ep_peer_share == cfinal.sys_init.ep_my_share /\
          cfinal.sys_resp.ep_my_share == cfinal.sys_init.ep_peer_share) /\
       (cfinal.sys_resp.ep_phase == Resp_Done ==>
          cfinal.sys_init.ep_phase == Init_Done /\
          cfinal.sys_init.ep_peer == Some cfinal.sys_resp.ep_me /\
          cfinal.sys_init.ep_my_share == cfinal.sys_resp.ep_peer_share /\
          cfinal.sys_init.ep_peer_share == cfinal.sys_resp.ep_my_share)
     with pt pfinal and ())
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 6 — Honest-run non-vacuity witness
    ═══════════════════════════════════════════════════════════════════════════

    The general theorems above must not be vacuously true.  The composed system's
    full honest three-message run (both endpoints complete, keys agree) is a
    genuine reachable execution whose lifted final product state satisfies
    `security_invariant` AND at which BOTH completion-authentication facts hold
    NON-vacuously in their CONNECTED form: the responder's `tag_responder_respond`
    and the initiator's `tag_initiator_finish` events are BOTH genuinely present on
    the shared DY* trace over transcripts whose identity AND both share components
    are pinned to this completion, and the two endpoints' concrete session keys
    agree. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_secure_honest_run (a b:principal) (x y:dh_scalar)
  : Lemma
    (requires x =!= y)
    (ensures (
      exists (pt:list product_transition) (pfinal:product_state).
        product_execution (product_sm a b) (product_initial a b) pt pfinal /\
        proj pfinal == Sys.h_s4 a b x y /\
        security_invariant pfinal /\
        pfinal.ps_sys.sys_init.ep_phase == Init_Done /\
        pfinal.ps_sys.sys_resp.ep_phase == Resp_Done /\
        Some? pfinal.ps_init.sh_peer_share /\
        Some? pfinal.ps_resp.sh_peer_share /\
        Some? pfinal.ps_init.sh_scalar /\
        Some? pfinal.ps_resp.sh_scalar /\
        pfinal.ps_resp.sh_peer_share ==
          Some (share_term (Some?.v pfinal.ps_init.sh_scalar)) /\
        Some? pfinal.ps_init.sh_key /\
        Some? pfinal.ps_resp.sh_key /\
        pfinal.ps_init.sh_key == pfinal.ps_resp.sh_key /\
        ~(AK.attacker_knows pfinal.ps_trace (Some?.v pfinal.ps_init.sh_key)) /\
        ~(AK.attacker_knows pfinal.ps_trace (Some?.v pfinal.ps_resp.sh_key)) /\
        TB.event_triggered pfinal.ps_trace resp_dy_principal tag_responder_respond
          (transcript_term (term_of_principal pfinal.ps_sys.sys_init.ep_me)
                           (Some?.v pfinal.ps_resp.sh_peer_share)
                           (Some?.v pfinal.ps_init.sh_peer_share)) /\
        TB.event_triggered pfinal.ps_trace init_dy_principal tag_initiator_finish
          (transcript_term (term_of_principal pfinal.ps_sys.sys_resp.ep_me)
                           (share_term (Some?.v pfinal.ps_init.sh_scalar))
                           (Some?.v pfinal.ps_init.sh_peer_share)) /\
        Sys.hikey x y == Sys.hrkey x y))
= lemma_honest_system_run a b x y;
  eliminate exists (pt:list product_transition) (pfinal:product_state).
      product_execution (product_sm a b) (product_initial a b) pt pfinal /\
      execution_projects_exactly (Sys.honest_run a b x y) pt /\
      proj pfinal == Sys.h_s4 a b x y
  returns (
    exists (pt':list product_transition) (pfinal':product_state).
      product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
      proj pfinal' == Sys.h_s4 a b x y /\
      security_invariant pfinal' /\
      pfinal'.ps_sys.sys_init.ep_phase == Init_Done /\
      pfinal'.ps_sys.sys_resp.ep_phase == Resp_Done /\
      Some? pfinal'.ps_init.sh_peer_share /\
      Some? pfinal'.ps_resp.sh_peer_share /\
      Some? pfinal'.ps_init.sh_scalar /\
      Some? pfinal'.ps_resp.sh_scalar /\
      pfinal'.ps_resp.sh_peer_share ==
        Some (share_term (Some?.v pfinal'.ps_init.sh_scalar)) /\
      Some? pfinal'.ps_init.sh_key /\
      Some? pfinal'.ps_resp.sh_key /\
      pfinal'.ps_init.sh_key == pfinal'.ps_resp.sh_key /\
      ~(AK.attacker_knows pfinal'.ps_trace (Some?.v pfinal'.ps_init.sh_key)) /\
      ~(AK.attacker_knows pfinal'.ps_trace (Some?.v pfinal'.ps_resp.sh_key)) /\
      TB.event_triggered pfinal'.ps_trace resp_dy_principal tag_responder_respond
        (transcript_term (term_of_principal pfinal'.ps_sys.sys_init.ep_me)
                         (Some?.v pfinal'.ps_resp.sh_peer_share)
                         (Some?.v pfinal'.ps_init.sh_peer_share)) /\
      TB.event_triggered pfinal'.ps_trace init_dy_principal tag_initiator_finish
        (transcript_term (term_of_principal pfinal'.ps_sys.sys_resp.ep_me)
                         (share_term (Some?.v pfinal'.ps_init.sh_scalar))
                         (Some?.v pfinal'.ps_init.sh_peer_share)) /\
      Sys.hikey x y == Sys.hrkey x y)
  with _pf.
    (product_reaches_security_invariant a b pt pfinal;
     theorem_initiator_authenticates_responder pfinal;
     theorem_responder_authenticates_initiator pfinal;
    theorem_reachable_completed_session_secure a b pt pfinal;
    introduce exists (pt':list product_transition) (pfinal':product_state).
       product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
       proj pfinal' == Sys.h_s4 a b x y /\
       security_invariant pfinal' /\
       pfinal'.ps_sys.sys_init.ep_phase == Init_Done /\
       pfinal'.ps_sys.sys_resp.ep_phase == Resp_Done /\
       Some? pfinal'.ps_init.sh_peer_share /\
       Some? pfinal'.ps_resp.sh_peer_share /\
       Some? pfinal'.ps_init.sh_scalar /\
       Some? pfinal'.ps_resp.sh_scalar /\
       pfinal'.ps_resp.sh_peer_share ==
         Some (share_term (Some?.v pfinal'.ps_init.sh_scalar)) /\
       Some? pfinal'.ps_init.sh_key /\
       Some? pfinal'.ps_resp.sh_key /\
       pfinal'.ps_init.sh_key == pfinal'.ps_resp.sh_key /\
       ~(AK.attacker_knows pfinal'.ps_trace (Some?.v pfinal'.ps_init.sh_key)) /\
       ~(AK.attacker_knows pfinal'.ps_trace (Some?.v pfinal'.ps_resp.sh_key)) /\
       TB.event_triggered pfinal'.ps_trace resp_dy_principal tag_responder_respond
         (transcript_term (term_of_principal pfinal'.ps_sys.sys_init.ep_me)
                          (Some?.v pfinal'.ps_resp.sh_peer_share)
                          (Some?.v pfinal'.ps_init.sh_peer_share)) /\
       TB.event_triggered pfinal'.ps_trace init_dy_principal tag_initiator_finish
         (transcript_term (term_of_principal pfinal'.ps_sys.sys_resp.ep_me)
                          (share_term (Some?.v pfinal'.ps_init.sh_scalar))
                          (Some?.v pfinal'.ps_init.sh_peer_share)) /\
       Sys.hikey x y == Sys.hrkey x y
     with pt pfinal and ())
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    Part 7 — Active-attacker non-vacuity (injected Msg1 reaches Resp_Wait3)
    ═══════════════════════════════════════════════════════════════════════════

    `ActInject` is genuinely load-bearing.  After a responder-scalar draw the
    attacker injects a Msg1 with ARBITRARY identity/share and routes it to the
    responder, which leaves `Resp_Start` for `Resp_Wait3` and answers with an
    honest Msg2 over the ATTACKER-chosen share.  This concrete run
    (`Sys.attacker_run`) lifts to a genuine product execution that STILL satisfies
    `security_invariant` — the invariant is consistent with the active attacker,
    because it makes NO honest-peer-share/secrecy claim at `Resp_Wait3`.  In this
    state the run link is BROKEN (`sys_resp_msg1_idx = Some 0`, `sys_init_msg1_idx
    = None`), the consumed packet has `Injected` origin, and the initiator has not
    even started (`Init_Start`).  Hence `theorem_responder_key_secret` (which
    requires `Resp_Done`) does NOT apply: no authentication or key secrecy is
    claimed for the attacker-selected intermediate responder key.  The responder
    can be started / DoS'd by the network but cannot be completed without a genuine
    peer signature AND a matching run link. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let lemma_attacker_injected_msg1_nonvacuous
  (a b am:principal) (ash:dh_share) (y:dh_scalar)
  : Lemma
    (ensures (
      exists (pt:list product_transition) (pfinal:product_state).
        product_execution (product_sm a b) (product_initial a b) pt pfinal /\
        proj pfinal == Sys.a_s2 a b am ash y /\
        security_invariant pfinal /\
        (* the injected Msg1 drove the responder to Resp_Wait3 ... *)
        pfinal.ps_sys.sys_resp.ep_phase == Resp_Wait3 /\
        (* ... but not to completion, and the initiator never started *)
        pfinal.ps_sys.sys_resp.ep_phase =!= Resp_Done /\
        pfinal.ps_sys.sys_init.ep_phase == Init_Start /\
        (* the run link is broken and the consumed Msg1 was injected *)
        pfinal.ps_sys.sys_resp_msg1_idx == Some 0 /\
        pfinal.ps_sys.sys_init_msg1_idx == None /\
        (Lst.index pfinal.ps_sys.sys_net 0).pk_origin == Injected))
= Sys.lemma_attacker_run_reaches a b am ash y;
  lemma_lift_system_execution a b (Sys.attacker_run a b am ash y) (Sys.a_s2 a b am ash y);
  eliminate exists (pt:list product_transition) (pfinal:product_state).
      product_execution (product_sm a b) (product_initial a b) pt pfinal /\
      execution_projects_exactly (Sys.attacker_run a b am ash y) pt /\
      execution_frames_project_exactly (proj (product_initial a b)) (product_initial a b)
        (Sys.attacker_run a b am ash y) pt /\
      proj pfinal == Sys.a_s2 a b am ash y
  returns (
    exists (pt':list product_transition) (pfinal':product_state).
      product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
      proj pfinal' == Sys.a_s2 a b am ash y /\
      security_invariant pfinal' /\
      pfinal'.ps_sys.sys_resp.ep_phase == Resp_Wait3 /\
      pfinal'.ps_sys.sys_resp.ep_phase =!= Resp_Done /\
      pfinal'.ps_sys.sys_init.ep_phase == Init_Start /\
      pfinal'.ps_sys.sys_resp_msg1_idx == Some 0 /\
      pfinal'.ps_sys.sys_init_msg1_idx == None /\
      (Lst.index pfinal'.ps_sys.sys_net 0).pk_origin == Injected)
  with _pf.
    (product_reaches_security_invariant a b pt pfinal;
     introduce exists (pt':list product_transition) (pfinal':product_state).
       product_execution (product_sm a b) (product_initial a b) pt' pfinal' /\
       proj pfinal' == Sys.a_s2 a b am ash y /\
       security_invariant pfinal' /\
       pfinal'.ps_sys.sys_resp.ep_phase == Resp_Wait3 /\
       pfinal'.ps_sys.sys_resp.ep_phase =!= Resp_Done /\
       pfinal'.ps_sys.sys_init.ep_phase == Init_Start /\
       pfinal'.ps_sys.sys_resp_msg1_idx == Some 0 /\
       pfinal'.ps_sys.sys_init_msg1_idx == None /\
       (Lst.index pfinal'.ps_sys.sys_net 0).pk_origin == Injected
     with pt pfinal and ())
#pop-options
