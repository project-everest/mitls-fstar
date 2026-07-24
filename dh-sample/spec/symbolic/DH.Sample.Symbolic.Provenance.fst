module DH.Sample.Symbolic.Provenance

(**
  DH.Sample.Symbolic.Provenance — the *auditable* provenance surface of the DH
  sample product model.  It discharges, as machine-checked theorems about the
  genuine DY* trace-monad segments of DH.Sample.Symbolic.Product, the structural
  facts a FUTURE authentication / secrecy invariant will consume — WITHOUT itself
  assuming any trace hygiene.

  Depends ONLY on the DY* CORE library and the standalone dh-sample symbolic
  modules.  No DY* example is referenced.

  What is certified
  -----------------
    1. ACYCLIC event/crypto order.  Every locally produced signature is preceded
       on the trace by its AUTHORIZATION event, STRICTLY before the network send
       that carries the signature term:
         * initiator finish: `Event tag_initiator_finish` at n  <  `MsgSent`
           carrying `sig_term …` at n+2  (`lemma_ifinish_authorizes_before_sign`);
         * responder respond: `Event tag_responder_respond` at n < `MsgSent`
           carrying `sig_term …` at n+2 (`lemma_respond_authorizes_before_sign`).
       Ephemeral / long-term random-generation origins are recorded on the trace
       too.  These are the strict "authorization BEFORE the cryptographic term"
       facts an acyclic invariant needs.

    2. RECEIVER COMPLETION AFTER a delivered, provenance-carrying term.  A
       receiving segment reads its delivered message with the genuine `recv_msg`,
       and (given the delivered term was a prior `MsgSent`, as network coherence
       guarantees) the receiver reads back EXACTLY that term and records its
       completion STRICTLY AFTER it (`lemma_recv_reads_prior_send`,
       `lemma_rfinish_completes_after_delivery`).  For an HONEST delivery that
       prior term is the peer's STRUCTURED signature (a genuine `Sign`), so the
       completion has sender provenance; the structural fact holds uniformly and
       is thus case-provable for a future invariant.

    3. ATTACKER INJECTION IS DY-PUBLISHABLE.  An injected message is the all-literal
       `inject_smsg m`, whose flat term is `is_publishable` on ANY trace under ANY
       crypto invariants (`lemma_inject_publishable`): sound Dolev-Yao traffic that
       asserts no cryptographic origin (a received signature is a `Literal`, never a
       `Sign`).
*)

module B   = DY.Core.Bytes
module BT  = DY.Core.Bytes.Type
module T   = DY.Core.Trace.Type
module TB  = DY.Core.Trace.Base
module Seq = FStar.Seq
module U8  = FStar.UInt8
open DY.Core.Trace.Manipulation

open DH.Sample.Types
open DH.Sample.Wire
open DH.Sample.System
open DH.Sample.Symbolic.Terms
open DH.Sample.Symbolic.Product

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10"

(** ── 1. Acyclic authorization-before-signature order ────────────────────────

    The initiator's message-3 authorization `Event` (at n+1) is STRICTLY before the
    network `MsgSent` carrying its signature term (at n+2). *)
let lemma_ifinish_authorizes_before_sign
  (mep:T.principal) (ltk scalar b_t peer_share:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let transcript = transcript_term b_t (share_term scalar) peer_share in
      let tr' = ifinish_trace mep ltk scalar b_t peer_share tr in
      TB.entry_at tr' n (T.Event mep tag_initiator_finish transcript) /\
      TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg3 (sig_term ltk (signonce_term (n + 1)) transcript)))) /\
      n < (n + 2) /\
      TB.event_triggered tr' mep tag_initiator_finish transcript))
= ifinish_facts mep ltk scalar b_t peer_share tr

(** The responder's message-2 authorization `Event` (at n) is STRICTLY before
    the network `MsgSent` carrying its signature term (at n+2).  Its ephemeral
    was recorded by a separate, earlier RNG transition. *)
let lemma_respond_authorizes_before_sign
  (mep:T.principal) (ltk me_t a_t peer_share scalar:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let transcript = transcript_term a_t peer_share (share_term scalar) in
      let tr' = respond_trace mep ltk me_t a_t peer_share scalar tr in
      TB.entry_at tr' n (T.Event mep tag_responder_respond transcript) /\
      TB.entry_at tr' (n + 1) (T.RandGen signonce_usage signonce_label signonce_len) /\
      TB.entry_at tr' (n + 2) (T.MsgSent (flatten (SMsg2 me_t (share_term scalar) (sig_term ltk (signonce_term (n + 1)) transcript)))) /\
      n < (n + 2) /\
      TB.event_triggered tr' mep tag_responder_respond transcript))
= respond_facts mep ltk me_t a_t peer_share scalar tr

(** The explicit RNG segment records the ephemeral origin before any protocol
    step can consume it. *)
let lemma_rng_origin (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let scalar = eph_term n in
      let tr' = rng_trace tr in
      TB.rand_generated_at tr' n scalar /\
      scalar_recorded tr' scalar))
= rng_facts tr;
  let n = TB.trace_length tr in
  introduce exists (t:nat).
    eph_term n == eph_term t /\
    TB.entry_at (rng_trace tr) t (T.RandGen eph_usage eph_label eph_len)
  with n and ()

(** Start consumes an already recorded scalar, authorizes, and sends Msg1. *)
let lemma_start_origins
  (mep:T.principal) (me_t peer_t scalar:BT.bytes) (tr:TB.trace)
  : Lemma
    (requires scalar_recorded tr scalar)
    (ensures (
      let n = TB.trace_length tr in
      let tr' = start_trace mep me_t peer_t scalar tr in
      scalar_recorded tr' scalar /\
      TB.entry_at tr' n (T.Event mep tag_initiate (initiate_content me_t peer_t (share_term scalar))) /\
      TB.entry_at tr' (n + 1) (T.MsgSent (flatten (SMsg1 me_t (share_term scalar)))) /\
      TB.event_triggered tr' mep tag_initiate (initiate_content me_t peer_t (share_term scalar))))
= start_facts mep me_t peer_t scalar tr;
  scalar_recorded_grows tr (start_trace mep me_t peer_t scalar tr) scalar

(** Setup records the long-term key's origin and binds it to the identity. *)
let lemma_setup_binds_identity (mep:T.principal) (me_t:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = setup_trace mep me_t tr in
      TB.rand_generated_at tr' n (ltk_term n) /\
      TB.event_triggered tr' mep tag_keygen (keygen_content me_t (vkey_term (ltk_term n)))))
= setup_facts mep me_t tr

(** The responder's completion event is recorded (its trace position is n). *)
let lemma_rfinish_completion_event (mep:T.principal) (a_t key:BT.bytes) (tr:TB.trace)
  : Lemma (ensures (
      let n = TB.trace_length tr in
      let tr' = rfinish_trace mep a_t key tr in
      TB.entry_at tr' n (T.Event mep tag_responder_finish (session_content a_t key)) /\
      TB.event_triggered tr' mep tag_responder_finish (session_content a_t key)))
= rfinish_facts mep a_t key tr

#pop-options

(** ── Exact honest-signature provenance from network coherence ──────────────

    These are deliberately stronger than "there exist some key, nonce, and
    transcript".  The key is the named role shadow's exact `sh_ltk`; the nonce
    is fixed by the send position; and the transcript is exactly the structured
    partner/share context stored at the send. *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let lemma_sent_resp_msg2_exact
  (ish rsh:endpoint_shadow) (pk:packet) (ne:net_entry) (tr:TB.trace)
  : Lemma
    (requires
      pk.pk_origin == Sent Resp /\ Msg2? pk.pk_msg /\
      net_entry_coherent ish.sh_ltk rsh.sh_ltk pk ne tr)
    (ensures (
      match pk.pk_msg, ne.ne_smsg, ne.ne_auth with
      | Msg2 b _ _, SMsg2 b_t gy_t sig_t, RespAuth partner gx_t ->
        b_t == term_of_principal b /\
        (exists (s:BT.bytes). gy_t == share_term s /\ scalar_recorded tr s) /\
        sig_t == sig_term rsh.sh_ltk
          (signonce_term (auth_nonce_pos ne.ne_pos))
          (transcript_term partner gx_t gy_t)
      | _, _, _ -> False))
= reveal_opaque (`%smsg_provenance) smsg_provenance

let lemma_sent_init_msg3_exact
  (ish rsh:endpoint_shadow) (pk:packet) (ne:net_entry) (tr:TB.trace)
  : Lemma
    (requires
      pk.pk_origin == Sent Init /\ Msg3? pk.pk_msg /\
      net_entry_coherent ish.sh_ltk rsh.sh_ltk pk ne tr)
    (ensures (
      match ne.ne_smsg, ne.ne_auth with
      | SMsg3 sig_t, InitAuth partner gx_t gy_t ->
        sig_t == sig_term ish.sh_ltk
          (signonce_term (auth_nonce_pos ne.ne_pos))
          (transcript_term partner gx_t gy_t)
      | _, _ -> False))
= reveal_opaque (`%smsg_provenance) smsg_provenance

(** A delivery reads the exact immutable `ne_smsg` recorded at the send; there
    is no re-embedding or replacement by a fresh literal. *)
let lemma_coherent_delivery_reads_exact
  (ish rsh:endpoint_shadow) (pk:packet) (ne:net_entry) (tr:TB.trace)
  : Lemma
    (requires net_entry_coherent ish.sh_ltk rsh.sh_ltk pk ne tr)
    (ensures fst (recv_msg ne.ne_pos tr) == Some (flatten ne.ne_smsg))
= reveal_opaque (`%recv_msg) recv_msg

#pop-options

(** ── 2. Receiver reads back a prior send; completion strictly after it ───────*)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"

(** The genuine `recv_msg` reads back EXACTLY the term a prior `MsgSent` put on the
    network — the faithful delivery semantics underlying every receiving segment. *)
let lemma_recv_reads_prior_send (rpos:nat) (m:BT.bytes) (tr:TB.trace)
  : Lemma
    (requires rpos < TB.trace_length tr /\ TB.entry_at tr rpos (T.MsgSent m))
    (ensures fst (recv_msg rpos tr) == Some m)
= reveal_opaque (`%recv_msg) recv_msg

(** Responder finish: reading the delivered message-3 term (a prior `MsgSent` at
    `rpos`, per network coherence) reads back EXACTLY that term, and the completion
    `Event` is recorded STRICTLY AFTER it (`rpos < trace_length tr`, and the
    completion sits at `trace_length tr`).  For an HONEST delivery the delivered
    term is the initiator's STRUCTURED signature (sender provenance). *)
let lemma_rfinish_completes_after_delivery
  (mep:T.principal) (a_t key:BT.bytes) (tr:TB.trace) (rpos:nat) (delivered:BT.bytes)
  : Lemma
    (requires rpos < TB.trace_length tr /\ TB.entry_at tr rpos (T.MsgSent delivered))
    (ensures (
      let n = TB.trace_length tr in
      let (_, tr') = rfinish_run mep a_t key tr rpos in
      fst (recv_msg rpos tr) == Some delivered /\
      TB.entry_at tr' rpos (T.MsgSent delivered) /\
      TB.entry_at tr' n (T.Event mep tag_responder_finish (session_content a_t key)) /\
      rpos < n))
= reveal_opaque (`%recv_msg) recv_msg;
  rfinish_structure mep a_t key tr rpos;
  rfinish_facts mep a_t key tr

#pop-options

(** ── 3. Attacker injection is DY-publishable ─────────────────────────────────*)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

let lemma_recv1_publishable
  (#cinvs:B.crypto_invariants) (tr:TB.trace) (a:principal) (gx:dh_share)
  : Lemma (ensures B.is_publishable tr (flatten (SMsg1 (term_of_principal a) (term_of_blob gx))))
= B.literal_to_bytes_is_publishable tr a;
  B.literal_to_bytes_is_publishable tr gx;
  B.concat_preserves_publishability tr (term_of_principal a) (term_of_blob gx)

let lemma_recv2_publishable
  (#cinvs:B.crypto_invariants) (tr:TB.trace) (b:principal) (gy:dh_share) (sigB:signature)
  : Lemma (ensures B.is_publishable tr
             (flatten (SMsg2 (term_of_principal b) (term_of_blob gy) (term_of_blob sigB))))
= B.literal_to_bytes_is_publishable tr b;
  B.literal_to_bytes_is_publishable tr gy;
  B.literal_to_bytes_is_publishable tr sigB;
  B.concat_preserves_publishability tr (term_of_blob gy) (term_of_blob sigB);
  B.concat_preserves_publishability tr (term_of_principal b)
    (B.concat (term_of_blob gy) (term_of_blob sigB))

let lemma_recv3_publishable
  (#cinvs:B.crypto_invariants) (tr:TB.trace) (sigA:signature)
  : Lemma (ensures B.is_publishable tr (flatten (SMsg3 (term_of_blob sigA))))
= B.literal_to_bytes_is_publishable tr sigA

(** The flat term the attacker injects (`inject_smsg m`) is `is_publishable` on ANY
    trace under ANY crypto invariants — it is built solely from public literals, so
    an attacker with no secret knowledge could have produced and sent it, and a
    received signature in it is a `Literal`, never a `Sign`. *)
let lemma_inject_publishable
  (#cinvs:B.crypto_invariants) (tr:TB.trace) (m:dh_message)
  : Lemma (ensures B.is_publishable tr (flatten (inject_smsg m)))
= match m with
  | Msg1 a gx      -> lemma_recv1_publishable #cinvs tr a gx
  | Msg2 b gy sigB -> lemma_recv2_publishable #cinvs tr b gy sigB
  | Msg3 sigA      -> lemma_recv3_publishable #cinvs tr sigA

#pop-options

(** ── Received material carries no forged origin (by construction) ────────────

    NOTE.  An ATTACKER-INJECTED blob (peer share or peer signature) is embedded by
    `term_of_blob = literal_to_bytes` — never one of the origin-producing builders
    (`eph_term`, `share_term`, `secret_term`, `sig_term`, `mk_rand`).  Hence the
    product structurally cannot attach a fresh or authentic origin to injected
    material, and never derives a signature origin from the deliberately weak
    concrete verifier.  A HONESTLY delivered term, by contrast, is reused verbatim
    from the sender's own `MsgSent` (a genuine `Sign`), so an honest received
    signature is never reclassified as a literal. *)
