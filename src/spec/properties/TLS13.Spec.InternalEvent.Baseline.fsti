module TLS13.Spec.InternalEvent.Baseline

(* ==================================================================== *)
(* Phase 0 of INTERNAL_EVENT_PLAN.md: a machine-checked characterisation *)
(* of the CURRENT coalesced-record receive semantics.                    *)
(*                                                                       *)
(* Purpose.  Phases 2-3 replace the [protected_handshake_head] flag with  *)
(* an explicit pending-plaintext structure and re-express the receive     *)
(* path as one record [WireEvent] followed by internal transitions.  That *)
(* refactor is only safe if it PRESERVES the observable behaviour of the  *)
(* present spec.  The lemmas below pin that behaviour down as proof       *)
(* obligations, so a regression shows up as a broken proof rather than as *)
(* a silently different state machine.                                    *)
(*                                                                       *)
(* Every lemma here is about [TLS13.Spec.StateMachine] as it stands       *)
(* today.  None of them is used by the production path; this module is a  *)
(* leaf, so re-checking it is cheap.                                      *)
(* ==================================================================== *)

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module T = TLS13.Types
module B = TLS13.Bytes
module W = TLS13.Wire.Spec
module R = TLS13.Record.Spec
module X = TLS13.X509.Spec
module Seq = FStar.Seq

(* -------------------------------------------------------------------- *)
(* B1.  Raw-byte accounting: a coalesced record is charged exactly once.  *)
(*                                                                       *)
(* The head step of a protected-handshake pipeline accounts for exactly   *)
(* one Application_data record on the received side and nothing on the    *)
(* sent side; every tail step accounts for no bytes at all.  This is the  *)
(* invariant that makes "one physical record = one WireEvent" the right   *)
(* target shape: the raw ledger already behaves that way.                 *)
(* -------------------------------------------------------------------- *)

val lemma_head_charges_exactly_one_record
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  (raw_sent raw_received:B.bytes)
  : Lemma
    (requires
      step.CS.protected_handshake_head /\
      CS.event_raw_delta_legal model (CS.ConnProtectedHandshake step) raw_sent raw_received)
    (ensures
      Seq.equal raw_sent B.empty /\
      CS.raw_records_exactly raw_received T.Application_data 1)

val lemma_tail_charges_nothing
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  (raw_sent raw_received:B.bytes)
  : Lemma
    (requires
      ~ step.CS.protected_handshake_head /\
      CS.event_raw_delta_legal model (CS.ConnProtectedHandshake step) raw_sent raw_received)
    (ensures
      Seq.equal raw_sent B.empty /\
      Seq.equal raw_received B.empty)

(* -------------------------------------------------------------------- *)
(* B2.  The pending-plaintext discipline.                                 *)
(*                                                                       *)
(* [set_pending_protected_handshake] is the sole writer of the pending    *)
(* buffer.  It retains the WHOLE fragment together with a parse cursor    *)
(* while a residual remains, and clears both fields the moment the cursor *)
(* reaches the end.  Phase 2's explicit pending structure must reproduce  *)
(* exactly these two cases.                                               *)
(* -------------------------------------------------------------------- *)

val lemma_pending_retained_iff_residual
  (model:CS.connection_model)
  (fragment:B.bytes)
  (parsed:nat)
  : Lemma
    (ensures (
      let m' = CS.set_pending_protected_handshake model fragment parsed in
      let bufs = m'.CS.model_handshake.CS.hs_buffers in
      if parsed < B.length fragment
      then
        Seq.equal bufs.CS.hb_encrypted_server_handshake_bytes fragment /\
        bufs.CS.hb_encrypted_server_handshake_parsed == parsed
      else CS.protected_handshake_buffer_empty m'))

(* A head step may only be taken when nothing is pending.  This is the    *)
(* precondition that decision S3 preserves: the pending structure must be *)
(* empty before a record transition, so there is never more than one      *)
(* record in flight and no queue is needed.                               *)
val lemma_head_requires_empty_pending
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires
      CS.legal_protected_handshake_step model step /\
      step.CS.protected_handshake_head)
    (ensures
      CS.protected_handshake_buffer_empty model /\
      step.CS.protected_handshake_offset == 0)

(* A tail step reads the fragment and the cursor out of the pending       *)
(* buffer rather than off the wire: it is already an INTERNAL move in     *)
(* everything but name.  This is the core evidence for decision S1.       *)
val lemma_tail_is_determined_by_state
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires
      CS.legal_protected_handshake_step model step /\
      ~ step.CS.protected_handshake_head)
    (ensures (
      let bufs = model.CS.model_handshake.CS.hs_buffers in
      Seq.equal step.CS.protected_handshake_fragment
                bufs.CS.hb_encrypted_server_handshake_bytes /\
      step.CS.protected_handshake_offset ==
        bufs.CS.hb_encrypted_server_handshake_parsed /\
      W.parse_handshake
        (Seq.slice step.CS.protected_handshake_fragment
                   step.CS.protected_handshake_offset
                   (B.length step.CS.protected_handshake_fragment)) ==
        Some (step.CS.protected_handshake_message,
              step.CS.protected_handshake_consumed)))

(* -------------------------------------------------------------------- *)
(* B3.  Termination: the parse cursor strictly advances.                  *)
(*                                                                       *)
(* Every legal step consumes at least one byte and never runs past the    *)
(* end of the fragment, so the residual is a strictly decreasing natural  *)
(* number.  Phase 3's internal-step loop inherits its variant from here.  *)
(* -------------------------------------------------------------------- *)

val lemma_cursor_strictly_advances
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires CS.legal_protected_handshake_step model step)
    (ensures (
      let offset = step.CS.protected_handshake_offset in
      let consumed = step.CS.protected_handshake_consumed in
      let flen = B.length step.CS.protected_handshake_fragment in
      offset < offset + consumed /\
      offset + consumed <= flen))

val lemma_residual_decreases
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  (stepped:CS.connection_model)
  : Lemma
    (requires
      CS.legal_protected_handshake_step model step /\
      CS.step_protected_handshake model step == Some stepped)
    (ensures (
      let flen = B.length step.CS.protected_handshake_fragment in
      let bufs = stepped.CS.model_handshake.CS.hs_buffers in
      let residual_after =
        B.length bufs.CS.hb_encrypted_server_handshake_bytes -
        bufs.CS.hb_encrypted_server_handshake_parsed in
      residual_after == flen - (step.CS.protected_handshake_offset +
                                step.CS.protected_handshake_consumed) /\
      residual_after < flen - step.CS.protected_handshake_offset))

(* -------------------------------------------------------------------- *)
(* B4.  Read-sequence accounting.                                         *)
(*                                                                       *)
(* A tail step restores [record_read] from the pre-state, so the record   *)
(* read counter advances exactly once per PHYSICAL record even when that  *)
(* record carries several messages.  [Finished] is the deliberate         *)
(* exception: it installs the application read keys, and that install     *)
(* must survive the restore.                                              *)
(* -------------------------------------------------------------------- *)

val lemma_tail_preserves_record_read
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  (stepped:CS.connection_model)
  : Lemma
    (requires
      ~ step.CS.protected_handshake_head /\
      ~ (M.Finished? step.CS.protected_handshake_message) /\
      CS.step_protected_handshake model step == Some stepped)
    (ensures
      stepped.CS.model_record.CS.record_read == model.CS.model_record.CS.record_read)

val lemma_tail_finished_keeps_stepped_record_state
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  (stepped:CS.connection_model)
  : Lemma
    (requires
      ~ step.CS.protected_handshake_head /\
      M.Finished? step.CS.protected_handshake_message /\
      CS.step_protected_handshake model step == Some stepped)
    (ensures (
      match CS.step_handshake_message model CL.Received
              step.CS.protected_handshake_message with
      | Some m' -> stepped.CS.model_record == m'.CS.model_record
      | None -> False))

(* -------------------------------------------------------------------- *)
(* B5.  The semantic fork, and its removal.                              *)
(*                                                                       *)
(* A protected record carrying EXACTLY ONE handshake message used to be   *)
(* excluded from the pipeline: the head case demanded [consumed < length  *)
(* fragment], so such a record had to be described by a                   *)
(* [ConnNetworkEvent], while a multi-message record was described by a    *)
(* head plus tails.  Two spec-level shapes for one physical event was     *)
(* the fork that INTERNAL_EVENT_PLAN.md eliminates.                       *)
(*                                                                       *)
(* These lemmas record that it is gone, from both sides: the head step    *)
(* now describes a single-message record, and the network route for such  *)
(* a message no longer exists.                                            *)
(* -------------------------------------------------------------------- *)

(* A record carrying exactly one message is a head step with no tails: the *)
(* pending buffer it leaves behind is empty.                               *)
val lemma_single_message_record_is_a_head_step
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  (stepped:CS.connection_model)
  : Lemma
    (requires
      CS.legal_protected_handshake_step model step /\
      CS.step_protected_handshake model step == Some stepped /\
      step.CS.protected_handshake_head /\
      step.CS.protected_handshake_consumed ==
        B.length step.CS.protected_handshake_fragment)
    (ensures
      CS.protected_handshake_buffer_empty stepped)

(* The other side of the fork.  The two descriptions of a single-message  *)
(* protected record -- the saturating HEAD step the implementation emits, *)
(* and the ordinary received [ConnNetworkEvent] the pairing proofs are    *)
(* written against -- denote the SAME transition.  This is what makes the *)
(* fork removable without banning either route: the spec stays            *)
(* permissive, and every proof may normalise one into the other.          *)
val lemma_single_message_routes_agree
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires
      CS.legal_protected_handshake_step model step /\
      TLS13.Spec.StateMachine.Replay.single_message_head_step_shape step)
    (ensures
      CS.legal_event model
        (TLS13.Spec.StateMachine.Replay.head_step_network_event step) /\
      CS.step_model model (CS.ConnProtectedHandshake step) ==
        CS.step_model model
          (TLS13.Spec.StateMachine.Replay.head_step_network_event step))

(* B7.  Why a three-way internal status is not enough (decision S2).      *)
(*                                                                       *)
(* Receiving [Certificate] leaves the client at [HsCertificateReceived],  *)
(* but [CertificateVerify] is only legal at [HsCertificateValidated].     *)
(* The only transition between them is the LOCAL event                    *)
(* [LocalValidateCertificate].  So immediately after the [Certificate]    *)
(* message of a coalesced flight the client has a NON-EMPTY pending       *)
(* plaintext and NO enabled internal step.                                *)
(*                                                                       *)
(* A three-way status (StepOk / no-step / error) would report that as     *)
(* quiescence, and the scheduler would read the socket in the middle of   *)
(* a record it has already received.  This is the concrete reason         *)
(* [internal_status] needs a fourth case, [InternalBlocked], distinguished *)
(* by [pi_internal_pending].                                              *)
(* -------------------------------------------------------------------- *)

val lemma_certificate_blocks_the_pipeline
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires
      model.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived /\
      M.CertificateVerify? step.CS.protected_handshake_message)
    (ensures ~ (CS.legal_protected_handshake_step model step))

(* No OTHER protected handshake message is legal there either, so the     *)
(* pipeline is genuinely stuck rather than merely stuck on this message.  *)
val lemma_no_protected_step_at_certificate_received
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires model.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived)
    (ensures ~ (CS.legal_protected_handshake_step model step))

(* The local event that unblocks it leaves the pending plaintext          *)
(* untouched, so the pipeline resumes exactly where it stopped.  This is  *)
(* what makes "blocked -> run a local action -> resume internal steps" a  *)
(* sound schedule rather than a restart.                                  *)
val lemma_validate_certificate_unblocks_and_preserves_pending
  (model:CS.connection_model)
  (peer:X.peer_identity)
  : Lemma
    (requires model.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived)
    (ensures (
      match CS.step_local_event model (CS.LocalValidateCertificate peer) with
      | Some m' ->
        m'.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated /\
        m'.CS.model_handshake.CS.hs_buffers ==
          model.CS.model_handshake.CS.hs_buffers
      | None -> False))

(* And a local event never touches the raw ledger, so interleaving it     *)
(* into a record's internal steps cannot disturb byte accounting.         *)
val lemma_local_event_charges_nothing
  (model:CS.connection_model)
  (local:CS.local_event)
  (raw_sent raw_received:B.bytes)
  : Lemma
    (requires
      CS.event_raw_delta_legal model (CS.ConnLocalEvent local) raw_sent raw_received)
    (ensures
      Seq.equal raw_sent B.empty /\
      Seq.equal raw_received B.empty)

(* -------------------------------------------------------------------- *)
(* B8.  Bridge to the Phase 0 streaming parser.                           *)
(*                                                                       *)
(* Every legal pipeline step is a [parse_handshake_stream] step on the    *)
(* residual plaintext.  Phase 2 defines the internal transition directly  *)
(* over [parse_handshake_stream]; this lemma is what makes the two agree, *)
(* and hence what makes the new definition a conservative extension of    *)
(* the old one rather than a fresh guess.                                 *)
(* -------------------------------------------------------------------- *)

val lemma_legal_step_is_a_stream_parse
  (model:CS.connection_model)
  (step:CS.protected_handshake_step)
  : Lemma
    (requires CS.legal_protected_handshake_step model step)
    (ensures
      W.parse_handshake_stream
        (Seq.slice step.CS.protected_handshake_fragment
                   step.CS.protected_handshake_offset
                   (B.length step.CS.protected_handshake_fragment)) ==
      Some (M.TlsHandshake step.CS.protected_handshake_message,
            step.CS.protected_handshake_consumed))

(* The whole-fragment parser used by the non-coalesced receive path is the *)
(* streaming parser at zero residual.  Together with B6 this shows that a  *)
(* single pipeline subsumes BOTH of today's shapes, which is the technical *)
(* content of the Phase 2 unification.                                     *)
val lemma_network_receive_is_a_saturated_stream_parse
  (fragment:B.bytes)
  (msg:M.tls_message)
  : Lemma
    (requires W.parse_tls_message T.Handshake fragment == Some msg)
    (ensures
      W.parse_handshake_stream fragment == Some (msg, B.length fragment))
