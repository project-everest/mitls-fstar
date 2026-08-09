module TLS13.Impl.Client.Drain

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module Can = TLS13.Spec.StateMachine.Canonical
module CT = TLS13.Impl.Client.Types
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT

(**
  Internal protected-handshake drain steps.

  A protected TLS record can carry several coalesced handshake messages.  The
  receive primitive applies only the *head* message and leaves the remainder in
  the model's pending plaintext buffer; the remaining messages are delivered by
  [process_pending_protected_handshake], one internal step at a time.

  This module gives that sequence of internal steps a name and proves that it
  is *application-invisible*: a drain step consumes no wire bytes, emits no wire
  bytes, and produces neither application nor network output.  Everything a
  driver observes about a connection -- its configuration, both halves of the
  wire log, and the end-to-end invariant -- is therefore stable under draining,
  which is what lets a driver run the drain to completion without disturbing the
  correctness argument it already has for the network step.
**)

/// A single internal step: the pending buffer held an unprocessed handshake
/// message and it was applied successfully.
let drain_step (st0 st1:CS.connection_state) : prop =
  exists resp.
    CT.pending_protected_handshake_result_correct st0 st1 (Some resp) /\
    resp.CT.status == CT.StepOk

/// [n]-bounded reflexive-transitive closure of [drain_step].
let rec drain_chain (n:nat) (st0 st1:CS.connection_state)
  : Tot prop (decreases n) =
  if n = 0
  then st1 == st0
  else
    st1 == st0 \/
    (exists st'. drain_step st0 st' /\ drain_chain (n - 1) st' st1)

/// The unbounded closure, which is what callers state.
let drained (st0 st1:CS.connection_state) : prop =
  exists (n:nat). drain_chain n st0 st1

let lemma_drained_refl (st0:CS.connection_state)
  : Lemma (ensures drained st0 st0)
=
  assert (drain_chain 0 st0 st0)

let lemma_drained_step (st0 st1 st2:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1 /\ drained st1 st2)
      (ensures drained st0 st2)
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> drain_chain n st1 st2) in
  assert (drain_step st0 st1 /\ drain_chain n st1 st2);
  assert (drain_chain (n + 1) st0 st2)

#push-options "--fuel 2 --ifuel 2"
let lemma_drain_chain_refl (n:nat) (st:CS.connection_state)
  : Lemma (ensures drain_chain n st st)
=
  if n = 0 then () else ()

/// Extending a chain on the right, which is the direction an imperative drain
/// loop needs: it has already drained [st0] to [st1] and takes one more step.
let rec lemma_drain_chain_snoc
      (n:nat)
      (st0 st1 st2:CS.connection_state)
  : Lemma
      (requires drain_chain n st0 st1 /\ drain_step st1 st2)
      (ensures drain_chain (n + 1) st0 st2)
      (decreases n)
=
  if n = 0
  then lemma_drain_chain_refl 0 st2
  else
  let m : nat = n - 1 in
    eliminate
      (st1 == st0) \/
      (exists st'. drain_step st0 st' /\ drain_chain m st' st1)
    with lemma_drain_chain_refl n st2
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> drain_step st0 st' /\ drain_chain m st' st1) in
       lemma_drain_chain_snoc m st' st1 st2)
#pop-options

let lemma_drained_snoc (st0 st1 st2:CS.connection_state)
  : Lemma
      (requires drained st0 st1 /\ drain_step st1 st2)
      (ensures drained st0 st2)
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> drain_chain n st0 st1) in
  lemma_drain_chain_snoc n st0 st1 st2

(** ---------------------------------------------------------------------- *)
(** Single-step facts                                                       *)
(** ---------------------------------------------------------------------- *)

/// Extract the witnessing response and protected-handshake step of a drain
/// step.  Factored out so that each fact below is a small, separate query --
/// proving them all in one lemma makes the VC large enough to crash Z3.
let drain_step_witness (st0 st1:CS.connection_state)
  : Ghost (CT.client_response & CS.protected_handshake_step)
      (requires drain_step st0 st1)
      (ensures fun rs ->
        let (resp, step) = rs in
        resp.CT.status == CT.StepOk /\
        CT.protected_handshake_step_correct
          st0 st1 resp step B.empty B.empty B.empty)
=
  let resp =
    ID.indefinite_description_ghost
      CT.client_response
      (fun resp ->
        CT.pending_protected_handshake_result_correct st0 st1 (Some resp) /\
        resp.CT.status == CT.StepOk) in
  let step =
    ID.indefinite_description_ghost
      CS.protected_handshake_step
      (fun step ->
        CT.protected_handshake_step_correct
          st0 st1 resp step B.empty B.empty B.empty) in
  (resp, step)

/// A drain step appends nothing to either half of the wire log, because
/// legal_connection_delta appends its raw deltas and both are empty here.
let lemma_drain_step_wire_log (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          st0.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received)
=
  let (resp, step) = drain_step_witness st0 st1 in
  let ev = CS.ConnProtectedHandshake step in
  assert (CT.legal_delta st0 st1 ev B.empty B.empty)

let lemma_drain_step_config (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  let (resp, step) = drain_step_witness st0 st1 in
  let ev = CS.ConnProtectedHandshake step in
  assert (CT.legal_delta st0 st1 ev B.empty B.empty);
  CSL.lemma_step_model_preserves_config st0.CS.cs_model ev st1.CS.cs_model

let lemma_drain_step_invariant (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1)
      (ensures
        CT.client_end_to_end_invariant st0 ==>
        CT.client_end_to_end_invariant st1)
=
  let (resp, step) = drain_step_witness st0 st1 in
  CT.lemma_protected_handshake_step_correct_preserves_end_to_end_invariant_conditional
    st0 st1 resp step B.empty B.empty B.empty

let lemma_drain_step_state_correct (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1)
      (ensures
        CT.client_state_correct st0 ==> CT.client_state_correct st1)
=
  let (resp, step) = drain_step_witness st0 st1 in
  let ev = CS.ConnProtectedHandshake step in
  introduce CT.client_state_correct st0 ==> CT.client_state_correct st1
  with (
    assert (Can.sent_event_nonempty_seal_projection st0.CS.cs_model ev B.empty);
    CT.lemma_legal_response_for_event_client_state_correct
      st0 st1 resp ev B.empty B.empty B.empty B.empty)

let lemma_drain_step_facts (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          st0.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received /\
        (CT.client_end_to_end_invariant st0 ==>
         CT.client_end_to_end_invariant st1) /\
        (CT.client_state_correct st0 ==> CT.client_state_correct st1))
=
  lemma_drain_step_wire_log st0 st1;
  lemma_drain_step_config st0 st1;
  lemma_drain_step_invariant st0 st1;
  lemma_drain_step_state_correct st0 st1

(** ---------------------------------------------------------------------- *)
(** The same facts, lifted over a chain                                     *)
(** ---------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2"
let rec lemma_drain_chain_facts (n:nat) (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_chain n st0 st1)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          st0.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received /\
        (CT.client_end_to_end_invariant st0 ==>
         CT.client_end_to_end_invariant st1) /\
        (CT.client_state_correct st0 ==> CT.client_state_correct st1))
      (decreases n)
=
  if n = 0
  then ()
  else
  let m : nat = n - 1 in
    eliminate
      (st1 == st0) \/
      (exists st'. drain_step st0 st' /\ drain_chain m st' st1)
    with ()
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> drain_step st0 st' /\ drain_chain m st' st1) in
       lemma_drain_step_facts st0 st';
       lemma_drain_chain_facts m st' st1)
#pop-options

let lemma_drained_facts (st0 st1:CS.connection_state)
  : Lemma
      (requires drained st0 st1)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          st0.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received /\
        (CT.client_end_to_end_invariant st0 ==>
         CT.client_end_to_end_invariant st1) /\
        (CT.client_state_correct st0 ==> CT.client_state_correct st1))
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> drain_chain n st0 st1) in
  lemma_drain_chain_facts n st0 st1

(** ---------------------------------------------------------------------- *)
(** Non-failure propagates backwards through a drain                        *)
(** ---------------------------------------------------------------------- *)

/// Consumers reason under a [connection_control_not_failed st1] hypothesis on
/// the *final* state, but the interesting facts are proved at the intermediate
/// state.  A drain step is a legal event, so non-failure travels backwards
/// along it, and hence along a whole chain.
let lemma_drain_step_nonfailed_previous (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1 /\ CT.connection_control_not_failed st1)
      (ensures CT.connection_control_not_failed st0)
=
  let (resp, step) = drain_step_witness st0 st1 in
  CT.lemma_legal_response_for_event_nonfailed_previous
    st0 st1 resp (CS.ConnProtectedHandshake step) B.empty B.empty B.empty B.empty

#push-options "--fuel 2 --ifuel 2"
let rec lemma_drain_chain_nonfailed_previous (n:nat) (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_chain n st0 st1 /\ CT.connection_control_not_failed st1)
      (ensures CT.connection_control_not_failed st0)
      (decreases n)
=
  if n = 0
  then ()
  else
  let m : nat = n - 1 in
    eliminate
      (st1 == st0) \/ (exists st'. drain_step st0 st' /\ drain_chain m st' st1)
    with ()
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> drain_step st0 st' /\ drain_chain m st' st1) in
       lemma_drain_chain_nonfailed_previous m st' st1;
       lemma_drain_step_nonfailed_previous st0 st')
#pop-options

let lemma_drained_nonfailed_previous (st0 st1:CS.connection_state)
  : Lemma
      (requires drained st0 st1 /\ CT.connection_control_not_failed st1)
      (ensures CT.connection_control_not_failed st0)
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> drain_chain n st0 st1) in
  lemma_drain_chain_nonfailed_previous n st0 st1

/// Implication form, for use where the hypothesis is not available at the call
/// site -- notably inside Pulse code, which has no [introduce].
let lemma_drained_nonfailed_previous_imp (st0 st1:CS.connection_state)
  : Lemma
      (requires drained st0 st1)
      (ensures
        CT.connection_control_not_failed st1 ==>
          CT.connection_control_not_failed st0)
=
  introduce
    CT.connection_control_not_failed st1 ==>
      CT.connection_control_not_failed st0
  with lemma_drained_nonfailed_previous st0 st1

(** ---------------------------------------------------------------------- *)
(** A network step followed by a drain                                      *)
(** ---------------------------------------------------------------------- *)

(**
  What a driver that owns the socket establishes about one call: it applied the
  record, and then drained every internal step the record left pending.

  [coalesced_network_bytes_end_to_end_correct] pins its second argument as the
  *direct* successor of its first, so a drained call cannot be described by it
  alone; the intermediate state has to be existentially quantified.  Because a
  drain step is application-invisible ([lemma_drained_facts]), every fact a
  driver needs about the final state either holds of the intermediate state
  already or transfers to the final state unchanged.
**)
let drained_network_bytes_end_to_end_correct
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input:B.bytes)
  (old_network_out network_out:B.bytes)
  (old_app_out app_out:B.bytes)
  : prop =
  exists st_mid.
    CT.coalesced_network_bytes_end_to_end_correct
      st0 st_mid buffer_resp network_input
      old_network_out network_out old_app_out app_out /\
    drained st_mid st1

/// Introduction form, for the driver's call site.
let lemma_drained_network_intro
      (st0 st_mid st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        CT.coalesced_network_bytes_end_to_end_correct
          st0 st_mid buffer_resp network_input
          old_network_out network_out old_app_out app_out /\
        drained st_mid st1)
      (ensures
        drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
=
  ()

/// Elimination form: recover the intermediate state, so that every lemma that
/// already exists for the undrained step can be applied to [st0], [st_mid] and
/// its conclusion then transported to [st1] with [lemma_drained_facts].
let drained_network_middle
      (st0 st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Ghost CS.connection_state
      (requires
        drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures fun st_mid ->
        CT.coalesced_network_bytes_end_to_end_correct
          st0 st_mid buffer_resp network_input
          old_network_out network_out old_app_out app_out /\
        drained st_mid st1)
=
  ID.indefinite_description_ghost
    CS.connection_state
    (fun st_mid ->
      CT.coalesced_network_bytes_end_to_end_correct
        st0 st_mid buffer_resp network_input
        old_network_out network_out old_app_out app_out /\
      drained st_mid st1)

/// Config preservation for the undrained coalesced step.  The strong disjunct
/// has a lemma already; the head disjunct gets it from its legal delta.
let lemma_coalesced_preserves_config
      (st0 st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        CT.coalesced_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  if CT.network_bytes_end_to_end_correct
       st0 st1 buffer_resp network_input
       old_network_out network_out old_app_out app_out
  then
    CT.lemma_network_bytes_end_to_end_correct_preserves_config
      st0 st1 buffer_resp network_input
      old_network_out network_out old_app_out app_out
  else (
    let step =
      ID.indefinite_description_ghost
        CS.protected_handshake_step
        (fun step ->
          0 < SZ.v buffer_resp.CT.consumed_len /\
          SZ.v buffer_resp.CT.consumed_len <= B.length network_input /\
          CT.protected_handshake_step_correct
            st0 st1 buffer_resp.CT.response step
            (CT.network_consumed_prefix
              network_input buffer_resp.CT.consumed_len)
            network_out app_out /\
          Seq.equal network_out old_network_out /\
          Seq.equal app_out old_app_out) in
    CSL.lemma_step_model_preserves_config
      st0.CS.cs_model (CS.ConnProtectedHandshake step) st1.CS.cs_model)

/// The two facts every driver predicate needs, stated directly on the composite.
let lemma_drained_network_preserves_config
      (st0 st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  let st_mid =
    drained_network_middle
      st0 st1 buffer_resp network_input
      old_network_out network_out old_app_out app_out in
  lemma_coalesced_preserves_config
    st0 st_mid buffer_resp network_input
    old_network_out network_out old_app_out app_out;
  lemma_drained_facts st_mid st1

let lemma_drained_network_preserves_invariant
      (st0 st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out /\
        CT.client_end_to_end_invariant st0)
      (ensures CT.client_end_to_end_invariant st1)
=
  let st_mid =
    drained_network_middle
      st0 st1 buffer_resp network_input
      old_network_out network_out old_app_out app_out in
  CT.lemma_coalesced_network_bytes_end_to_end_correct_preserves_invariant
    st0 st_mid buffer_resp network_input
    old_network_out network_out old_app_out app_out;
  lemma_drained_facts st_mid st1

(**
  The composite is *weaker* than the undrained predicate: a call that drained
  nothing is described by taking the intermediate state to be the final one.

  This is what makes moving the driver predicates onto the composite a
  weakening rather than a rewrite, exactly as in Phase 5a: every existing proof
  that establishes the undrained predicate still establishes the composite, and
  only consumers need adjusting -- via [drained_network_middle] to get back to
  the undrained step, and [lemma_drained_facts] to transport the conclusion.
**)
let lemma_coalesced_implies_drained_network
      (st0 st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        CT.coalesced_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures
        drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
=
  lemma_drained_refl st1

(** ---------------------------------------------------------------------- *)
(** A drain step cannot fail the connection                                 *)
(** ---------------------------------------------------------------------- *)

/// [step_handshake_message] moves to [ControlFailed] in exactly one place --
/// a received [HelloRetryRequest] -- and [step_protected_handshake] admits
/// only the four [protected_handshake_message_supported] messages, which
/// excludes it.  [set_pending_protected_handshake] touches only the handshake
/// buffers.  So a protected-handshake step never introduces a failure.
#push-options "--fuel 1 --ifuel 2 --split_queries always --z3rlimit 30"
let lemma_step_protected_handshake_not_failed
      (model:CS.connection_model)
      (step:CS.protected_handshake_step)
      (model1:CS.connection_model)
  : Lemma
      (requires
        CS.step_protected_handshake model step == Some model1 /\
        (match model.CS.model_control with
         | CS.ControlFailed _ -> False
         | _ -> True))
      (ensures
        (match model1.CS.model_control with
         | CS.ControlFailed _ -> False
         | _ -> True))
=
  (* A buffering step delivers no message: it rewrites only [model_record]
     and the handshake buffers, so it cannot introduce a failure either. *)
  if step.CS.protected_handshake_buffering
  then ()
  else begin
  assert (CS.protected_handshake_message_supported step.CS.protected_handshake_message);
  match step.CS.protected_handshake_message with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ -> ()
  | _ -> assert False
  end
#pop-options

let lemma_drain_step_not_failed (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_step st0 st1 /\ CT.connection_control_not_failed st0)
      (ensures CT.connection_control_not_failed st1)
=
  let (resp, step) = drain_step_witness st0 st1 in
  assert (CS.step_model st0.CS.cs_model (CS.ConnProtectedHandshake step)
            == Some st1.CS.cs_model);
  lemma_step_protected_handshake_not_failed
    st0.CS.cs_model step st1.CS.cs_model

#push-options "--fuel 2 --ifuel 2"
let rec lemma_drain_chain_not_failed (n:nat) (st0 st1:CS.connection_state)
  : Lemma
      (requires drain_chain n st0 st1 /\ CT.connection_control_not_failed st0)
      (ensures CT.connection_control_not_failed st1)
      (decreases n)
=
  if n = 0
  then ()
  else
  let m : nat = n - 1 in
    eliminate
      (st1 == st0) \/ (exists st'. drain_step st0 st' /\ drain_chain m st' st1)
    with ()
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> drain_step st0 st' /\ drain_chain m st' st1) in
       lemma_drain_step_not_failed st0 st';
       lemma_drain_chain_not_failed m st' st1)
#pop-options

let lemma_drained_not_failed (st0 st1:CS.connection_state)
  : Lemma
      (requires drained st0 st1 /\ CT.connection_control_not_failed st0)
      (ensures CT.connection_control_not_failed st1)
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> drain_chain n st0 st1) in
  lemma_drain_chain_not_failed n st0 st1

/// Drained form of [CT.lemma_network_bytes_app_out_positive_not_failed].  A
/// positive application-output length rules out the head disjunct (a protected
/// handshake step produces no application bytes), so the intermediate state is
/// reached by a genuine network step; the drain then carries non-failure
/// forward.
let lemma_drained_network_app_out_positive_not_failed
      (st0 st1:CS.connection_state)
      (buffer_resp:CT.client_buffer_response)
      (network_input:B.bytes)
      (old_network_out network_out:B.bytes)
      (old_app_out app_out:B.bytes)
  : Lemma
      (requires
        drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out /\
        SZ.v buffer_resp.CT.response.CT.app_out_len > 0)
      (ensures CT.connection_control_not_failed st1)
=
  let st_mid =
    drained_network_middle
      st0 st1 buffer_resp network_input
      old_network_out network_out old_app_out app_out in
  CT.lemma_network_bytes_app_out_positive_not_failed
    st0 st_mid buffer_resp network_input
    old_network_out network_out old_app_out app_out;
  lemma_drained_not_failed st_mid st1

(** ---------------------------------------------------------------------- *)
(** Internal work still pending                                             *)
(** ---------------------------------------------------------------------- *)

/// Unprocessed plaintext remains in the pending protected-handshake buffer.
/// Stated here, rather than reused from
/// [TLS13.Impl.Client.CanonicalProtocol.client_internal_pending], so that the
/// drain loop does not have to depend on the canonical-protocol module;
/// [TLS13.Impl.Client.DrainProgress.lemma_internal_pending_agrees] ties the two
/// together for the callers that need the canonical form.
let internal_pending (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed <
  B.length
    st.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes

/// The drain primitive reports [None] exactly at quiescence.
let lemma_pending_none_quiescent (st0 st1:CS.connection_state)
  : Lemma
      (requires CT.pending_protected_handshake_result_correct st0 st1 None)
      (ensures ~ (internal_pending st1))
= ()
