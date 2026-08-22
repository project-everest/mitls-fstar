module TLS13.ConnectionState.HandshakeSeqZero

(**
  Raw handshake-epoch record-counter facts for the client-Finished delivery.

  The application-material-agreement bridge
  (`lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer`)
  requires, as its FIRST hypothesis, a RAW record-sequence equality
  `sender.record_write.seq == receiver.record_read.seq`.  At the client-Finished
  send/delivery this is a genuine, non-vacuous obligation about the
  handshake-epoch record counters, and `app_seq_pairing` does NOT supply it:
  its projections (`m_wadv`/`m_radv`/`app_wseq`/`app_rseq`) count only at
  `ControlApplicationData`, and the committed `handshaking_{read,write}_app_seq_zero`
  shapes pin only the APPLICATION-epoch seq (their `epoch =!= Application`
  disjunct is vacuously true at handshake epoch).

  This module supplies the missing handshake-epoch counter facts, specialised to
  the (server-authentication-only) supported profile in which a CLIENT writes
  nothing under handshake write keys before its own Finished, and a SERVER reads
  nothing under handshake read keys before the client Finished.  At the delivery
  both counters are 0, so the bridge's raw seq equality is `0 == 0`.  The
  `epoch =!= Handshake` disjunct is discharged at the use site by Brick 4's output
  (`lemma_handshake_client_traffic_peer_record_material_agrees_nonready`), which
  pins `record_write.epoch == Handshake` / `record_read.epoch == Handshake` --
  collapsing each disjunction to `seq == 0`.  The dependency on Brick 4 is
  one-way: Brick 4 does not consume these seq facts.

  ----------------------------------------------------------------------------
  DESIGN NOTE 1 -- stage-gate, not role-gate (reusable lesson).
  These shapes are STAGE-gated.  A role-gated formulation ("a client's write seq
  is 0 at every handshaking stage") FAILS to verify: it asks Z3 to exclude a
  client from the server-flight write arms via `legal_handshake_message`'s
  `== ServerEndpoint` role guard, and the SMT will not do that cross-role case
  reasoning on its own -- the SAME family of failure as "the SMT will not
  case-split a constructor on its own."  Stage-gating instead constrains only the
  chain in which the relevant direction never bumps and puts every bumping arm
  under a `_ -> True` arm, so the cross-role question never arises and the step
  lemma closes with `()`.  (Verified: the role-gated write step lemma fails while
  the stage-gated one closes at identical fuel/ifuel/rlimit.)

  DESIGN NOTE 2 -- why the consumed lemmas pin EXACT controls, not `ControlHandshaking?`.
  Each shape constrains only PART of the handshaking stages: the client's
  pre-Finished chain for the write seq, the server's pre-delivery chain for the
  read seq.  At a SERVER handshaking stage the client-write shape yields `True`
  (the server legitimately has write seq > 0 there after sending its flight), so a
  broad `ControlHandshaking?` requirement genuinely could not conclude `seq == 0`.
  The two consumed lemmas therefore pin the exact controls at which they are used
  (`HsServerFinishedVerified` for the client send, `HsServerFinishedSent` for the
  server delivery), both of which sit inside their respective constrained chains.

  DESIGN NOTE 3 -- why NO no-CCS hypothesis is needed here.
  The obvious threat to "a server reads nothing under handshake read keys before
  the client Finished" is ChangeCipherSpec: a client CCS arriving after the server
  installs its handshake read keys would bump `record_read.seq` off zero.  But the
  CCS arm (`M.TlsChangeCipherSpec, ControlHandshaking _ -> Some model`,
  StateMachine.fst) returns the model COMPLETELY UNCHANGED -- no `next_seq`, no
  record touch -- so CCS is inert to the record counters.  Contrast Brick 1's
  `ClientCanonicalShape`, which needed `log_has_no_received_ccs` because it reasons
  about the BYTE-LOG shape; here we reason about the RECORD COUNTERS, to which CCS
  is invisible.  Do NOT import a no-CCS hypothesis here by analogy -- it is
  unnecessary.  The remaining server-handshaking receive arms are alerts
  (`fail_model`, which preserves `model_record` and moves control to `ControlFailed`,
  outside the pin) and the client Finished (the delivery itself, i.e. the step OUT
  of the pinned control), so "reads nothing" is exhaustive.
**)

module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module ID = FStar.IndefiniteDescription

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Reachability

(* ==========================================================================
   Z1 -- client handshake-epoch WRITE seq is 0 on the client's pre-Finished chain.
   ========================================================================== *)

(* Stage-gated: constrain exactly the client pre-Finished handshaking chain
   (+ ControlNew).  Every write-bumping arm lands in a SERVER stage or in
   ControlApplicationData, which fall under `_ -> True`, so no cross-role
   reasoning is needed (see DESIGN NOTE 1). *)
let client_hs_write_seq_shape (model:connection_model) : prop =
  match model.model_control with
  | ControlNew
  | ControlHandshaking HsNotStarted
  | ControlHandshaking HsStarted
  | ControlHandshaking HsClientHelloSent
  | ControlHandshaking HsServerHelloReceived
  | ControlHandshaking HsEncryptedExtensionsReceived
  | ControlHandshaking HsCertificateReceived
  | ControlHandshaking HsCertificateValidated
  | ControlHandshaking HsCertificateVerifyReceived
  | ControlHandshaking HsCertificateVerifyVerified
  | ControlHandshaking HsServerFinishedReceived
  | ControlHandshaking HsServerFinishedVerified ->
    model.model_record.record_write.R.epoch =!= R.Handshake \/
    model.model_record.record_write.R.seq == 0
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100"
let lemma_step_model_client_hs_write_seq_shape
  (model:connection_model) (ev:conn_event) (model':connection_model)
  : Lemma
      (requires
        client_hs_write_seq_shape model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures client_hs_write_seq_shape model')
  = match ev with
    | ConnCleartextHandshake step ->
      (* Buffering is now legal for the CLIENT too (awaiting ServerHello), so
         this arm is reachable in a client-shaped lemma; it is inert on both
         the control and the record write state, which is all the shape reads. *)
      lemma_step_cleartext_handshake_inert model step;
      assert (model' == Some?.v (step_cleartext_handshake model step));
      assert (model'.model_control == model.model_control);
      assert (model'.model_record == model.model_record)
    | _ -> ()
#pop-options

let conn_client_hs_write_seq_shape (st:connection_state) : prop =
  client_hs_write_seq_shape st.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_client_hs_write_seq_shape (st0 st1:connection_state)
  : Lemma
      (requires
        conn_client_hs_write_seq_shape st0 /\ connection_state_single_step st0 st1)
      (ensures conn_client_hs_write_seq_shape st1)
  = assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    lemma_step_model_client_hs_write_seq_shape
      st0.cs_model delta.delta_event st1.cs_model
#pop-options

let lemma_single_step_client_hs_write_seq_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (conn_client_hs_write_seq_shape y); (connection_state_single_step x y)}
          conn_client_hs_write_seq_shape x /\ connection_state_single_step x y ==>
          conn_client_hs_write_seq_shape y)
  = introduce forall x y.
      conn_client_hs_write_seq_shape x /\ connection_state_single_step x y ==>
      conn_client_hs_write_seq_shape y
    with introduce _ ==> _ with
      lemma_delta_client_hs_write_seq_shape x y

let lemma_initial_client_hs_write_seq_shape (cfg:connection_config)
  : Lemma (ensures conn_client_hs_write_seq_shape (initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_client_handshake_write_seq_zero (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedVerified)
      (ensures
        st.cs_model.model_record.record_write.R.epoch =!= R.Handshake \/
        st.cs_model.model_record.record_write.R.seq == 0)
  = lemma_initial_client_hs_write_seq_shape st.cs_model.model_config;
    lemma_single_step_client_hs_write_seq_shape ();
    let p = conn_client_hs_write_seq_shape in
    let stable :
      squash (forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure connection_state_single_step p stable;
    assert (p (initial st.cs_model.model_config));
    assert (connection_state_evolves (initial st.cs_model.model_config) st);
    assert (p st)
#pop-options

(* ==========================================================================
   Z2 -- server handshake-epoch READ seq is 0 on the server's pre-delivery chain.
   ========================================================================== *)

(* Stage-gated: constrain exactly the server pre-delivery handshaking chain
   (+ ControlNew).  Every read-bumping arm lands in a CLIENT stage, or (the
   client-Finished delivery) exits to ControlApplicationData, all under
   `_ -> True`. *)
let server_hs_read_seq_shape (model:connection_model) : prop =
  match model.model_control with
  | ControlNew
  | ControlHandshaking HsNotStarted
  | ControlHandshaking HsAwaitingClientHello
  | ControlHandshaking HsClientHelloReceived
  | ControlHandshaking HsServerHelloSent
  | ControlHandshaking HsServerEncryptedFlightSent
  | ControlHandshaking HsServerFinishedSent ->
    model.model_record.record_read.R.epoch =!= R.Handshake \/
    model.model_record.record_read.R.seq == 0
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100"
let lemma_step_model_server_hs_read_seq_shape
  (model:connection_model) (ev:conn_event) (model':connection_model)
  : Lemma
      (requires
        server_hs_read_seq_shape model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures server_hs_read_seq_shape model')
  = match ev with
    | ConnCleartextHandshake step ->
      (* Cleartext buffering is inert on control and record state. *)
      lemma_step_cleartext_handshake_inert model step;
      assert (model' == Some?.v (step_cleartext_handshake model step));
      assert (model'.model_control == model.model_control);
      assert (model'.model_record == model.model_record)
    | _ -> ()
#pop-options

let conn_server_hs_read_seq_shape (st:connection_state) : prop =
  server_hs_read_seq_shape st.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_server_hs_read_seq_shape (st0 st1:connection_state)
  : Lemma
      (requires
        conn_server_hs_read_seq_shape st0 /\ connection_state_single_step st0 st1)
      (ensures conn_server_hs_read_seq_shape st1)
  = assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    lemma_step_model_server_hs_read_seq_shape
      st0.cs_model delta.delta_event st1.cs_model
#pop-options

let lemma_single_step_server_hs_read_seq_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (conn_server_hs_read_seq_shape y); (connection_state_single_step x y)}
          conn_server_hs_read_seq_shape x /\ connection_state_single_step x y ==>
          conn_server_hs_read_seq_shape y)
  = introduce forall x y.
      conn_server_hs_read_seq_shape x /\ connection_state_single_step x y ==>
      conn_server_hs_read_seq_shape y
    with introduce _ ==> _ with
      lemma_delta_server_hs_read_seq_shape x y

let lemma_initial_server_hs_read_seq_shape (cfg:connection_config)
  : Lemma (ensures conn_server_hs_read_seq_shape (initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_handshake_read_seq_zero (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedSent)
      (ensures
        st.cs_model.model_record.record_read.R.epoch =!= R.Handshake \/
        st.cs_model.model_record.record_read.R.seq == 0)
  = lemma_initial_server_hs_read_seq_shape st.cs_model.model_config;
    lemma_single_step_server_hs_read_seq_shape ();
    let p = conn_server_hs_read_seq_shape in
    let stable :
      squash (forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure connection_state_single_step p stable;
    assert (p (initial st.cs_model.model_config));
    assert (connection_state_evolves (initial st.cs_model.model_config) st);
    assert (p st)
#pop-options
