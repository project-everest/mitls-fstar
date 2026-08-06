module TLS13.ConnectionState.HandshakeSeqZero

(**
  Raw handshake-epoch record-counter facts for the client-Finished delivery.

  The application-material-agreement bridge
  (`lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer`)
  requires, as its FIRST hypothesis, a RAW record-sequence equality
  `sender.record_write.seq == receiver.record_read.seq`.  At the client-Finished
  send/delivery this is a genuine, non-vacuous obligation about the
  handshake-epoch record counters, and `app_seq_pairing` does NOT supply it:
  `app_seq_pairing`'s projections (`m_wadv`/`m_radv`/`app_wseq`/`app_rseq`) count
  only at `ControlApplicationData`, and the committed
  `handshaking_{read,write}_app_seq_zero` shapes pin only the APPLICATION-epoch
  seq (their `epoch =!= Application` disjunct is vacuously true at handshake
  epoch).

  This module supplies the missing handshake-epoch counter facts, specialised to
  the (server-authentication-only) supported profile in which:
    - a CLIENT writes nothing under handshake write keys before its own Finished
      (its only handshake-stage send arm is `ClientHello` at cleartext/Initial
      epoch; the write-bumping arms are all the SERVER flight sends), so at the
      client's pre-Finished chain the handshake-epoch write seq is still 0; and
    - a SERVER reads nothing under handshake read keys before the client Finished
      (it only reads the cleartext `ClientHello`; the read-bumping arms are all
      CLIENT receives, and the client-Finished delivery itself exits to
      `ControlApplicationData`), so at the server's pre-delivery chain the
      handshake-epoch read seq is still 0.

  At the delivery both counters are 0, so the bridge's raw seq equality is
  `0 == 0`.  The `epoch =!= Handshake` disjunct below is discharged at the use
  site by Brick 4's output
  (`lemma_handshake_client_traffic_peer_record_material_agrees_nonready`), which
  pins `record_write.epoch == Handshake` / `record_read.epoch == Handshake` on
  the two directions -- collapsing each disjunction to `seq == 0`.  The
  dependency on Brick 4 is one-way: Brick 4 does not consume these seq facts.

  Proof technique (reusable lesson).  These shapes are STAGE-gated, not
  role-gated.  A role-gated formulation ("a client's write seq is 0 at every
  handshaking stage") FAILS: it asks Z3 to exclude a client from the
  server-flight write arms via `legal_handshake_message`'s `== ServerEndpoint`
  role guard, and the SMT will not do that cross-role case reasoning on its own
  (same family as "the SMT will not case-split a constructor on its own").
  Stage-gating instead constrains only the chain in which the relevant direction
  never bumps, and puts every bumping arm under a `_ -> True` arm, so the
  cross-role question never arises and the step lemma closes with `()`.
**)

module R = TLS13.Record.Spec

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Reachability

(** At the client-Finished SEND pre-state (client control
    `HsServerFinishedVerified`), the client's record WRITE handshake-epoch seq is
    0 (or its write epoch is not yet `Handshake`).  Consumed with Brick 4's
    `record_write.epoch == Handshake` to obtain `record_write.seq == 0`. **)
val lemma_client_handshake_write_seq_zero (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedVerified)
      (ensures
        st.cs_model.model_record.record_write.R.epoch =!= R.Handshake \/
        st.cs_model.model_record.record_write.R.seq == 0)

(** At the client-Finished DELIVERY pre-state (server control
    `HsServerFinishedSent`, where the server is frozen because `server_serve` is
    disabled), the server's record READ handshake-epoch seq is 0 (or its read
    epoch is not yet `Handshake`).  Consumed with Brick 4's
    `record_read.epoch == Handshake` to obtain `record_read.seq == 0`. **)
val lemma_server_handshake_read_seq_zero (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedSent)
      (ensures
        st.cs_model.model_record.record_read.R.epoch =!= R.Handshake \/
        st.cs_model.model_record.record_read.R.seq == 0)
