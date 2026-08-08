module TLS13.ConnectionState.AppDataBufferEmpty

(**
  AT APPLICATION DATA, THE PROTECTED-HANDSHAKE BUFFER IS EMPTY, at ANY reachable
  state.

  A structural reachability fact about the pending protected-handshake plaintext
  buffer ([hb_encrypted_server_handshake_bytes] / [..._parsed]), proved by
  [RTC.stable_on_closure] over the canonical single-step relation.

  WHY IT HOLDS.  The buffer has exactly ONE writer in the whole state machine,
  [set_pending_protected_handshake] (StateMachine.fst:1019), reachable only
  through [step_protected_handshake]; every other [hs_buffers] update in
  [step_handshake_message] / [step_local_event] rewrites a DIFFERENT field
  ([hb_client_hello_bytes], [hb_server_hello_bytes], [hb_certificate_leaf_der],
  [hb_certificate_verify_input]) and leaves the protected-handshake pair alone.
  And [legal_protected_handshake_step] (StateMachine.fst:1587) pins
  [config_role == ClientEndpoint].  Hence:

  (A) a SERVER's buffer is empty at every reachable state -- nothing can ever
      write it; and

  (B) any endpoint at [ControlApplicationData] has an empty buffer.  There are
      exactly three transitions INTO [ControlApplicationData]:
        * [CL.Sent, Finished, HsServerFinishedVerified] -- the client's, whose
          [legal_handshake_message] guard demands
          [protected_handshake_buffer_empty] outright;
        * [CL.Received, Finished, HsServerFinishedSent] -- the server's, and
        * [LocalVerifyClientFinished] at [HsClientFinishedReceived] -- also
          role-pinned to [ServerEndpoint];
      the last two are covered by (A).  Once AT [ControlApplicationData] the
      buffer cannot be refilled either: refilling needs a
      [ConnProtectedHandshake] step, whose legality requires
      [legal_handshake_message model CL.Received _], and NO arm of
      [legal_handshake_message] admits [ControlApplicationData].

  CONSUMER.  [TLS13.System.lemma_appdata_implies_client_ready].  Since the merge
  of the internal-event work, [client_driver_application_ready] carries
  [CS.protected_handshake_buffer_empty] as a conjunct (it is what makes readiness
  imply [TLS13.System.Internal.tls_settled]); the Pulse driver discharges it by a
  runtime check, but the SPEC-level bridge from "consistent and at application
  data" to "ready" needs it as a reachability fact.  That is this module.
**)

module CS  = TLS13.Spec.StateMachine
module SMR = TLS13.Spec.StateMachine.Reachability

(** (B): the fact the readiness bridge consumes. **)
val lemma_connection_appdata_protected_handshake_buffer_empty
  (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures CS.protected_handshake_buffer_empty st.CS.cs_model)

(** (A): the role-side half, exposed because it is the honest reason the server
    arm of (B) holds and is independently reusable. **)
val lemma_connection_non_client_protected_handshake_buffer_empty
  (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        ~(st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint))
      (ensures CS.protected_handshake_buffer_empty st.CS.cs_model)
