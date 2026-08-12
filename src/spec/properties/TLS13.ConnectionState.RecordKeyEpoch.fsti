module TLS13.ConnectionState.RecordKeyEpoch

(**
  RECORD KEY-PRESENCE => NON-INITIAL EPOCH, at ANY reachable state.

  A control-free structural reachability fact: on any [connection_state_consistent]
  state (i.e. reachable from [CS.initial] via the canonical single-step closure),
  a present record-direction key forces a non-[Initial] epoch.  Equivalently, the
  [Initial] epoch carries [key == None].

  WHY THIS IS NOT [record_read_key_schedule_projection].  The key-schedule
  projection ([SMKM.record_read_key_schedule_projection_for_role]) is
  CONTROL-GATED: it is [| ControlFailed _ -> True], hence VACUOUS at a failed
  endpoint.  So it supplies [Initial ==> key == None] only for a live control.
  This lemma is proved by [RTC.stable_on_closure] over the reachability relation
  directly, so it holds UNIFORMLY across every control INCLUDING [ControlFailed]:
  the only key-installer is [R.install_keys], which is only ever called with a
  [Handshake]/[Application] epoch (via [traffic_record_epoch] or a literal), never
  [Initial]; [R.next_seq], [advance_direction_records] and [fail_model] all
  preserve the (epoch, key) pair.

  CONSUMER.  The application-read faithful-decode cruxes need [~Initial(read)] to
  fire the handshake-sealed in-flight bridge, and they obtain [Some? read.key]
  from the delivery's OWN protected-message decode (open_record succeeds only with
  a key present).  Bridging those two is exactly this lemma, and it must survive
  [ControlFailed] because a peer can fail before an in-flight Finished lands.  The
  statement is role-agnostic, so the same read lemma serves both the server->client
  (SF) and client->server (CF) delivery arms.
**)

module CS  = TLS13.Spec.StateMachine
module R   = TLS13.Record.Spec
module SMR = TLS13.Spec.StateMachine.Reachability

val lemma_connection_consistent_read_key_present_not_initial
  (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        Some? st.CS.cs_model.CS.model_record.CS.record_read.R.key)
      (ensures
        ~(R.Initial? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch))

val lemma_connection_consistent_write_key_present_not_initial
  (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        Some? st.CS.cs_model.CS.model_record.CS.record_write.R.key)
      (ensures
        ~(R.Initial? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch))
