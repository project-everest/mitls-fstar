module TLS13.System.Ordering

(** ═══════════════════════════════════════════════════════════════════════════
    PHASE B / Step 2 — the cross-endpoint ORDERING lemma (the "P2" soundness
    pivot), stated STANDALONE with the sender-facing reachability + byte-pairing
    as EXPLICIT hypotheses (so it can be validated cheaply BEFORE the
    `tls_system_inv` surgery that carries those hypotheses as a conjunct).

    deliver-to-client direction (recipient = client, sender = server):
      an in-flight record whose FROZEN pre-send server snapshot has already
      installed its application WRITE keys (write.epoch == Application) cannot be
      delivered to a client that is still in its handshake RECEIVE region
      (read.epoch == Handshake, i.e. before it installs the server-application
      READ keys).  Equivalently, contrapositive-free: at such a client the
      snapshot's write epoch is NOT Application.

    HONEST PROOF (pure reachability + record counting; NO authenticity /
    injectivity / receiver-coupling):
      * write.epoch(snap) == Application  ⟹  (server flight-complete shape) the
        server has populated all four protected-flight fields  ⟹  it has SENT ≥ 4
        ApplicationData-typed records (`lemma_server_reachable_sent_ge_marker`).
      * byte-pairing + the sender-facing snapshot reachability give
        snap.raw_sent == client.raw_received (append right-cancellation).
      * a client in its handshake receive region has RECEIVED ≤ 3 ApplicationData
        records (`lemma_client_reachable_recv_region_le3`).
      * 4 ≤ count(snap.raw_sent) == count(client.raw_received) ≤ 3 — contradiction.
    ═══════════════════════════════════════════════════════════════════════════ **)

module CS = TLS13.Spec.ConnectionState
module R  = TLS13.Record.Spec
module B  = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module RTC = FStar.ReflexiveTransitiveClosure
module ID  = FStar.IndefiniteDescription
module WStep = TLS13.System.WireStep

(** ─────────────────────────────────────────────────────────────────────────
    The SERVER flight-complete write-once shape.  A single self-contained,
    single-step-inductive invariant: for a SERVER, every set field forces its
    predecessors, `HsServerFinishedSent` and every post-flight control force the
    server Finished field, and `write.epoch == Application` forces it too (the
    application WRITE keys are installed only AT `HsServerFinishedSent`, by which
    point the whole flight is already sent).  Consequently a consistent server
    with `write.epoch == Application` has ALL FOUR protected-flight fields set.
    ───────────────────────────────────────────────────────────────────────── **)
let server_flight_marker_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
  (let hs = m.CS.model_handshake in
   (Some? hs.CS.hs_certificate ==> Some? hs.CS.hs_encrypted_extensions) /\
   (hs.CS.hs_certificate_verify_verified ==>
      (Some? hs.CS.hs_encrypted_extensions /\ Some? hs.CS.hs_certificate)) /\
   (Some? hs.CS.hs_server_finished ==>
      (Some? hs.CS.hs_encrypted_extensions /\
       Some? hs.CS.hs_certificate /\
       hs.CS.hs_certificate_verify_verified)) /\
   (m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent ==>
      Some? hs.CS.hs_server_finished) /\
   (m.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived ==>
      Some? hs.CS.hs_server_finished) /\
   (m.CS.model_control == CS.ControlApplicationData ==>
      Some? hs.CS.hs_server_finished) /\
   (m.CS.model_control == CS.ControlClosing ==>
      Some? hs.CS.hs_server_finished) /\
   (m.CS.model_control == CS.ControlClosed ==>
      Some? hs.CS.hs_server_finished) /\
   ((m.CS.model_control == CS.ControlNew \/
     m.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello \/
     m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived \/
     m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
     m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent) ==>
      m.CS.model_record.CS.record_write.R.epoch =!= R.Application) /\
   (m.CS.model_record.CS.record_write.R.epoch == R.Application ==>
      Some? hs.CS.hs_server_finished))

#push-options "--fuel 2 --ifuel 5 --z3rlimit 150 --split_queries always"
let lemma_step_server_flight_marker_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        server_flight_marker_shape m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures server_flight_marker_shape m')
  = ()
#pop-options

let lemma_delta_server_flight_marker_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires
        server_flight_marker_shape st0.CS.cs_model /\
        CS.connection_state_single_step st0 st1)
      (ensures server_flight_marker_shape st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_server_flight_marker_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_server_flight_marker_shape (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures server_flight_marker_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = server_flight_marker_shape st.CS.cs_model in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _.
        lemma_delta_server_flight_marker_shape x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(** A consistent server whose application WRITE keys are installed has its whole
    protected flight populated — hence `server_sent_marker_count == 4`. **)
let lemma_server_write_app_marker4 (st:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        st.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Application)
      (ensures WStep.server_sent_marker_count st.CS.cs_model == 4)
  = lemma_consistent_server_flight_marker_shape st

(** ─────────────────────────────────────────────────────────────────────────
    THE ORDERING LEMMA — deliver-to-client direction.

    `client` is the recipient, `snap_st` the frozen pre-send SERVER snapshot
    carried by the in-flight channel (its model is `snap`, its raw-sent log is
    the sender's pre-send log).  `raw` is the in-flight record.  The hypotheses
    are exactly what the sender-facing `inflight_snap_reachable` conjunct + the
    existing `byte_pairing` conjunct + the recipient reachability supply at a
    delivery; they are taken explicitly here so the count argument can be
    validated before it is wired into `tls_system_inv`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_inflight_sender_write_epoch_not_application_client
  (client snap_st:CS.connection_state) (raw:B.bytes)
  : Lemma
      (requires
        // recipient (client) is byte-reachable and in its handshake receive region
        WStep.client_reachable (CS.initial client.CS.cs_model.CS.model_config) client /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        WStep.client_recv_region_ctrl client.CS.cs_model.CS.model_control /\
        // sender snapshot is byte-reachable + consistent (the `inflight_snap_reachable`
        // existential witness `pred`) and is a server
        WStep.server_reachable (CS.initial snap_st.CS.cs_model.CS.model_config) snap_st /\
        CS.connection_state_consistent snap_st /\
        snap_st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        // byte-pairing: sender's pre-send log ++ raw == recipient's received ++ raw
        Seq.equal
          (B.append snap_st.CS.cs_wire_log.CL.raw_sent raw)
          (B.append client.CS.cs_wire_log.CL.raw_received raw))
      (ensures
        snap_st.CS.cs_model.CS.model_record.CS.record_write.R.epoch =!= R.Application)
  = // Suppose the snapshot has installed its application write keys.
    // Then the whole server flight is sent: count(snap.raw_sent) >= 4.
    // But snap.raw_sent == client.raw_received (append right-cancellation),
    // and a client in its receive region has received <= 3.  Contradiction.
    Seq.lemma_append_inj
      snap_st.CS.cs_wire_log.CL.raw_sent raw
      client.CS.cs_wire_log.CL.raw_received raw;
    assert (Seq.equal
              snap_st.CS.cs_wire_log.CL.raw_sent
              client.CS.cs_wire_log.CL.raw_received);
    WStep.lemma_raw_appdata_count_seq_equal
      snap_st.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received;
    WStep.lemma_client_reachable_recv_region_le3
      client.CS.cs_model.CS.model_config client;
    if snap_st.CS.cs_model.CS.model_record.CS.record_write.R.epoch = R.Application
    then begin
      lemma_server_write_app_marker4 snap_st;
      WStep.lemma_server_reachable_sent_ge_marker
        snap_st.CS.cs_model.CS.model_config snap_st
    end
#pop-options
