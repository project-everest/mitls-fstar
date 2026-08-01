module TLS13.System.ServerNotCFR

(** STANDALONE SPIKE — the reachability fact that a CONSISTENT server (indeed ANY
    consistent connection) is NEVER at control `ControlHandshaking
    HsClientFinishedReceived`.

    RATIONALE: NO arm of `step_handshake_message`/`step_local_event`/
    `step_tls_message` ever SETS `model_control := ControlHandshaking
    HsClientFinishedReceived` (the server processes the client Finished ATOMICALLY
    at `StateMachine.fst:774`, `HsServerFinishedSent -> ControlApplicationData`,
    skipping this stage entirely; the stage survives only as the legality anchor of
    `LocalVerifyClientFinished` and the server app-READ install, neither of which is
    ever reached).  This is exactly the `False` arm of `server_canonical_shape`
    (`ServerCanonicalShape.fst:237`).  We prove it directly as a single-step-stable
    closure predicate — no arm produces it, so it is preserved unconditionally and
    holds at `initial` (`ControlNew`).

    CONSUMER: the `app_material_agreement` `server_local` family.  The ONLY local
    event that raises the server's `record_read` epoch to `Application` is
    `LocalInstallTrafficKeysForRole(ServerEndpoint, TrafficApplication,
    TrafficRead)`, legal ONLY at `HsClientFinishedReceived`
    (`traffic_install_allowed_at_stage_for_role`, StateMachine.fst:1176/1233).  This
    lemma excludes that control at a consistent server, so a server LOCAL step can
    neither ESTABLISH nor RE-INSTALL (material-break) the app read epoch — collapsing
    the family to pure congruence / `cf_delivered`-vacuity. **)

module CS  = TLS13.Spec.StateMachine
module SMR = TLS13.Spec.StateMachine.Reachability
module RTC = FStar.ReflexiveTransitiveClosure
module ID  = FStar.IndefiniteDescription
module M   = TLS13.Messages
module CL  = TLS13.ConnectionLog

let ctrl_not_cfr_m (m:CS.connection_model) : prop =
  m.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedReceived

let ctrl_not_cfr (st:CS.connection_state) : prop =
  ctrl_not_cfr_m st.CS.cs_model

(** MODEL-LEVEL per-step: no legal step produces the `HsClientFinishedReceived`
    control (the predicate holds on the post-state UNCONDITIONALLY — the `p x`
    hypothesis is unused, since even a step FROM that control leaves it). **)
(** The big `step_handshake_message` dispatch, isolated so its enumeration is a
    small self-contained query. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_step_handshake_not_cfr
  (m:CS.connection_model) (dir:CS.direction) (hm:M.handshake_msg) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_cfr_m m /\ CS.step_handshake_message m dir hm == Some m')
      (ensures ctrl_not_cfr_m m')
  = ()
#pop-options

(** `step_tls_message` dispatch. **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_step_tls_not_cfr
  (m:CS.connection_model) (dir:CS.direction) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_cfr_m m /\ CS.step_tls_message m dir msg == Some m')
      (ensures ctrl_not_cfr_m m')
  = ()
#pop-options

(** `step_local_event` dispatch. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_step_local_not_cfr
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_cfr_m m /\ CS.step_local_event m lev == Some m')
      (ensures ctrl_not_cfr_m m')
  = ()
#pop-options

(** MODEL-LEVEL per-step: no legal step produces the `HsClientFinishedReceived`
    control (the predicate holds on the post-state UNCONDITIONALLY — the `p x`
    hypothesis is unused, since even a step FROM that control leaves it). **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_step_model_ctrl_not_cfr
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        ctrl_not_cfr_m m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures ctrl_not_cfr_m m')
  = match ev with
    | CS.ConnNetworkEvent dm ->
      lemma_step_tls_not_cfr m dm.CL.message_direction dm.CL.message_value m'
    | CS.ConnLocalEvent lev ->
      lemma_step_local_not_cfr m lev m'
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_ctrl_not_cfr (st0 st1:CS.connection_state)
  : Lemma
      (requires ctrl_not_cfr st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures ctrl_not_cfr st1)
  = assert (exists delta. CS.legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_model_ctrl_not_cfr
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_ctrl_not_cfr (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (ctrl_not_cfr y); (SMR.connection_state_single_step x y)}
          ctrl_not_cfr x /\ SMR.connection_state_single_step x y ==>
          ctrl_not_cfr y)
  = introduce forall x y.
      ctrl_not_cfr x /\ SMR.connection_state_single_step x y ==> ctrl_not_cfr y
    with introduce _ ==> _ with _.
      lemma_delta_ctrl_not_cfr x y

(** THE EXCLUSION: a consistent connection is never at `HsClientFinishedReceived`. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_not_cfr (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures
        st.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedReceived)
  = lemma_single_step_ctrl_not_cfr ();
    let p = ctrl_not_cfr in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** ========================================================================
    SECOND EXCLUSION: a consistent SERVER is never at `HsServerFinishedVerified`.

    Unlike `HsClientFinishedReceived` (produced by NO arm), `HsServerFinishedVerified`
    IS produced — by the CLIENT's atomic server-Finished receive
    (`step_handshake_message`, StateMachine.fst:738, the reachable producer) and by
    `LocalVerifyFinished` at `HsServerFinishedReceived` (StateMachine.fst:551).  BOTH
    are role-gated to a client: the handshake arm's `legal_handshake_message`
    (StateMachine.fst:1372) and the local arm's `legal_local_event`
    (StateMachine.fst:1271) each require `config_role == ClientEndpoint`.  So a
    *legal* SERVER step never produces HSFV.  Since `config_role` is preserved by
    every step, a role-gated single-step-stable predicate closes.

    CONSUMER: the SERVER branch of the record-material congruence.  `App(rd server)`
    at a handshaking control forces control ∈ {HSFV, CFR}
    (`lemma_handshaking_nonfinal_read_not_application`); CFR is excluded above and
    HSFV here, so a consistent server with `App(rd)` is off every handshaking
    control — settled — exactly as the client is. **)

let srv_not_hsfv_m (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
  m.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedVerified

let srv_not_hsfv (st:CS.connection_state) : prop =
  srv_not_hsfv_m st.CS.cs_model

(** The client's atomic server-Finished receive (StateMachine.fst:738) SETS HSFV, but
    its `legal_handshake_message` (StateMachine.fst:1372) pins `config_role ==
    ClientEndpoint`; every arm preserves `config_role`.  So a *legal* SERVER
    handshake step never produces HSFV. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 150 --split_queries always"
let lemma_step_handshake_not_shsfv
  (m:CS.connection_model) (dir:CS.direction) (hm:M.handshake_msg) (m':CS.connection_model)
  : Lemma
      (requires
        srv_not_hsfv_m m /\ CS.legal_handshake_message m dir hm /\
        CS.step_handshake_message m dir hm == Some m')
      (ensures srv_not_hsfv_m m')
  = ()
#pop-options

(** `step_tls_message`: the only HSFV producer is the `TlsHandshake` arm, gated to
    a client by `legal_handshake_message`. **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_step_tls_not_shsfv
  (m:CS.connection_model) (dir:CS.direction) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        srv_not_hsfv_m m /\ CS.legal_tls_message m dir msg /\
        CS.step_tls_message m dir msg == Some m')
      (ensures srv_not_hsfv_m m')
  = match msg with
    | M.TlsHandshake hm -> lemma_step_handshake_not_shsfv m dir hm m'
    | _ -> ()
#pop-options

(** `step_local_event`: `LocalVerifyFinished` is the ONLY arm producing HSFV, and its
    `legal_local_event` pins `config_role == ClientEndpoint`, contradicting the
    server hypothesis. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 150 --split_queries always"
let lemma_step_local_not_shsfv
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        srv_not_hsfv_m m /\ CS.legal_local_event m lev /\
        CS.step_local_event m lev == Some m')
      (ensures srv_not_hsfv_m m')
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_step_model_not_shsfv
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        srv_not_hsfv_m m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures srv_not_hsfv_m m')
  = match ev with
    | CS.ConnNetworkEvent dm ->
      lemma_step_tls_not_shsfv m dm.CL.message_direction dm.CL.message_value m'
    | CS.ConnLocalEvent lev ->
      lemma_step_local_not_shsfv m lev m'
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_not_shsfv (st0 st1:CS.connection_state)
  : Lemma
      (requires srv_not_hsfv st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures srv_not_hsfv st1)
  = assert (exists delta. CS.legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_model_not_shsfv
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_not_shsfv (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (srv_not_hsfv y); (SMR.connection_state_single_step x y)}
          srv_not_hsfv x /\ SMR.connection_state_single_step x y ==>
          srv_not_hsfv y)
  = introduce forall x y.
      srv_not_hsfv x /\ SMR.connection_state_single_step x y ==> srv_not_hsfv y
    with introduce _ ==> _ with _.
      lemma_delta_not_shsfv x y

(** THE EXCLUSION: a consistent SERVER is never at `HsServerFinishedVerified`. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_server_not_shsfv (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        st.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedVerified)
  = lemma_single_step_not_shsfv ();
    let p = srv_not_hsfv in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options
