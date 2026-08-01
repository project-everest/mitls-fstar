module TLS13.System.AppBothCongruence

(** STANDALONE SPIKE — the unified record-material congruence lemma for the four
    NON-establishing `app_material_agreement` families (server_send, client_local,
    server_local, deliver_to_client) and the congruence branch of client_send.

    CLAIM: at a CONSISTENT endpoint whose BOTH record directions are already at the
    `Application` epoch, a single legal `~KeyUpdate` step preserves the
    `(epoch, key, static_iv)` triple of BOTH directions — exactly the material
    `peer_record_material_agrees` reads (never seq).

    WHY BOTH-App pins the control OFF every installer:
      * `App(rd)` at a handshaking control forces control ∈ {HsServerFinishedVerified
        (client), HsClientFinishedReceived} (`lemma_handshaking_nonfinal_read_not_application`);
      * `HsClientFinishedReceived` is excluded by `ServerNotCFR.lemma_consistent_not_cfr`
        (unreachable — the server installs app-read atomically at the receive);
      * `App(wr)` excludes `HsServerFinishedVerified` (the write shape:
        `lemma_handshaking_nonfinal_write_not_application`, a client at HSFV has NOT
        yet sent its Finished so its write epoch is still off Application).
    So both-App ⟹ control ∈ {ControlApplicationData, ControlClosing, ControlClosed,
    ControlFailed}.  At those controls the only record-mutating arms are the seq
    advances (`advance_direction_records`/`R.next_seq`, which preserve epoch/key/iv)
    and `fail_model` (preserves `model_record` outright); every KEY-INSTALL arm sits
    at a handshaking control and every `KeyUpdate` re-install is excluded by
    hypothesis.  Hence both triples are preserved. **)

module CS  = TLS13.Spec.StateMachine
module M   = TLS13.Messages
module CL  = TLS13.ConnectionLog
module R   = TLS13.Record.Spec
module B   = TLS13.Bytes
module SMR = TLS13.Spec.StateMachine.Reachability
module CSL = TLS13.ConnectionState.Lemmas
module SNCFR = TLS13.System.ServerNotCFR
module RF  = TLS13.Spec.StateMachine.RecordFraming

let is_keyupdate_event (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnNetworkEvent dm -> M.TlsKeyUpdate? dm.CL.message_value
  | _ -> false

let record_mat_eq (r r':CS.record_layer_state) : prop =
  r'.CS.record_write.R.epoch     == r.CS.record_write.R.epoch /\
  r'.CS.record_write.R.key       == r.CS.record_write.R.key /\
  r'.CS.record_write.R.static_iv == r.CS.record_write.R.static_iv /\
  r'.CS.record_read.R.epoch      == r.CS.record_read.R.epoch /\
  r'.CS.record_read.R.key        == r.CS.record_read.R.key /\
  r'.CS.record_read.R.static_iv  == r.CS.record_read.R.static_iv

(** Control is settled: past every key-installer.  In `step_local_event` and
    `step_handshake_message` EVERY key-install arm is gated on `ControlHandshaking _`,
    so `~ControlHandshaking?` alone puts the step off every installer.  (At
    `ControlNew` the only record-touching arms — `LocalStartHandshake`,
    `LocalStartServer`, `LocalFail` — preserve `model_record`.) **)
unfold let ctrl_settled (m:CS.connection_model) : prop =
  ~(CS.ControlHandshaking? m.CS.model_control)

(** `step_handshake_message` returns `None` at a settled control (no handshake arm
    fires), so this preservation is vacuous. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_hs_preserves_mat
  (m:CS.connection_model) (dir:CS.direction) (hm:M.handshake_msg) (m':CS.connection_model)
  : Lemma
      (requires ctrl_settled m /\ CS.step_handshake_message m dir hm == Some m')
      (ensures record_mat_eq m.CS.model_record m'.CS.model_record)
  = assert (CS.step_handshake_message m dir hm == None)
#pop-options

(** `advance_direction_records` only iterates `next_seq`, which preserves the
    material triple; local re-proof since the ulib lemmas aren't exported. **)
let rec lemma_adv_preserves_mat (st:R.direction_state) (n:nat)
  : Lemma
      (ensures
        (let a = CS.advance_direction_records st n in
         a.R.epoch == st.R.epoch /\ a.R.key == st.R.key /\
         a.R.static_iv == st.R.static_iv))
      (decreases n)
  = if n = 0 then () else lemma_adv_preserves_mat st (n - 1)

(** `step_tls_message` at a settled control: app-data (seq advance), alert
    (`fail_model` preserves record), ignored-post-handshake (read seq advance).
    `KeyUpdate` (the only re-installer) excluded by hypothesis. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 150 --split_queries always"
let lemma_tls_preserves_mat
  (m:CS.connection_model) (dir:CS.direction) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        ctrl_settled m /\ ~(M.TlsKeyUpdate? msg) /\
        CS.step_tls_message m dir msg == Some m')
      (ensures record_mat_eq m.CS.model_record m'.CS.model_record)
  = match msg with
    | M.TlsHandshake hm -> lemma_hs_preserves_mat m dir hm m'
    | M.TlsApplicationData bytes ->
      lemma_adv_preserves_mat m.CS.model_record.CS.record_write
        (RF.application_data_record_count bytes)
    | _ -> ()
#pop-options

(** `step_local_event` at a settled control: `LocalDeliverApplicationData`
    (touches only `app_log`) or `LocalFail` (`fail_model` preserves record). **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_local_preserves_mat
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires ctrl_settled m /\ CS.step_local_event m lev == Some m')
      (ensures record_mat_eq m.CS.model_record m'.CS.model_record)
  = ()
#pop-options

(** Combiner: a legal `~KeyUpdate` step at a settled control preserves both
    material triples. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_settled_step_preserves_mat
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        ctrl_settled m /\ ~(is_keyupdate_event ev) /\
        CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures record_mat_eq m.CS.model_record m'.CS.model_record)
  = match ev with
    | CS.ConnNetworkEvent dm ->
      lemma_tls_preserves_mat m dm.CL.message_direction dm.CL.message_value m'
    | CS.ConnLocalEvent lev ->
      lemma_local_preserves_mat m lev m'
#pop-options

(** MODEL-LEVEL congruence (CLIENT): both directions App ⟹ step preserves both
    triples.  Control is pinned off every installer: App(rd) at handshaking forces
    HSFV (nonfinal-read + CFR-exclusion), and a consistent client at HSFV has
    write ≠ App (`lemma_client_finished_verified_write_epoch_not_application`),
    contradicting App(wr); so control is settled (appdata/closure). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_client_step_appboth_preserves_record_material
  (st st':CS.connection_state) (ev:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event st.CS.cs_model ev /\
        CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model /\
        ~(is_keyupdate_event ev) /\
        R.Application? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch /\
        R.Application? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
      (ensures record_mat_eq st.CS.cs_model.CS.model_record st'.CS.cs_model.CS.model_record)
  = SNCFR.lemma_consistent_not_cfr st;
    (if CS.ControlHandshaking? st.CS.cs_model.CS.model_control then begin
       if st.CS.cs_model.CS.model_control
            = CS.ControlHandshaking CS.HsServerFinishedVerified
       then CSL.lemma_client_finished_verified_write_epoch_not_application st
       else CSL.lemma_handshaking_nonfinal_read_not_application st
     end);
    // control is now settled; enumerate the record-preserving arms.
    lemma_settled_step_preserves_mat st.CS.cs_model ev st'.CS.cs_model
#pop-options

(** MODEL-LEVEL congruence (SERVER): both directions App ⟹ step preserves both
    triples.  Control is pinned off every installer symmetrically to the client:
    App(rd) at a handshaking control forces control ∈ {HSFV, CFR}
    (`lemma_handshaking_nonfinal_read_not_application`); `ServerNotCFR` excludes
    BOTH — CFR unconditionally and HSFV for a server (`lemma_consistent_server_not_shsfv`,
    since the only HSFV producers, the client atomic Finished-receive and
    `LocalVerifyFinished`, are both role-gated to a client).  So a consistent server
    with `App(rd)` is settled, and the settled-arm enumeration preserves both triples. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_server_step_appboth_preserves_record_material
  (st st':CS.connection_state) (ev:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event st.CS.cs_model ev /\
        CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model /\
        ~(is_keyupdate_event ev) /\
        R.Application? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch /\
        R.Application? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
      (ensures record_mat_eq st.CS.cs_model.CS.model_record st'.CS.cs_model.CS.model_record)
  = SNCFR.lemma_consistent_not_cfr st;
    SNCFR.lemma_consistent_server_not_shsfv st;
    (if CS.ControlHandshaking? st.CS.cs_model.CS.model_control then
       CSL.lemma_handshaking_nonfinal_read_not_application st);
    // control is now settled; enumerate the record-preserving arms.
    lemma_settled_step_preserves_mat st.CS.cs_model ev st'.CS.cs_model
#pop-options
