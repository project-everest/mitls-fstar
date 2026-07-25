module TLS13.System.ProgressCount

(**
  Structural handshake-PROGRESS counts for the wire-level TLS system.

  The System-level strict-progress guard (added to the six pre-application-data
  transitions in `TLS13.System`) forbids the two model no-op self-loops
  (redundant idempotent key installs and stray `TlsChangeCipherSpec` records)
  during the handshake, making the per-endpoint event-log LENGTH a deterministic
  function of the endpoint micro-state.  The counts here are that function.

  Both counts are `16 - rank` on the rank-covered handshake stages, reusing the
  already-verified obligation-rank measures:
    * client: `PNI.client_application_progress_rank` (covers HsStarted through
      ControlApplicationData);
    * server: `SWR.server_hello_window_rank` (covers HsServerHelloSent through
      ControlApplicationData), plus a small additive PREFIX formula for the five
      cleartext prefix events (ControlNew .. HsServerHelloSent) that the window
      rank does not reach.

  The `_step_bound` lemmas prove each count rises by AT MOST ONE per legal event
  (the strict-progress guard supplies the matching lower bound, pinning the
  advance to exactly one).  Region ENTRIES (ControlNew -> first handshake stage,
  and the server prefix -> window boundary) need small "fresh-stage" shape facts,
  bundled as `client_micro_shape` / `server_micro_shape` and maintained as
  invariant conjuncts by `TLS13.System`.
**)

module CS  = TLS13.Spec.StateMachine
module CL  = TLS13.ConnectionLog
module M   = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module SWR = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank
module L   = FStar.List.Tot
module B   = TLS13.Bytes
module SMKM = TLS13.Spec.StateMachine.KeyMaterial

(** Control stages strictly before application data (and before any close). **)
let pre_appdata_control (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed
  | CS.ControlFailed _ -> false
  | _ -> true

(** All five key-schedule slots empty. **)
let keys_all_none (keys:CS.key_schedule_state) : prop =
  keys.CS.ks_shared_secret == None /\
  keys.CS.ks_client_handshake_traffic == None /\
  keys.CS.ks_server_handshake_traffic == None /\
  keys.CS.ks_client_application_traffic == None /\
  keys.CS.ks_server_application_traffic == None

(** ─────────────────────────────────────────────────────────────────────────
    Client count.
    ───────────────────────────────────────────────────────────────────────── **)

let client_progress (m:CS.connection_model) : int =
  match m.CS.model_control with
  | CS.ControlNew -> 0
  | CS.ControlHandshaking _ -> 16 - PNI.client_application_progress_rank m
  | _ -> 0

(** The one client region-entry shape fact: at ControlNew the key schedule is
    empty (no install can have fired before leaving ControlNew).  Every other
    client boundary is handshake-stage -> handshake-stage, handled uniformly by
    the rank step lemma. **)
let client_micro_shape (m:CS.connection_model) : prop =
  CS.ControlNew? m.CS.model_control ==>
    keys_all_none m.CS.model_handshake.CS.hs_keys

(** A legal client-role step raises `client_progress` by at most one across the
    pre-application-data region. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_progress_step_bound
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        pre_appdata_control m.CS.model_control /\
        pre_appdata_control m'.CS.model_control /\
        client_micro_shape m)
      (ensures client_progress m' <= client_progress m + 1)
  = match m.CS.model_control with
    | CS.ControlNew ->
      // Only LocalStartHandshake is legal for a client at ControlNew; it moves
      // to HsStarted keeping the (empty) key schedule, so rank m' == 15.
      assert (keys_all_none m.CS.model_handshake.CS.hs_keys);
      ()
    | CS.ControlHandshaking _ ->
      // Uniform: client_progress = 16 - rank on both sides; the rank step lemma
      // gives rank m <= rank m' + 1 (m' is not Failed, being pre-appdata).
      PNI.lemma_client_application_progress_rank_step m ev m'
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Server count.

    Prefix (ControlNew .. HsClientHelloReceived) is an additive milestone count;
    the window stages (HsServerHelloSent onward) reuse `SWR.server_hello_window_rank`
    as `16 - rank`.  The prefix->window boundary (Sent ServerHello) lands on a
    FRESH HsServerHelloSent whose window rank is exactly 11, giving 16-11 = 5,
    one more than the prefix value 4 at a fully-selected HsClientHelloReceived.
    ───────────────────────────────────────────────────────────────────────── **)

let server_progress (m:CS.connection_model) : int =
  let hs = m.CS.model_handshake in
  match m.CS.model_control with
  | CS.ControlNew -> 0
  | CS.ControlHandshaking CS.HsAwaitingClientHello -> 1
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    2 + (if Some? hs.CS.hs_server_selection then 1 else 0)
      + (if Some? hs.CS.hs_keys.CS.ks_shared_secret then 1 else 0)
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlHandshaking CS.HsClientFinishedReceived ->
    16 - SWR.server_hello_window_rank m
  | _ -> 0

(** Server region-entry shape facts:
      * HsAwaitingClientHello: no selection/shared yet (prefix base for the
        HsClientHelloReceived count 2);
      * HsClientHelloReceived: the four handshake/application traffic keys and the
        three encrypted-flight message fields (and the CV-verified flag) are still
        empty, so `Sent ServerHello` lands on a FRESH HsServerHelloSent. **)
let server_early_all_none (m:CS.connection_model) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  hs.CS.hs_server_selection == None /\
  keys_all_none keys /\
  hs.CS.hs_encrypted_extensions == None /\
  hs.CS.hs_certificate == None /\
  hs.CS.hs_certificate_verify == None /\
  hs.CS.hs_certificate_verify_verified == false

let server_micro_shape (m:CS.connection_model) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  (CS.ControlNew? m.CS.model_control ==> server_early_all_none m) /\
  ((m.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello) ==>
     server_early_all_none m) /\
  ((m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived) ==>
     keys.CS.ks_client_handshake_traffic == None /\
     keys.CS.ks_server_handshake_traffic == None /\
     keys.CS.ks_client_application_traffic == None /\
     keys.CS.ks_server_application_traffic == None /\
     hs.CS.hs_encrypted_extensions == None /\
     hs.CS.hs_certificate == None /\
     hs.CS.hs_certificate_verify == None /\
     hs.CS.hs_certificate_verify_verified == false)

(** A legal server-role step raises `server_progress` by at most one across the
    pre-application-data region. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60"
let lemma_server_progress_step_bound
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        pre_appdata_control m.CS.model_control /\
        pre_appdata_control m'.CS.model_control /\
        server_micro_shape m)
      (ensures server_progress m' <= server_progress m + 1)
  = match m.CS.model_control with
    | CS.ControlNew -> ()
    | CS.ControlHandshaking CS.HsAwaitingClientHello -> ()
    | CS.ControlHandshaking CS.HsClientHelloReceived ->
      // Select / Derive stay in-stage (+1 in the additive count); Sent ServerHello
      // crosses to a FRESH HsServerHelloSent whose window rank is exactly 11.
      (match m'.CS.model_control with
       | CS.ControlHandshaking CS.HsServerHelloSent ->
         SWR.lemma_server_hello_window_rank_fresh_is_eleven m'
       | _ -> ())
    | CS.ControlHandshaking CS.HsServerHelloSent
    | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
    | CS.ControlHandshaking CS.HsServerFinishedSent
    | CS.ControlHandshaking CS.HsClientFinishedReceived ->
      SWR.lemma_server_hello_window_rank_step m ev m'
    | _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Model-level preservation helpers (called from `TLS13.System`).
    ───────────────────────────────────────────────────────────────────────── **)

(** Once out of the pre-application-data region (application data or a close
    control), a legal step never returns to it. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_step_post_appdata_stable
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        ~(pre_appdata_control m.CS.model_control))
      (ensures ~(pre_appdata_control m'.CS.model_control))
  = ()
#pop-options

(** `client_micro_shape` is preserved by any legal client-role step. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80"
let lemma_client_micro_shape_step
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        client_micro_shape m)
      (ensures client_micro_shape m')
  = ()
#pop-options

(** `server_micro_shape` is preserved by any legal server-role step. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 120"
let lemma_server_micro_shape_step
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        server_micro_shape m)
      (ensures server_micro_shape m')
  = ()
#pop-options

(** Every legal connection delta appends exactly one event, raising the
    event-log length by exactly one. **)
let lemma_delta_length (st0 st1:CS.connection_state) (d:CS.connection_delta)
  : Lemma
      (requires CS.legal_connection_delta st0 d st1)
      (ensures
        L.length st1.CS.cs_event_log == L.length st0.CS.cs_event_log + 1)
  = L.append_length st0.CS.cs_event_log [d.CS.delta_event]

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 2A — key-schedule prefix (ksp).

    A tiny write-once/monotone key-schedule fact used to pin the client's
    late-obligation rank at the send-Client-Finished boundary (so the boundary
    length is exactly 16 without an external pin).  It says: an application
    traffic secret is present only if the master secret is (FACT 2), and the
    master secret is present only if the shared secret is (FACT 1 — both are set
    atomically by `derive_shared_secret_model`).
    ───────────────────────────────────────────────────────────────────────── **)

let ksp_keys (keys:CS.key_schedule_state) : prop =
  ((Some? keys.CS.ks_client_application_traffic \/ Some? keys.CS.ks_server_application_traffic)
     ==> Some? keys.CS.ks_master_secret) /\
  (Some? keys.CS.ks_master_secret ==> Some? keys.CS.ks_shared_secret)

let model_ksp (m:CS.connection_model) : prop =
  ksp_keys m.CS.model_handshake.CS.hs_keys

(** A single-slot key-schedule install preserves `ksp_keys`, provided that an
    application-epoch install has the master secret already present (the install
    never touches master or shared). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 20"
let lemma_update_label_ksp
  (keys:CS.key_schedule_state) (epoch:CS.traffic_epoch)
  (label:CS.traffic_label) (material:CS.traffic_key_material)
  : Lemma
      (requires
        ksp_keys keys /\
        (epoch == CS.TrafficApplication ==> Some? keys.CS.ks_master_secret))
      (ensures ksp_keys (CS.update_key_schedule_with_label keys epoch label material))
  = ()
#pop-options

(** `model_ksp` is preserved by any legal step.  The only events touching the
    three tracked slots are `LocalDeriveSharedSecret` (sets master & shared
    together) and the two traffic-key installs (an application-epoch install is
    legal only when `expected_traffic_secret` — hence the master secret — is
    already present); every other event leaves the key schedule fixed. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_ksp_step
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        model_ksp m)
      (ensures model_ksp m')
  = let hs = m.CS.model_handshake in
    match ev with
    | CS.ConnLocalEvent local ->
      (match local, m.CS.model_control with
       | CS.LocalInstallTrafficKeys install, CS.ControlHandshaking _ ->
         // Legality forces expected_traffic_secret (role Client) present; for the
         // application epoch that requires the master secret.
         assert (CS.traffic_install_matches_key_schedule hs install);
         assert (install.CS.install_epoch == CS.TrafficApplication ==>
                   Some? hs.CS.hs_keys.CS.ks_master_secret);
         lemma_update_label_ksp hs.CS.hs_keys install.CS.install_epoch
           (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint install.CS.install_direction)
           install.CS.install_material
       | CS.LocalInstallTrafficKeysForRole role_install, CS.ControlHandshaking _ ->
         let install = role_install.CS.install_payload in
         assert (CS.traffic_install_matches_key_schedule_for_role
                   role_install.CS.install_role hs install);
         assert (install.CS.install_epoch == CS.TrafficApplication ==>
                   Some? hs.CS.hs_keys.CS.ks_master_secret);
         lemma_update_label_ksp hs.CS.hs_keys install.CS.install_epoch
           (CS.traffic_label_for_endpoint_direction role_install.CS.install_role
              install.CS.install_direction)
           install.CS.install_material
       | _ -> ())
    | CS.ConnNetworkEvent _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 2B — client send-Client-Finished progress.

    The unique client edge from the pre-application-data region into
    `ControlApplicationData` is `Sent Finished` at `HsServerFinishedVerified`.
    Its legality supplies the client-handshake and both application traffic
    secrets; `model_ksp` then supplies the shared secret, so the client's
    late-obligation rank is 0 and `client_progress` at the pre-state is exactly
    15 — hence the post-state event-log length is exactly 16.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_send_cf_progress
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        ~(m.CS.model_control == CS.ControlApplicationData) /\
        m'.CS.model_control == CS.ControlApplicationData /\
        model_ksp m)
      (ensures pre_appdata_control m.CS.model_control /\ client_progress m == 15)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 2B — server transition-source at HsServerFinishedSent.

    The only legal one-step predecessors of control `HsServerFinishedSent` are:
      * `HsServerEncryptedFlightSent` (the server sends its Finished), and
      * `HsServerFinishedSent` itself (a write-key install self-loop).
    Neither is "post client-Finished", which is exactly what the system-level
    coupling needs to rule the client out of readiness at the pre-state of a
    server-send that produces `HsServerFinishedSent`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_server_delta_source_finished_sent
  (st0 st1:CS.connection_state) (d:CS.connection_delta)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        st1.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
      (ensures
        st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
        st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
  = ()
#pop-options

(** Predecessors of `HsClientFinishedReceived`: the server receives the client's
    Finished (from `HsServerFinishedSent`), or a self-loop keeps it there.  Used
    to reduce the system-level HsCFR length clause to the HsSFS clause of the
    pre-state (whose server sits at `HsServerFinishedSent`). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_server_delta_source_client_finished_received
  (st0 st1:CS.connection_state) (d:CS.connection_delta)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        st1.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived)
      (ensures
        st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
        st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived)
  = ()
#pop-options

(** RECEIVED-event refinement of the HsClientFinishedReceived predecessor fact.
    A wire delivery to the server carries a `Received` network event.  The only
    such event legal INTO `HsClientFinishedReceived` from a different stage is the
    client Finished (whose source is `HsServerFinishedSent`).  The sole
    `HsClientFinishedReceived`-self-loop for a received event is a stray
    `TlsChangeCipherSpec` record, which `step_tls_message` maps to `Some model`
    with the model entirely UNCHANGED.  So a received-event step landing at
    `HsClientFinishedReceived` either comes from `HsServerFinishedSent` or leaves
    the model fixed — and the latter is excluded at the System level by the
    strict-progress `server_advances` guard (the stage is pre-application-data, so
    the guard demands a strict progress increase that an unchanged model cannot
    provide). **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_server_received_source_client_finished_received
  (m0 m1:CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_model m0 (SMKM.received_tls_event msg) == Some m1 /\
        m1.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived)
      (ensures
        m0.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
        m1 == m0)
  = ()
#pop-options

(** RECEIVED-event refinement for HsServerFinishedSent: no received event lands at
    `HsServerFinishedSent` from a different stage (that stage is produced only by the
    server SENDING its Finished).  The sole received-event self-loop there is a stray
    `TlsChangeCipherSpec`, which leaves the model UNCHANGED.  So a received-event step
    landing at `HsServerFinishedSent` leaves the model fixed — excluded at the System
    level by the strict-progress `server_advances` guard. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_server_received_source_finished_sent
  (m0 m1:CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_model m0 (SMKM.received_tls_event msg) == Some m1 /\
        m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
      (ensures m1 == m0)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 2B — client app-key installation at ControlApplicationData.

    A client that has reached `ControlApplicationData` sent its Finished, whose
    legality (`legal_handshake_message`, `Sent Finished` at
    `HsServerFinishedVerified`) demands both application-traffic secrets; the
    application-key slots are write-once and never cleared, so any later step
    keeps them.  Phrased as a single-step-stable model shape, established over
    reachability (`connection_state_consistent`) at the System level.
    ───────────────────────────────────────────────────────────────────────── **)
let client_appdata_appkeys (m:CS.connection_model) : prop =
  (m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
   m.CS.model_control == CS.ControlApplicationData) ==>
  (Some? m.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
   Some? m.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)

let client_appdata_appkeys_st (st:CS.connection_state) : prop =
  client_appdata_appkeys st.CS.cs_model

#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_client_appdata_appkeys_delta
  (st0 st1:CS.connection_state) (d:CS.connection_delta)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        client_appdata_appkeys_st st0)
      (ensures client_appdata_appkeys_st st1)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PHASE 1 — control-change ⇒ strict progress increase (for the internal LOCAL
    transitions).

    A legal step that CHANGES the control state (and stays pre-application-data)
    strictly increases the progress count.  This is the lower-bound half needed
    to keep the forward LENGTH invariant (`client_len_ok`/`server_len_ok`) under
    the STRICTER internal-local guard `client_local_advances`/`server_local_advances`
    (progress↑ ∨ control-changed), which — unlike the send/deliver guard — also
    forbids the internal application-data self-loop.

    The client version needs no restriction (every pre-appdata client control
    change strictly advances progress).  The server version additionally requires
    the raw byte delta to be EMPTY (as it is for an internal LOCAL event), which
    rules out the window `Sent`/deliver control changes whose progress step is not
    a strict +1; those are guarded by `server_advances` (unchanged), not the local
    guard, so this restriction loses nothing. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 80 --split_queries always"
let lemma_client_control_change_progress
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            pre_appdata_control m.CS.model_control /\
            pre_appdata_control m'.CS.model_control /\
            client_micro_shape m /\
            ~(m'.CS.model_control == m.CS.model_control))
          (ensures client_progress m' > client_progress m)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 80 --split_queries always"
let lemma_server_control_change_progress
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires
            m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            CS.legal_event m ev /\
            CS.step_model m ev == Some m' /\
            CS.event_raw_delta_legal m ev B.empty B.empty /\
            pre_appdata_control m.CS.model_control /\
            pre_appdata_control m'.CS.model_control /\
            server_micro_shape m /\
            ~(m'.CS.model_control == m.CS.model_control))
          (ensures server_progress m' > server_progress m)
  = ()
#pop-options
