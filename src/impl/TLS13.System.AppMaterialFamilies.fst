module TLS13.System.AppMaterialFamilies

(** STAGE B — the five NON-`deliver_to_server` `app_material_agreement` preservation
    families, wired onto the record-material congruence engine
    (`TLS13.System.AppBothCongruence`, committed `61aa6f1f7`) and the epoch→count
    bridge (`TLS13.System.ServerReadRecvCount`, committed `44311a8c4`).

    RECALL the partition (recorded at `61aa6f1f7`): among the SIX families, exactly
    TWO can ESTABLISH `cf_delivered` — `deliver_to_server` (committed
    `lemma_ama_deliver_to_server`) and `client_send` — and the other FOUR are pure
    CONGRUENCE.  `server_local` cannot establish because the only local app-READ
    installer, `LocalInstallTrafficKeysForRole(Server, App, Read)`, is legal solely
    at `HsClientFinishedReceived`, which `ServerNotCFR.lemma_consistent_not_cfr`
    proves unreachable.

    THE PER-FAMILY BILL (each discharged by a NAMED lemma below):
      * `server_send`      — congruence; read epoch preserved by a SENT step
                             (`lemma_sent_preserves_read_epoch`), so `App(rd b.server)`
                             lifts to `App(rd a.server)`.
      * `client_send`      — congruence branch (`App(wr a.client)` already) OR
                             ESTABLISHMENT case-3: the `ServerReadRecvCount` bridge +
                             `byte_pairing` give the `0 == ≥1` vacuity.
      * `client_local`     — congruence; WRITE epoch preserved by a client local step
                             (`lemma_client_local_preserves_write_epoch`): a client can
                             NEVER install app-write locally (only
                             `install_record_keys_for_role(Server, App, Write)` sets it).
      * `server_local`     — congruence; READ epoch preserved off CFR
                             (`lemma_server_local_preserves_read_epoch`), the CFR-gated
                             install excluded by `lemma_consistent_not_cfr`.
      * `deliver_to_client`— congruence; WRITE epoch preserved by a RECEIVED step
                             (`lemma_recv_preserves_write_epoch`): no receive installs
                             write (the atomic Finished receives install app-READ).

    KEY LICENSE (KeyMaterial.fst:617/283): `supported_profile_application_record_material_agrees`
    pins ALL FOUR directions' epoch `== Application`, so in the congruence case
    `agreement a` supplies both-App at the acting endpoint — exactly the congruence
    engine's precondition. **)

module CS   = TLS13.Spec.StateMachine
module M    = TLS13.Messages
module CL   = TLS13.ConnectionLog
module R    = TLS13.Record.Spec
module T    = TLS13.Types
module B    = TLS13.Bytes
module L    = FStar.List.Tot
module Seq  = FStar.Seq
module SMR  = TLS13.Spec.StateMachine.Reachability
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module CSL  = TLS13.ConnectionState.Lemmas
module SY   = TLS13.System
module MP   = Common.MachineProduct
module ASP  = TLS13.System.AppSeqPairing
module AB   = TLS13.System.AppBothCongruence
module SNCFR = TLS13.System.ServerNotCFR
module SRRC = TLS13.System.ServerReadRecvCount
module WStep = TLS13.System.WireStep
module RF   = TLS13.Spec.StateMachine.RecordFraming
module WF    = Common.WireFormat
module SMCan = TLS13.Spec.StateMachine.Canonical
module ES   = TLS13.Spec.Endpoint.Server
module EC   = TLS13.Spec.Endpoint.Client
module CTy  = TLS13.Impl.CanonicalTypes
module CW   = TLS13.Spec.Endpoint.Wire
module EAPI = TLS13.Spec.Endpoint.API
module SM   = Common.StateMachine
module SMCorr = TLS13.Spec.StateMachine.Correspondence
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module HANR = TLS13.ConnectionState.HandshakeAgreementNonReady
module WFL  = TLS13.Spec.WireFormatLemmas
module SLM  = TLS13.System.SlotMono
module WSpec = TLS13.Wire.Spec
module CCS  = TLS13.ConnectionState.ClientCanonicalShape
module SCS  = TLS13.ConnectionState.ServerCanonicalShape

let wr (st:CS.connection_state) : R.direction_state =
  st.CS.cs_model.CS.model_record.CS.record_write
let rd (st:CS.connection_state) : R.direction_state =
  st.CS.cs_model.CS.model_record.CS.record_read

(** ─────────────────────────────────────────────────────────────────────────
    EPOCH-PRESERVATION MODEL HELPERS

    Each shows that the acting step does not NEWLY raise the relevant direction's
    epoch to `Application` — the crux the user flagged: a copied argument would be
    false at exactly `client_send`'s Finished (write install), which is why that one
    family is establishment, not congruence.
    ───────────────────────────────────────────────────────────────────────── **)

(** A SENT handshake message never touches `record_read` (the read-installing arms —
    the client/server atomic Finished receives — are `CL.Received`). **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_sent_handshake_preserves_read
  (m:CS.connection_model) (hm:M.handshake_msg) (m':CS.connection_model)
  : Lemma
      (requires CS.step_handshake_message m CL.Sent hm == Some m')
      (ensures (m'.CS.model_record.CS.record_read).R.epoch ==
               (m.CS.model_record.CS.record_read).R.epoch)
  = ()
#pop-options

(** A SENT tls message preserves the READ epoch (app-data/alert Sent advance WRITE;
    handshake Sent delegates to the lemma above). **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_sent_preserves_read_epoch
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires CS.step_tls_message m CL.Sent msg == Some m')
      (ensures (m'.CS.model_record.CS.record_read).R.epoch ==
               (m.CS.model_record.CS.record_read).R.epoch)
  = match msg with
    | M.TlsHandshake hm -> lemma_sent_handshake_preserves_read m hm m'
    | _ -> ()
#pop-options

(** A RECEIVED handshake message never installs `record_write` (the atomic Finished
    receives install app-READ; no receive arm writes `record_write`). **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_recv_handshake_preserves_write
  (m:CS.connection_model) (hm:M.handshake_msg) (m':CS.connection_model)
  : Lemma
      (requires CS.step_handshake_message m CL.Received hm == Some m')
      (ensures (m'.CS.model_record.CS.record_write).R.epoch ==
               (m.CS.model_record.CS.record_write).R.epoch)
  = ()
#pop-options

(** A RECEIVED tls message preserves the WRITE epoch. **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_recv_preserves_write_epoch
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires CS.step_tls_message m CL.Received msg == Some m')
      (ensures (m'.CS.model_record.CS.record_write).R.epoch ==
               (m.CS.model_record.CS.record_write).R.epoch)
  = match msg with
    | M.TlsHandshake hm -> lemma_recv_handshake_preserves_write m hm m'
    | _ -> ()
#pop-options

(** A CLIENT local event never raises the WRITE epoch to `Application`: the ONLY
    app-write installer is `install_record_keys_for_role(Server, App, Write)`, and a
    LEGAL client local pins `install_role == config_role == ClientEndpoint`, so that
    arm never fires; every other install writes at most the Handshake epoch, and
    `install_record_keys (App, Write)` is a no-op. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 200 --split_queries always"
let lemma_client_local_event_preserves_write_epoch
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_local_event m lev /\ CS.step_local_event m lev == Some m')
      (ensures
        R.Application? (m'.CS.model_record.CS.record_write).R.epoch ==>
        R.Application? (m.CS.model_record.CS.record_write).R.epoch)
  = ()
#pop-options

(** A SERVER local event OFF `HsClientFinishedReceived` never raises the READ epoch
    to `Application`: `LocalInstallTrafficKeys` is client-only; the only server
    app-READ install, `LocalInstallTrafficKeysForRole(Server, App, Read)`, is legal
    solely at `HsClientFinishedReceived` (`traffic_install_allowed_at_stage_for_role`),
    excluded by hypothesis; other installs set at most the Handshake read epoch. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 300 --split_queries always"
let lemma_server_local_event_preserves_read_epoch
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.legal_local_event m lev /\ CS.step_local_event m lev == Some m')
      (ensures
        R.Application? (m'.CS.model_record.CS.record_read).R.epoch ==>
        R.Application? (m.CS.model_record.CS.record_read).R.epoch)
  = ()
#pop-options

(** DISPATCH: a CLIENT empty-byte-delta step preserves "no new app-write". **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_client_local_preserves_write_epoch
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event m ce /\ CS.step_model m ce == Some m' /\
        CS.event_raw_delta_legal m ce B.empty B.empty)
      (ensures
        R.Application? (m'.CS.model_record.CS.record_write).R.epoch ==>
        R.Application? (m.CS.model_record.CS.record_write).R.epoch)
  = match ce with
    | CS.ConnLocalEvent lev ->
      lemma_client_local_event_preserves_write_epoch m lev m'
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM.  A HEAD protected step is charged
         `raw_records_exactly raw_received Application_data 1`, which `B.empty`
         cannot satisfy, so only TAIL steps reach here.  Either way the step
         routes through `CS.step_handshake_message _ CL.Received _`, and NO
         `CL.Received` arm touches `record_write` at all -- the write epoch is
         literally unchanged, so the implication is trivial. *)
      if step.CS.protected_handshake_head
      then WStep.lemma_ws_raw_records_nonempty_parse_record B.empty T.Application_data 1
      else ()
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated m dm m'
#pop-options

(** DISPATCH: a SERVER empty-byte-delta step OFF CFR preserves "no new app-read". **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_server_local_preserves_read_epoch
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.legal_event m ce /\ CS.step_model m ce == Some m' /\
        CS.event_raw_delta_legal m ce B.empty B.empty)
      (ensures
        R.Application? (m'.CS.model_record.CS.record_read).R.epoch ==>
        R.Application? (m.CS.model_record.CS.record_read).R.epoch)
  = match ce with
    | CS.ConnLocalEvent lev ->
      lemma_server_local_event_preserves_read_epoch m lev m'
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM, STRUCTURALLY VACUOUS.  `CS.legal_protected_handshake_step` pins
         `model.model_config.config_role == CS.ClientEndpoint` as its FIRST
         conjunct, and this dispatch is gated on `config_role == ServerEndpoint`.
         A server can therefore never take a protected-handshake step.  (This is
         NOT an `assert False` off a vacuous hypothesis: the exclusion is the
         explicit role conjunct of `legal_protected_handshake_step`.) *)
      assert (CS.legal_protected_handshake_step m step);
      assert (m.CS.model_config.CS.config_role == CS.ClientEndpoint)
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated m dm m'
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE FIVE FAMILIES
    ───────────────────────────────────────────────────────────────────────── **)

(** SERVER SEND — congruence.  `read` epoch preserved by the sent step, so
    `cf_delivered b` lifts to `cf_delivered a`; `agreement a` then supplies both-App
    at the server and `lemma_server_step_appboth_preserves_record_material` carries
    the material across. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_ama_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_material_agreement b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (w:CW.wire_message) (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns ASP.app_material_agreement b
    with _pf.
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      let ev = SMKM.sent_tls_event sent in
      assert (CS.step_model a.server.CS.cs_model ev == Some s'.CS.cs_model);
      assert (SMCorr.connection_state_no_key_update_trace s');
      ASP.lemma_sent_not_key_update s' sent;
      introduce ASP.cf_delivered b ==>
                  SMKM.supported_profile_application_record_material_agrees b.client b.server
      with _cfd.
      (
        // b.client == a.client, b.server == s'.
        lemma_sent_preserves_read_epoch a.server.CS.cs_model sent s'.CS.cs_model;
        // App(rd s') ==> App(rd a.server); App(wr b.client) == App(wr a.client).
        assert (ASP.cf_delivered a);
        assert (SMKM.supported_profile_application_record_material_agrees a.client a.server);
        AB.lemma_server_step_appboth_preserves_record_material a.server s' ev;
        assert (AB.record_mat_eq a.server.CS.cs_model.CS.model_record
                                 s'.CS.cs_model.CS.model_record)
      )
    )
#pop-options

(** CLIENT LOCAL — congruence.  The client is the acting endpoint; the server is
    untouched.  `write` epoch preserved (a client never installs app-write locally),
    so `cf_delivered b` lifts to `cf_delivered a`; the material carries across either
    by record-unchanged (empty-delta network) or by the client congruence engine
    (a genuine local event, where `~KeyUpdate` is immediate). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_ama_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_local a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_material_agreement b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns ASP.app_material_agreement b
    with _pf.
    (
      ASP.lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      returns ASP.app_material_agreement b
      with _pe.
      (
        introduce ASP.cf_delivered b ==>
                    SMKM.supported_profile_application_record_material_agrees b.client b.server
        with _cfd.
        (
          lemma_client_local_preserves_write_epoch a.client.CS.cs_model c'.CS.cs_model ce;
          assert (ASP.cf_delivered a);
          assert (SMKM.supported_profile_application_record_material_agrees a.client a.server);
          (match ce with
           | CS.ConnLocalEvent lev ->
             AB.lemma_client_step_appboth_preserves_record_material a.client c' ce
           | CS.ConnProtectedHandshake step ->
             (* NEW ARM.  The empty byte-delta forces a TAIL step (a HEAD step is
                charged exactly one `Application_data` record by
                `CS.event_raw_delta_legal`).  Two sub-cases:
                - message is NOT `Finished`: `CS.step_protected_handshake`
                  RESTORES `record_read` from the pre-state, and no `CL.Received`
                  arm of `CS.step_handshake_message` touches `record_write`, so
                  `record_mat_eq` holds on the nose -- no key material moves.
                - message IS `Finished`: the atomic client arm lands at
                  `HsServerFinishedVerified`, where
                  `CSL.lemma_client_finished_verified_write_epoch_not_application`
                  forces `(wr c').epoch =!= R.Application`.  That contradicts
                  `ASP.cf_delivered b`, whose first conjunct is
                  `R.Application? (wr b.client)`.  VACUOUS -- and note this is a
                  CONTROL/epoch exclusion, not an appeal to a vacuous hypothesis. *)
             (* A BUFFERING step (one that merely sets a record's plaintext
                aside so a handshake message spanning several records can be
                reassembled) is a HEAD step, and `CS.event_raw_delta_legal`
                charges a head step exactly one `Application_data` record --
                impossible against the EMPTY byte-delta here.  So this arm is
                a TAIL step, as it always was, and is never a buffering step;
                in particular `protected_handshake_message` below is a real
                message rather than the inert placeholder a buffering step
                carries. *)
             (if step.CS.protected_handshake_head
              then begin
                CSL.lemma_raw_records_exactly_one_parse_record
                  B.empty T.Application_data;
                eliminate exists (fragment:B.bytes).
                  WSpec.parse_record B.empty ==
                    Some (T.Application_data, fragment, B.length B.empty)
                returns False
                with _.
                ( WSpec.lemma_parse_record_implies_parse_record_wire B.empty;
                  WSpec.lemma_parse_record_wire_some_consumed_positive
                    B.empty T.Application_data fragment (B.length B.empty) )
              end);
             assert (step.CS.protected_handshake_head == false);
             (match step.CS.protected_handshake_message with
              | M.Finished _ ->
                assert (SMR.connection_state_consistent c');
                assert (c'.CS.cs_model.CS.model_control
                          == CS.ControlHandshaking CS.HsServerFinishedVerified);
                CSL.lemma_client_finished_verified_write_epoch_not_application c'
              | _ -> ())
           | CS.ConnNetworkEvent dm ->
             ASP.lemma_network_empty_delta_record_unchanged_ungated
               a.client.CS.cs_model dm c'.CS.cs_model);
          assert (AB.record_mat_eq a.client.CS.cs_model.CS.model_record
                                   c'.CS.cs_model.CS.model_record)
        )
      )
    )
#pop-options

(** SERVER LOCAL — congruence.  Mirror of the client local, with `read` epoch
    preserved OFF `HsClientFinishedReceived` (the CFR-gated app-read install excluded
    by `lemma_consistent_not_cfr`); the congruence engine is the server one. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_ama_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_local a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_material_agreement b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns ASP.app_material_agreement b
    with _pf.
    (
      ASP.lemma_server_local_extract a.server s' local out;
      SNCFR.lemma_consistent_not_cfr a.server;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      returns ASP.app_material_agreement b
      with _pe.
      (
        introduce ASP.cf_delivered b ==>
                    SMKM.supported_profile_application_record_material_agrees b.client b.server
        with _cfd.
        (
          lemma_server_local_preserves_read_epoch a.server.CS.cs_model s'.CS.cs_model ce;
          assert (ASP.cf_delivered a);
          assert (SMKM.supported_profile_application_record_material_agrees a.client a.server);
          (match ce with
           | CS.ConnLocalEvent lev ->
             AB.lemma_server_step_appboth_preserves_record_material a.server s' ce
           | CS.ConnNetworkEvent dm ->
             ASP.lemma_network_empty_delta_record_unchanged_ungated
               a.server.CS.cs_model dm s'.CS.cs_model);
          assert (AB.record_mat_eq a.server.CS.cs_model.CS.model_record
                                   s'.CS.cs_model.CS.model_record)
        )
      )
    )
#pop-options

(** DELIVER TO CLIENT — congruence.  The client RECEIVES; the server is untouched.
    A receive never installs `record_write` (the atomic Finished receives install
    app-READ), so `write` epoch is preserved and `cf_delivered b` lifts to
    `cf_delivered a`; `agreement a` then supplies both-App at the client and the
    client congruence engine carries the material across.  Unlike
    `deliver_to_server`, there is NO establishment case: a receive cannot raise the
    client's WRITE epoch, so this family is pure congruence. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_ama_deliver_to_client
  (a:SY.tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        ASP.app_extras a /\
        a.channel == SY.tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
        SY.tls_system_inv ({ a with client = c'; channel = MP.Quiet }) /\
        SY.tls_no_rekeying ({ a with client = c'; channel = MP.Quiet }))
      (ensures ASP.app_material_agreement ({ a with client = c'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with client = c'; channel = MP.Quiet } in
    introduce ASP.cf_delivered b ==>
                SMKM.supported_profile_application_record_material_agrees b.client b.server
    with _cfd.
    (
      EC.lemma_client_wire_step_inversion #CTy.client_local_event a.client c' wire out;
      eliminate exists (conn_ev0:CS.conn_event).
        (EC.client_wire_received_event a.client wire conn_ev0 /\
         SMCan.canonical_wire_step a.client c' conn_ev0
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev0 out.SM.so_local_outputs)
      returns SMKM.supported_profile_application_record_material_agrees b.client b.server
      with _pd.
      (
      match conn_ev0 with
      | CS.ConnLocalEvent _ -> ()   // `client_wire_received_event` is False here
      | CS.ConnProtectedHandshake step ->
        (* NEW ARM (HEAD protected handshake, the new client wire-receive shape).
           `AB.record_mat_eq` compares only epoch/key/static_iv -- NOT seq -- so the
           `R.next_seq` bump of the EncryptedExtensions/Certificate/CertificateVerify
           arms moves nothing it observes.  The only material-moving arm is the
           atomic `Finished` install, and that lands the client at
           `HsServerFinishedVerified`, where
           `CSL.lemma_client_finished_verified_write_epoch_not_application`
           forces `(wr c').epoch =!= R.Application`, contradicting `ASP.cf_delivered b`
           (whose first conjunct is `R.Application? (wr b.client)`).  VACUOUS by a
           control/epoch exclusion, not by a vacuous hypothesis. *)
        (if step.CS.protected_handshake_buffering
         then
           (* A BUFFERING step sets this record's plaintext aside so a
              handshake message spanning several records can be reassembled.
              It delivers NO message -- its `protected_handshake_message` is
              an inert placeholder, so the dispatch below would be reading
              garbage -- and it moves only the pending buffer and the read
              sequence number (via `R.next_seq`, which preserves epoch, key
              and static IV).  Those are exactly the fields `AB.record_mat_eq`
              observes, so no material moves. *)
           begin
             assert (ASP.cf_delivered a);
             assert (AB.record_mat_eq a.client.CS.cs_model.CS.model_record
                                      c'.CS.cs_model.CS.model_record)
           end
         else
         match step.CS.protected_handshake_message with
         | M.Finished _ ->
           assert (SMR.connection_state_consistent c');
           assert (c'.CS.cs_model.CS.model_control
                     == CS.ControlHandshaking CS.HsServerFinishedVerified);
           CSL.lemma_client_finished_verified_write_epoch_not_application c'
         | _ ->
           assert (ASP.cf_delivered a);
           assert (AB.record_mat_eq a.client.CS.cs_model.CS.model_record
                                    c'.CS.cs_model.CS.model_record))
      | CS.ConnNetworkEvent tm ->
        let msg : M.tls_message = tm.CL.message_value in
        let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
        assert (conn_ev0 == conn_ev);
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        assert (CS.step_tls_message a.client.CS.cs_model CL.Received msg == Some c'.CS.cs_model);
        ASP.lemma_recv_not_key_update c' msg;
        // congruence: b.server == a.server, b.client == c'.
        lemma_recv_preserves_write_epoch a.client.CS.cs_model msg c'.CS.cs_model;
        assert (ASP.cf_delivered a);
        assert (SMKM.supported_profile_application_record_material_agrees a.client a.server);
        AB.lemma_client_step_appboth_preserves_record_material a.client c' conn_ev;
        assert (AB.record_mat_eq a.client.CS.cs_model.CS.model_record
                                 c'.CS.cs_model.CS.model_record)
      )
    )
#pop-options

(** CLIENT SEND — congruence (B1) + establishment-vacuity (B2).  This is the ONLY
    send/local family that can RAISE the acting endpoint's app-WRITE epoch (the
    client Finished send installs app write), so it does not ride on write-epoch
    preservation.  Split on the PRE-state client write epoch:
      * B1 (already `Application`): with `cf_delivered b`'s `App(rd b.server)`
        (server unchanged) this gives `cf_delivered a`; `agreement a` supplies
        both-App at the client and the client congruence engine carries the
        material across.
      * B2 (not yet `Application`, becomes `Application` at `c'`): the send INSTALLS
        app write — but then the client has just now become the FIRST app-data
        sender, while `cf_delivered b`'s `App(rd a.server)` forces (via the
        epoch->count bridge) the server to have ALREADY received an app-data
        record.  Quiescent byte-pairing transports the counts: the client has sent
        0 app-data records (pre-appdata region) but the server received >= 1.
        `0 == >= 1` is a contradiction, so B2 is VACUOUS.  Epoch-keyed on the
        server side (the bridge is valid at every control), control-pinned on the
        client side via the into-appdata send-Finished shape. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 150 --split_queries always"
let lemma_ama_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_material_agreement b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (w:CW.wire_message) (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns ASP.app_material_agreement b
    with _pf.
    (
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      let ev = SMKM.sent_tls_event sent in
      assert (CS.step_model a.client.CS.cs_model ev == Some c'.CS.cs_model);
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      assert (SMCorr.connection_state_no_key_update_trace c');
      ASP.lemma_sent_not_key_update c' sent;
      let cfg_c = a.client.CS.cs_model.CS.model_config in
      let cfg_s = a.server.CS.cs_model.CS.model_config in
      introduce ASP.cf_delivered b ==>
                  SMKM.supported_profile_application_record_material_agrees b.client b.server
      with _cfd.
      (
        // cf_delivered b : App(wr c') /\ App(rd a.server).  b.server == a.server.
        if R.Application? (wr a.client).R.epoch then
        (
          // B1 CONGRUENCE: App(wr a.client) (branch) + App(rd a.server) (cf b)
          // give cf_delivered a; agreement a supplies all four App at the client.
          assert (ASP.cf_delivered a);
          assert (SMKM.supported_profile_application_record_material_agrees a.client a.server);
          AB.lemma_client_step_appboth_preserves_record_material a.client c' ev;
          assert (AB.record_mat_eq a.client.CS.cs_model.CS.model_record
                                   c'.CS.cs_model.CS.model_record)
        )
        else
        (
          // B2 ESTABLISHMENT-VACUITY.  The send installs app write (~App pre,
          // App post), so it is the client Finished send from HsServerFinishedVerified.
          // ~(a.client @ ControlApplicationData): else its app write epoch would be
          // Application, contradicting the branch.
          introduce a.client.CS.cs_model.CS.model_control == CS.ControlApplicationData ==> False
          with _.
          (
            CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint a.client;
            CSL.lemma_connection_application_ready_record_epochs_installed CS.ClientEndpoint a.client
          );
          ASP.lemma_client_send_installs_app_write_pins a.client.CS.cs_model c'.CS.cs_model sent;
          assert (c'.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          SY.lemma_client_into_appdata_shape a.client local c' out w;
          assert (a.client.CS.cs_model.CS.model_control
                    == CS.ControlHandshaking CS.HsServerFinishedVerified);
          // client sent 0 app-data records (pre-appdata region).
          WStep.lemma_client_preappdata_sent_no_appdata cfg_c a.client;
          // server received >= 1 app-data record (App read epoch, cf b).
          SRRC.lemma_server_app_read_received_ge1 cfg_s a.server;
          // quiescent byte-pairing: client.raw_sent == server.raw_received; counts equal.
          WStep.lemma_raw_appdata_count_seq_equal
            a.client.CS.cs_wire_log.CL.raw_sent a.server.CS.cs_wire_log.CL.raw_received
        )
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    GATE 2a — CONJUNCT 2 preservation: [ASP.client_hs_write_record_slot_link].

    The conjunct reads ONLY [s.client].  SERVER families are therefore trivial
    (client frozen).  CLIENT families re-derive at a non-failed Handshake-write
    client via [CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role],
    and transfer through a fail step (which preserves [model_record] + [hs_keys],
    so the material match survives into [ControlFailed]) otherwise.
    ═══════════════════════════════════════════════════════════════════════════ **)

let match_cw (client:CS.connection_state) : prop =
  SMKM.record_direction_material_matches_key_schedule_for_role
    CS.ClientEndpoint CS.TrafficWrite
    (SMKI.traffic_id CS.TrafficHandshake CS.ClientTraffic) client.CS.cs_model

(** A step whose RESULT lands at [ControlFailed] preserves [model_record] and the
    key schedule (fail is a pure control/failure-field update). **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_step_failed_result_preserves_record_keys
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ce /\ CS.step_model m ce == Some m' /\
        CS.ControlFailed? m'.CS.model_control)
      (ensures
        m'.CS.model_record == m.CS.model_record /\
        m'.CS.model_handshake.CS.hs_keys == m.CS.model_handshake.CS.hs_keys)
  = ()
#pop-options

(** Per-endpoint transfer for conjunct 2 across ANY client step. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_chwsl_client_transfer (ca cb:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent cb /\
        cb.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        (R.Handshake? (wr ca).R.epoch ==> match_cw ca) /\
        WStep.model_stepped ca.CS.cs_model cb.CS.cs_model)
      (ensures (R.Handshake? (wr cb).R.epoch ==> match_cw cb))
  = introduce R.Handshake? (wr cb).R.epoch ==> match_cw cb
    with _hs.
    (
      if CS.ControlFailed? cb.CS.cs_model.CS.model_control then
      (
        eliminate exists (ce:CS.conn_event).
          CS.legal_event ca.CS.cs_model ce /\
          CS.step_model ca.CS.cs_model ce == Some cb.CS.cs_model
        returns match_cw cb
        with _ce.
        (
          lemma_step_failed_result_preserves_record_keys ca.CS.cs_model cb.CS.cs_model ce;
          assert (wr cb == wr ca);
          assert (cb.CS.cs_model.CS.model_handshake.CS.hs_keys
                    == ca.CS.cs_model.CS.model_handshake.CS.hs_keys);
          assert (R.Handshake? (wr ca).R.epoch)
        )
      )
      else
      (
        CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role cb;
        assert (SMKM.model_record_keys_consistent_for_role CS.ClientEndpoint cb.CS.cs_model);
        CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
          CS.ClientEndpoint CS.TrafficWrite cb.CS.cs_model;
        assert (SMKI.traffic_id CS.TrafficHandshake
                  (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite)
                  == SMKI.traffic_id CS.TrafficHandshake CS.ClientTraffic)
      )
    )
#pop-options

(** CONJUNCT 2 — SERVER SEND (trivial: client frozen). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_chwsl_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.client_hs_write_record_slot_link a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.client_hs_write_record_slot_link b)
  = SY.lemma_server_send_shape a b
#pop-options

(** CONJUNCT 2 — SERVER LOCAL (trivial: client frozen). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_chwsl_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.client_hs_write_record_slot_link a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_local a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.client_hs_write_record_slot_link b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns ASP.client_hs_write_record_slot_link b
    with _pf. ()
#pop-options

(** CONJUNCT 2 — DELIVER TO SERVER (trivial: client frozen). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_chwsl_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.client_hs_write_record_slot_link a /\
        SY.tls_step_deliver_to_server a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.client_hs_write_record_slot_link b)
  = SY.lemma_deliver_to_server_shape a b
#pop-options

(** CONJUNCT 2 — CLIENT SEND (re-derive / fail transfer). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_chwsl_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.client_hs_write_record_slot_link a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.client_hs_write_record_slot_link b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (w:CW.wire_message) (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns ASP.client_hs_write_record_slot_link b
    with _pf.
    (
      WStep.lemma_client_step_model_stepped a.client (SM.LocalEvent local) c' out;
      lemma_chwsl_client_transfer a.client c'
    )
#pop-options

(** CONJUNCT 2 — CLIENT LOCAL (re-derive / fail transfer). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_chwsl_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.client_hs_write_record_slot_link a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_local a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.client_hs_write_record_slot_link b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns ASP.client_hs_write_record_slot_link b
    with _pf.
    (
      WStep.lemma_client_step_model_stepped a.client (SM.LocalEvent local) c' out;
      lemma_chwsl_client_transfer a.client c'
    )
#pop-options

(** CONJUNCT 2 — DELIVER TO CLIENT (re-derive / fail transfer). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_chwsl_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.client_hs_write_record_slot_link a /\
        SY.tls_step_deliver_to_client a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.client_hs_write_record_slot_link b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns ASP.client_hs_write_record_slot_link b
    with _pf.
    (
      WStep.lemma_client_step_model_stepped a.client (SM.WireEvent wire) c' out;
      lemma_chwsl_client_transfer a.client c'
    )
#pop-options
