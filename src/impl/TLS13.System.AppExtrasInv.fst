module TLS13.System.AppExtrasInv

(** ─────────────────────────────────────────────────────────────────────────
    APP-EXTRAS STEP-PRESERVATION AGGREGATION + STREAM-2 INVARIANT LAYER.

    This module is DOWNSTREAM of `TLS13.System` (SY), `TLS13.System.AppSeqPairing`
    (ASP, which DEFINES `app_extras`), `TLS13.System.HsMaterialFamilies` (HMF) and
    `TLS13.System.AppMaterialFamilies` (AMF) — the three modules that hold the
    per-conjunct step families.  The aggregation `lemma_app_extras_preserved` must
    call families from all three, so it CANNOT live in ASP (which they import); it
    lives here.  `stream2_combined_inv` layers `app_extras` (gated by
    `tls_no_rekeying`) on top of `stream_combined_inv`, so `TLS13.System.fst` and
    its 26-conjunct `tls_system_inv` stay BYTE-IDENTICAL.
    ───────────────────────────────────────────────────────────────────────── **)

module CS   = TLS13.Spec.StateMachine
module M    = TLS13.Messages
module CL   = TLS13.ConnectionLog
module B    = TLS13.Bytes
module Seq  = FStar.Seq
module R    = TLS13.Record.Spec
module RF   = TLS13.Spec.StateMachine.RecordFraming
module MP   = Common.MachineProduct
module SY   = TLS13.System
module SMCan = TLS13.Spec.StateMachine.Canonical
module CSL  = TLS13.ConnectionState.Lemmas
module RKE  = TLS13.ConnectionState.RecordKeyEpoch
module W    = TLS13.Wire.Spec
module T    = TLS13.Types
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module SMCorr = TLS13.Spec.StateMachine.Correspondence
module SMR  = TLS13.Spec.StateMachine.Reachability
module SM   = Common.StateMachine
module CW   = TLS13.Spec.Endpoint.Wire
module CTy  = TLS13.Impl.CanonicalTypes
module EC   = TLS13.Spec.Endpoint.Client
module ES   = TLS13.Spec.Endpoint.Server
module EAPI = TLS13.Spec.Endpoint.API
module L    = FStar.List.Tot
module WStep = TLS13.System.WireStep
module WF   = Common.WireFormat
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module HANR = TLS13.ConnectionState.HandshakeAgreementNonReady
module WFL  = TLS13.Spec.WireFormatLemmas
module SLM  = TLS13.System.SlotMono
module ASP  = TLS13.System.AppSeqPairing
module HSP  = TLS13.System.HsSeqPairing
module HMF  = TLS13.System.HsMaterialFamilies
module AMF  = TLS13.System.AppMaterialFamilies
module ORD  = TLS13.System.Ordering
module SNCFR = TLS13.System.ServerNotCFR
module GFin = TLS13.Wire.Generated.Finished
module ID   = FStar.IndefiniteDescription
module RTC  = FStar.ReflexiveTransitiveClosure
module ADBE = TLS13.ConnectionState.AppDataBufferEmpty

(** ─────────────────────────────────────────────────────────────────────────
    COMPANION to `finished_delivered_appread_coupling` (fdac).  NOT a replacement:
    fdac's first half stays in ASP.app_extras.  These pin the identity of the
    in-flight Finished so fdac's delivery-preservation can conclude app-read.

    WHY A MESSAGE-IDENTITY CLAUSE, NOT A CONTROL PIN: the control-level alternative
    (an `sf_flight_lockstep` pinning the client control at each flight stage) needs
    FOUR two-control disjunctions, because the client's follow-up locals
    (LocalValidateCertificate @StateMachine.fst:529, LocalVerifyCertificateSignature
    @:531) require Quiet, so the server can legally send CV/SF while the client sits
    at the pre-local control (HsCertificateReceived / HsCertificateVerifyReceived) and
    the delivery then BLOCKS (:822).  The successful-delivery hypothesis subsumes those
    blocked cases: since StateMachine.fst:738 is the UNIQUE successful client
    Finished-receive arm and it installs app-read, a Finished that delivers
    successfully MUST have fired :738 -> the control is DERIVED from the step, not
    pinned.  So no control-consequent, no closure/monotone-leak surface, one gate.

    MUTUAL INDUCTION: preserved JOINTLY with fdac.  `sf_inflight_finished`'s
    server_send preservation uses fdac's first half at the pre-Quiet to exclude the
    "SF already sent" case; fdac's deliver_to_client preservation uses
    `sf_inflight_finished` at the pre-ToClient state.  Neither is standalone. **)
let sf_inflight_finished (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToClient p ->
      ( ~ (R.Application? (ASP.rd s.client).R.epoch)
        /\ Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished )
      ==> ( M.TlsHandshake? p.SY.pl_sent /\ M.Finished? (M.TlsHandshake?._0 p.SY.pl_sent) )
  | _ -> True

let cf_inflight_finished (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      ( ~ (R.Application? (ASP.rd s.server).R.epoch)
        /\ Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_client_finished )
      ==> ( M.TlsHandshake? p.SY.pl_sent /\ M.Finished? (M.TlsHandshake?._0 p.SY.pl_sent) )
  | _ -> True

(** Pure step facts: the UNIQUE `step_tls_message _ Sent _` arms that take the
    server's / client's `hs_*_finished` field from `None` to `Some` are the
    Finished sends (StateMachine.fst:685 / :818); every other `Sent` arm preserves
    the field.  Hence a `Sent` step that installs the field carries a Finished. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 40"
let lemma_send_none_to_some_server_finished
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent sent == Some m' /\
        None? m.CS.model_handshake.CS.hs_server_finished /\
        Some? m'.CS.model_handshake.CS.hs_server_finished)
      (ensures M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent))
  = ()
#pop-options

#push-options "--fuel 3 --ifuel 8 --z3rlimit 40"
let lemma_send_none_to_some_client_finished
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent sent == Some m' /\
        None? m.CS.model_handshake.CS.hs_client_finished /\
        Some? m'.CS.model_handshake.CS.hs_client_finished)
      (ensures M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent))
  = ()
#pop-options

(** A `Received` Finished that STEPS SUCCESSFULLY installs the application READ
    epoch.  The only two `step_handshake_message` arms accepting a `CL.Received`
    `M.Finished` are the client Finished-receive at `HsCertificateVerifyVerified`
    (StateMachine.fst:738) and the server Finished-receive at `HsServerFinishedSent`
    (:782); BOTH `R.install_keys ... R.Application ...` the read direction (or block
    on a `None` master secret, contradicting `Some m'`).  Hence any successful
    Finished receive lands the READ epoch at `Application`.  Role-free — used at the
    client SF-delivery, where the received message is pinned to the in-flight
    Finished by faithful decode. **)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 40"
let lemma_recv_finished_installs_app_read
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Received msg == Some m' /\
        M.TlsHandshake? msg /\ M.Finished? (M.TlsHandshake?._0 msg))
      (ensures R.Application? m'.CS.model_record.CS.record_read.R.epoch)
  = ()
#pop-options

(** A successful PROTECTED-message decode forces the reader's record READ key to
    be present.  [SMCan.received_single_protected_message_decode] existentially
    opens the record via [R.open_record record_read ...], which returns [Some]
    ONLY in its [Some key, Some iv] branch (Record.Spec.fst:47).  Hence any peer
    that faithfully decodes an in-flight protected record HAS a read key — which,
    composed with [RKE.lemma_connection_consistent_read_key_present_not_initial],
    excludes the [Initial] read epoch UNIFORMLY (including at [ControlFailed],
    where the control-gated key-schedule projection is vacuous).  This is the fact
    that lets the SF/CF delivery arms fire their handshake-sealed bridge without a
    (false) single-endpoint control->key brick. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_protected_decode_read_key_present
  (model:CS.connection_model) (msg:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires SMCan.received_single_protected_message_decode model msg raw)
      (ensures Some? model.CS.model_record.CS.record_read.R.key)
  = ()
#pop-options

(** HEAD REFUTATION UNDER AN EMPTY BYTE DELTA (the `ConnProtectedHandshake`
    companion for every LOCAL family in this module).

    `CS.event_raw_delta_legal` charges a HEAD protected-handshake step with
    `CS.raw_records_exactly raw_received T.Application_data 1`, i.e. exactly one
    `Application_data` record; with `raw_received == B.empty` the appdata count is
    `0 =!= 1`.  So under an empty byte delta only TAIL steps survive, and a TAIL
    step RESTORES `record_read` from the pre-state for every non-`Finished`
    message (`Finished` installs the `R.Application` read epoch), leaves
    `record_write` alone, and otherwise writes only the `hb_*` handshake buffers
    via `CS.set_pending_protected_handshake`. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_protected_head_impossible_empty
  (m:CS.connection_model) (step:CS.protected_handshake_step)
  : Lemma
      (requires CS.event_raw_delta_legal m (CS.ConnProtectedHandshake step) B.empty B.empty)
      (ensures step.CS.protected_handshake_head == false)
  = if step.CS.protected_handshake_head
    then (WStep.lemma_protected_raw_count_one B.empty;
          WStep.lemma_raw_appdata_count_empty ())
#pop-options

(** Skeleton sanity lemma — confirms the module compiles and is wired into the
    build.  Replaced/kept as the families and aggregation land. **)
let _appextrasinv_wired (s:SY.tls_system_state)
  : Lemma (requires ASP.app_extras s) (ensures ASP.app_extras s)
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    FORWARD EPOCH-PRESERVATION PRIMITIVES.

    An endpoint's empty-byte-delta step (a LOCAL family) preserves the
    Application read/write epoch FORWARD (`App` at the pre-state ⟹ `App` at the
    post-state).  The only record-mutating step_local_event arms are key installs,
    legal ONLY at `ControlHandshaking` stages: a handshake-epoch install sits at
    `HsServerHelloReceived`/`HsServerHelloSent` (where the corresponding epoch is
    NOT yet `Application`, by the reachable shape) and an application-epoch install
    RAISES the epoch to `Application` (so `App` is preserved).  A ConnNetworkEvent
    with empty delta leaves `model_record` unchanged
    (`lemma_network_empty_delta_record_unchanged_ungated`).
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_client_local_preserves_app_read
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty /\
        R.Application? (ASP.rd st).R.epoch)
      (ensures R.Application? (ASP.rd st').R.epoch)
  = match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev ->
      (match st.CS.cs_model.CS.model_control with
       | CS.ControlHandshaking CS.HsServerFinishedVerified -> ()
       | CS.ControlHandshaking CS.HsClientFinishedReceived -> ()
       | CS.ControlHandshaking _ ->
         CSL.lemma_handshaking_nonfinal_read_not_application st
       | _ -> ())
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM.  Empty byte delta ==> TAIL step (head refuted); a tail step
         restores/raises the read slot, freezes the write slot, and writes only the
         `hb_*` buffers. *)
      lemma_protected_head_impossible_empty st.CS.cs_model step
#pop-options

#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_server_local_preserves_app_read
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty /\
        R.Application? (ASP.rd st).R.epoch)
      (ensures R.Application? (ASP.rd st').R.epoch)
  = match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev ->
      (match st.CS.cs_model.CS.model_control with
       | CS.ControlHandshaking CS.HsServerFinishedVerified -> ()
       | CS.ControlHandshaking CS.HsClientFinishedReceived -> ()
       | CS.ControlHandshaking _ ->
         CSL.lemma_handshaking_nonfinal_read_not_application st
       | _ -> ())
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM, STRUCTURALLY VACUOUS.  `CS.legal_protected_handshake_step` pins
         `model_config.config_role == CS.ClientEndpoint` as its FIRST conjunct, so a
         SERVER can never take a protected-handshake step. *)
      ()
#pop-options


(** ─────────────────────────────────────────────────────────────────────────
    Finished-FIELD preservation across a LOCAL step (empty byte-delta).

    The client's own `hs_client_finished` is written ONLY by
    `LocalVerifyClientFinished` (StateMachine.fst:567) — which is SERVER-role-only
    (`legal_local_event` guard, StateMachine.fst:1279) — and by the client SEND of
    its Finished (StateMachine.fst:818, a NON-empty wire step, excluded from the
    local family).  Symmetrically the server's own `hs_server_finished` is written
    ONLY by `LocalVerifyFinished` (:556) — CLIENT-role-only (:1272) — and by the
    server SEND (:685).  A ConnNetworkEvent with empty byte-delta is cleartext
    (protected records have positive count) and its cleartext arms never touch the
    Finished fields; `fail_model` (:303) preserves every handshake field.  Hence a
    same-role local step leaves the endpoint's OWN Finished field unchanged.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 4 --ifuel 8 --z3rlimit 120 --split_queries always"
let lemma_client_local_preserves_client_finished
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty)
      (ensures
        st'.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
        st.CS.cs_model.CS.model_handshake.CS.hs_client_finished)
  = match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM.  Empty byte delta ==> TAIL step (head refuted); a tail step
         restores/raises the read slot, freezes the write slot, and writes only the
         `hb_*` buffers. *)
      lemma_protected_head_impossible_empty st.CS.cs_model step
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 120 --split_queries always"
let lemma_server_local_preserves_server_finished
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty)
      (ensures
        st'.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        st.CS.cs_model.CS.model_handshake.CS.hs_server_finished)
  = match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM, STRUCTURALLY VACUOUS.  `CS.legal_protected_handshake_step` pins
         `model_config.config_role == CS.ClientEndpoint` as its FIRST conjunct, so a
         SERVER can never take a protected-handshake step. *)
      ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    fdac LOCAL families.  Channel stays `Quiet`, so BOTH halves are active at `b`.
    The acting endpoint moves; the PEER is frozen (`b.server == a.server` for a
    client local).  First half: consequent `App(rd b.client)` — under the
    antecedent `Some? b.server.hs_server_finished` (= a.server, frozen), `fdac a`'s
    first half (a is `Quiet`, so `~ToClient`) gives `App(rd a.client)`, forwarded
    across the client move by `lemma_client_local_preserves_app_read`.  Second half:
    antecedent `Some? b.client.hs_client_finished`; the client's own
    `hs_client_finished` is preserved by `lemma_client_local_preserves_client_finished`
    (role-restricted), so `fdac a`'s second half gives `App(rd a.server)` =
    `App(rd b.server)` (server frozen).  Server local is the mirror. **)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_fdac_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.finished_delivered_appread_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b)
      (ensures ASP.finished_delivered_appread_coupling b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns ASP.finished_delivered_appread_coupling b
    with _pf.
    (
      ASP.lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      returns ASP.finished_delivered_appread_coupling b
      with _pe.
      (
        introduce
          Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished
          ==> R.Application? (ASP.rd b.client).R.epoch
        with _. lemma_client_local_preserves_app_read a.client c' ce;
        lemma_client_local_preserves_client_finished a.client c' ce
      )
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_fdac_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.finished_delivered_appread_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b)
      (ensures ASP.finished_delivered_appread_coupling b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns ASP.finished_delivered_appread_coupling b
    with _pf.
    (
      ASP.lemma_server_local_extract a.server s' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      returns ASP.finished_delivered_appread_coupling b
      with _pe.
      (
        introduce
          Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_client_finished
          ==> R.Application? (ASP.rd b.server).R.epoch
        with _. lemma_server_local_preserves_app_read a.server s' ce;
        lemma_server_local_preserves_server_finished a.server s' ce
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    fdac SEND families.  A `client_send` lands `ToServer`, so the SECOND half
    (gated `~ToServer`) is VACUOUS at `b`.  The FIRST half is active: the server is
    frozen (`b.server == a.server`), so the antecedent equals `a`'s; the client's
    READ epoch is unchanged by a SENT step (`lemma_sent_preserves_read_epoch` via
    `lemma_client_send_pins_model`), so `fdac a`'s first half (a is `Quiet`) carries
    `App(rd a.client)` to `App(rd b.client)`.  Server send is the mirror. **)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_fdac_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.finished_delivered_appread_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b)
      (ensures ASP.finished_delivered_appread_coupling b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns ASP.finished_delivered_appread_coupling b
    with _pf.
    (
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      AMF.lemma_sent_preserves_read_epoch a.client.CS.cs_model sent c'.CS.cs_model
    )
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_fdac_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.finished_delivered_appread_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b)
      (ensures ASP.finished_delivered_appread_coupling b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns ASP.finished_delivered_appread_coupling b
    with _pf.
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      AMF.lemma_sent_preserves_read_epoch a.server.CS.cs_model sent s'.CS.cs_model
    )
#pop-options

(** A CLIENT network RECEIVE preserves the client's `hs_client_finished` witness.
    The ONLY `step_tls_message` `Received` arm that writes `hs_client_finished` is
    the SERVER CF-receive at `HsServerFinishedSent` (StateMachine.fst:788), whose
    legality REQUIRES `ServerEndpoint` (legal_handshake_message, :1377); so a legal
    CLIENT receive cannot be at that control, and every other `Received` arm leaves
    the field untouched.  ROLE + LEGALITY are load-bearing (they exclude the
    server-only arm, exactly as `lemma_client_local_preserves_client_finished` uses
    them for the LocalVerifyClientFinished arm).  Used at fdac's `deliver_to_client`
    SECOND half to forward `Some? hs_client_finished` unchanged across the receive. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_recv_preserves_client_finished
  (st st':CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_tls_message st.CS.cs_model CL.Received msg /\
        CS.step_tls_message st.CS.cs_model CL.Received msg == Some st'.CS.cs_model)
      (ensures
        st'.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
        st.CS.cs_model.CS.model_handshake.CS.hs_client_finished)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    fdac DELIVER-TO-CLIENT — THE FIRST CRUX.

    `deliver_to_client` consumes the in-flight `ToClient` payload (sealed by the
    SERVER) and steps the CLIENT; channel `ToClient -> Quiet`, so BOTH halves of
    fdac are active at `b` (`b.client = c'`, `b.server = a.server` frozen).

    SECOND half (passive): `Some? c'.hs_client_finished ==> App(rd a.server)`.  A
    client RECEIVE never touches `hs_client_finished`
    (`lemma_recv_preserves_client_finished`), so `c'.hs_client_finished ==
    a.client.hs_client_finished`; then `fdac a`'s second half (a is `ToClient`, so
    `~ToServer`) carries `App(rd a.server) = App(rd b.server)` (server frozen).

    FIRST half (the crux): `Some? a.server.hs_server_finished ==> App(rd c')`.  Case
    split on the PRE-state client READ epoch `R.Application? (rd a.client)`:
      * APP case: the receive is monotone — `lemma_recv_app_preserves_record_material`
        (needs `~KeyUpdate`, from `lemma_recv_not_key_update`) forwards `App(rd c')`
        unconditionally (does not even use the antecedent).
      * ~APP case (RECORD-LEVEL faithful decode, mirror of
        `HSP.lemma_hsp_deliver_to_client`'s non-cleartext branch): under the
        antecedent, `sf_inflight_finished a` (ToClient, `~App(rd a.client)`, `Some?
        hs_server_finished`) pins `sent` to a Finished.  A Finished is a non-cleartext
        `TlsHandshake`, so the CARRIED clause `inflight_snap_handshake_write a` hands
        the SLOT->RECORD SNAPSHOT gate `Handshake?(snap_wr p)` (established at the
        send, consumed here — see the clause's ordering note).  `inflight_raw_delta_legal`
        + `inflight_single_record` make `raw` a single `Application_data` record, so
        the received `msg` is not cleartext (`HSP.lemma_hsp_client_recv_not_cleartext`,
        control/epoch-free), whence the projection yields
        `received_single_protected_message_decode a.client msg raw`.  From that
        decode `lemma_protected_decode_read_key_present` gives `Some? (rd a.client).key`,
        and `RKE.lemma_connection_consistent_read_key_present_not_initial` gives
        `~Initial(rd a.client)`; with the ~App case that is `Handshake?(rd a.client)`
        — the RECORD-level read gate.  Both gate halves in hand, `hs_channel_seal_ok a`
        fires the bridge and `sc_hs_seq_ok a` (now ~terminal-free) supplies the
        cross-endpoint seq alignment `snap.write.seq == a.client.read.seq`; the
        peer-decode lemma then pins `msg == sent = Finished`, and
        `lemma_recv_finished_installs_app_read` (role-free) lands `App(rd c')`.  The
        `ControlFailed` sub-case is subsumed by that last lemma (a Finished into a
        failed peer blocks, contradicting `step == Some c'`). **)
(** ═══════════════════════════════════════════════════════════════════════
    COALESCED PROTECTED-HANDSHAKE DELIVERY HELPERS (agentic's new client wire arm).

    `origin/agentic` extended `EC.client_wire_received_event` so a delivered record
    may be consumed by a HEAD `CS.ConnProtectedHandshake` step rather than a
    `ConnNetworkEvent`.  These five model-level helpers are what the new arm of
    `lemma_fdac_deliver_to_client` needs; each is the protected-step analogue of the
    `ConnNetworkEvent` helper it sits next to.
    ═══════════════════════════════════════════════════════════════════════ **)

(** Slice-of-everything, needed to line the two decode predicates up. **)
let lemma_slice_all (f:B.bytes) : Lemma (Seq.slice f 0 (B.length f) == f)
  = Seq.lemma_eq_elim (Seq.slice f 0 (B.length f)) f

(** (H1) A HEAD protected-handshake decode OPENS the record under the receiver's
    READ state, so the read key is present.  Analogue of
    `lemma_protected_decode_read_key_present`. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_protected_head_decode_read_key_present
  (model:CS.connection_model) (step:CS.protected_handshake_step) (raw:B.bytes)
  : Lemma
      (requires SMCan.received_protected_handshake_head_decode model step raw)
      (ensures Some? model.CS.model_record.CS.record_read.R.key)
  = ()
#pop-options

(** Inversion of `W.parse_tls_message` at `T.Handshake`: it succeeds ONLY via the
    `W.parse_handshake` arm with FULL consumption, so a successful parse and a
    successful `parse_handshake` of the same bytes agree on the message. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_parse_tls_handshake_inv
  (f:B.bytes) (hm0 hm:M.handshake_msg) (n:nat)
  : Lemma
      (requires
        W.parse_tls_message T.Handshake f == Some (M.TlsHandshake hm0) /\
        W.parse_handshake f == Some (hm, n))
      (ensures hm0 == hm)
  = W.lemma_parse_tls_message_handshake_some f hm0
#pop-options

(** (H2) THE RECORD -> MESSAGE BRIDGE for a HEAD step.  If the SAME record `raw`
    both single-protected-message-decodes to `sent` and head-decodes to `step`, then
    `sent` IS the step's handshake message.

    Everything in sight is FUNCTIONAL: `W.parse_record_wire raw` pins the outer
    fragment; `R.open_record` (a function of the read state, the header AAD and the
    outer fragment) pins `opened`; `W.parse_plaintext opened` pins the plaintext.
    The head decode then says `plaintext.fragment == step.protected_handshake_fragment`
    and (at `offset == 0`, which `CS.legal_protected_handshake_step` forces on a HEAD
    step) `W.parse_handshake` of that whole fragment yields
    `step.protected_handshake_message`; the single-message decode says
    `W.parse_tls_message T.Handshake plaintext.fragment == Some sent`, which unfolds
    to the SAME `W.parse_handshake` call with full consumption.  Injectivity of
    `Some` closes it. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 300 --split_queries always"
let lemma_protected_head_decode_functional
  (model:CS.connection_model) (step:CS.protected_handshake_step)
  (sent:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        SMCan.received_single_protected_message_decode model sent raw /\
        SMCan.received_protected_handshake_head_decode model step raw /\
        step.CS.protected_handshake_offset == 0 /\
        M.TlsHandshake? sent)
      (ensures M.TlsHandshake?._0 sent == step.CS.protected_handshake_message)
  = lemma_slice_all step.CS.protected_handshake_fragment;
    eliminate exists (of1:B.bytes) (op1:B.bytes) (pl1:M.plaintext).
      (W.parse_record_wire raw == Some (T.Application_data, of1, B.length raw) /\
       SMCan.received_record_opened model raw of1 op1 /\
       W.parse_plaintext op1 == Some pl1 /\
       W.parse_tls_message pl1.M.content_type pl1.M.fragment == Some sent)
    returns M.TlsHandshake?._0 sent == step.CS.protected_handshake_message
    with _h1.
    (
      eliminate exists (of2:B.bytes) (op2:B.bytes) (pl2:M.plaintext).
        (W.parse_record_wire raw == Some (T.Application_data, of2, B.length raw) /\
         SMCan.received_record_opened model raw of2 op2 /\
         W.parse_plaintext op2 == Some pl2 /\
         pl2.M.content_type == T.Handshake /\
         Seq.equal pl2.M.fragment step.CS.protected_handshake_fragment /\
         step.CS.protected_handshake_offset <=
           B.length step.CS.protected_handshake_fragment /\
         W.parse_handshake
           (Seq.slice
             step.CS.protected_handshake_fragment
             step.CS.protected_handshake_offset
             (B.length step.CS.protected_handshake_fragment)) ==
           Some
             (step.CS.protected_handshake_message,
              step.CS.protected_handshake_consumed))
      returns M.TlsHandshake?._0 sent == step.CS.protected_handshake_message
      with _h2.
      (
        (* `W.parse_record_wire raw` is a FUNCTION: `of1 == of2`. *)
        assert (of1 == of2);
        (* `R.open_record` is a FUNCTION of the read state, the header AAD and the
           outer fragment, so the two openings coincide: `op1 == op2`. *)
        assert (SMCan.received_record_opened model raw of1 op1);
        assert (SMCan.received_record_opened model raw of1 op2);
        eliminate exists (rs1:R.direction_state).
          (R.open_record model.CS.model_record.CS.record_read
             (SMCan.record_header_aad raw) of1 == Some (op1, rs1))
        returns op1 == op2
        with _r1.
        (
          eliminate exists (rs2:R.direction_state).
            (R.open_record model.CS.model_record.CS.record_read
               (SMCan.record_header_aad raw) of1 == Some (op2, rs2))
          returns op1 == op2
          with _r2. ()
        );
        assert (pl1 == pl2);
        Seq.lemma_eq_elim pl2.M.fragment step.CS.protected_handshake_fragment;
        assert (W.parse_handshake step.CS.protected_handshake_fragment ==
                  Some (step.CS.protected_handshake_message,
                        step.CS.protected_handshake_consumed));
        assert (W.parse_tls_message T.Handshake
                  step.CS.protected_handshake_fragment == Some sent);
        lemma_parse_tls_handshake_inv
          step.CS.protected_handshake_fragment
          (M.TlsHandshake?._0 sent)
          step.CS.protected_handshake_message
          step.CS.protected_handshake_consumed
      )
    )
#pop-options

(** (H3) A protected-handshake step carrying a `Finished` installs the APPLICATION
    read epoch -- `CS.step_protected_handshake` does NOT restore `record_read` on the
    `Finished` arm (head or tail), so the install from
    `CS.step_handshake_message _ CL.Received (M.Finished _)` survives. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_protected_finished_installs_app_read
  (m m':CS.connection_model) (step:CS.protected_handshake_step)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnProtectedHandshake step) /\
        CS.step_model m (CS.ConnProtectedHandshake step) == Some m' /\
        M.Finished? step.CS.protected_handshake_message)
      (ensures R.Application? m'.CS.model_record.CS.record_read.R.epoch)
  = ()
#pop-options

(** (H4) APPLICATION read epoch preserved FORWARD.  EE / Cert / CV advance
    `record_read` with `R.next_seq` (epoch-preserving) or restore it from the
    pre-state (tail); `Finished` installs `R.Application`.  Either way `App` in,
    `App` out. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_protected_preserves_app_read
  (m m':CS.connection_model) (step:CS.protected_handshake_step)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnProtectedHandshake step) /\
        CS.step_model m (CS.ConnProtectedHandshake step) == Some m' /\
        R.Application? m.CS.model_record.CS.record_read.R.epoch)
      (ensures R.Application? m'.CS.model_record.CS.record_read.R.epoch)
  = ()
#pop-options

(** (H5) The CLIENT's own `hs_client_finished` is untouched.  A protected-handshake
    step is a `CL.Received` handshake step, and the only writers of
    `hs_client_finished` are `LocalVerifyClientFinished` (server-role local) and the
    client's own SEND of its Finished. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_protected_preserves_client_finished
  (m m':CS.connection_model) (step:CS.protected_handshake_step)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnProtectedHandshake step) /\
        CS.step_model m (CS.ConnProtectedHandshake step) == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_client_finished ==
        m.CS.model_handshake.CS.hs_client_finished)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_fdac_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        SY.tls_step_deliver_to_client a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.finished_delivered_appread_coupling b)
  = SY.lemma_deliver_to_client_shape a b;
    assert (ASP.finished_delivered_appread_coupling a);
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns ASP.finished_delivered_appread_coupling b
    with _pf.
    (
      let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
      assert (a.channel == MP.ToClient p);
      EC.lemma_client_wire_step_inversion #CTy.client_local_event a.client c' wire out;
      eliminate exists (conn_ev0:CS.conn_event).
        (EC.client_wire_received_event a.client wire conn_ev0 /\
         SMCan.canonical_wire_step a.client c' conn_ev0
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev0 out.SM.so_local_outputs)
      returns ASP.finished_delivered_appread_coupling b
      with _inv.
      (
        match conn_ev0 with
        | CS.ConnLocalEvent _ ->
          (* `EC.client_wire_received_event` is `False` on a local event. *)
          ()
        | CS.ConnProtectedHandshake step ->
          (* NEW ARM.  The delivered record is consumed by a HEAD protected-handshake
             step.  SECOND half is passive (H5).  FIRST half splits on the PRE-state
             client read epoch exactly as the `ConnNetworkEvent` arm does:
               * APP: monotone forward by (H4);
               * ~APP: the in-flight message is pinned to a `Finished` by
                 `sf_inflight_finished a`; the HEAD decode opens the record under the
                 client's read state, giving the read key (H1) and hence — with ~APP
                 — the RECORD-level gate `Handshake?(rd a.client)`; the carried
                 `inflight_snap_handshake_write` gives the snapshot half; the seal
                 bridge then yields the single-message decode of the SAME record, and
                 (H2) identifies the step's handshake message WITH the sealed
                 `Finished`; (H3) lands `App(rd c')`. *)
          Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
          assert (step.CS.protected_handshake_head);
          assert (CS.legal_event a.client.CS.cs_model conn_ev0);
          assert (CS.step_model a.client.CS.cs_model conn_ev0 == Some c'.CS.cs_model);
          lemma_protected_preserves_client_finished
            a.client.CS.cs_model c'.CS.cs_model step;
          introduce
            Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished
            ==> R.Application? (ASP.rd c').R.epoch
          with _hsf.
          (
            if R.Application? (ASP.rd a.client).R.epoch then
              lemma_protected_preserves_app_read
                a.client.CS.cs_model c'.CS.cs_model step
            else
            (
              assert (M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent));
              assert (~(CS.network_message_is_cleartext CL.Sent sent));
              assert (ASP.inflight_snap_handshake_write a);
              assert (R.Handshake? (ASP.snap_wr p).R.epoch);
              assert (ASP.inflight_raw_delta_legal a /\ ASP.inflight_single_record a);
              assert (CS.network_message_raw_delta_legal snap
                        ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw);
              assert (CS.raw_records_exactly raw T.Application_data 1);
              HSP.lemma_rre_nonempty raw;
              (* HEAD decode projection of the client's own wire step. *)
              assert (SMCan.received_protected_handshake_head_decode
                        a.client.CS.cs_model step raw);
              lemma_protected_head_decode_read_key_present a.client.CS.cs_model step raw;
              RKE.lemma_connection_consistent_read_key_present_not_initial a.client;
              assert (R.Handshake? (ASP.rd a.client).R.epoch);
              assert (ASP.inflight_bridge_ready snap a.client.CS.cs_model sent raw);
              CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
                snap a.client.CS.cs_model sent raw;
              assert (step.CS.protected_handshake_offset == 0);
              lemma_protected_head_decode_functional
                a.client.CS.cs_model step sent raw;
              assert (M.TlsHandshake? sent);
              assert (M.Finished? step.CS.protected_handshake_message);
              lemma_protected_finished_installs_app_read
                a.client.CS.cs_model c'.CS.cs_model step
            )
          )
        | CS.ConnNetworkEvent tm ->
        let msg : M.tls_message = tm.CL.message_value in
        let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
        assert (conn_ev0 == conn_ev);
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        assert (CS.step_tls_message a.client.CS.cs_model CL.Received msg == Some c'.CS.cs_model);
        // SECOND half (passive): a client RECEIVE preserves `hs_client_finished`, so
        // `fdac a`'s second half transfers (server frozen).  ROLE + LEGALITY (from
        // `canonical_wire_step`) exclude the server-only CF-receive arm.
        assert (a.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert (CS.legal_tls_message a.client.CS.cs_model CL.Received msg);
        lemma_recv_preserves_client_finished a.client c' msg;
        // FIRST half (crux).
        introduce
          Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished
          ==> R.Application? (ASP.rd c').R.epoch
        with _hsf.
        (
          if R.Application? (ASP.rd a.client).R.epoch then
          (
            // APP case: monotone forward, unconditional.
            ASP.lemma_recv_not_key_update c' msg;
            ASP.lemma_recv_app_preserves_record_material a.client c' msg
          )
          else
          (
            // ~APP case: RECORD-LEVEL faithful decode.
            // sf_inflight_finished a (ToClient, ~App(rd a.client), Some? hs_server_finished):
            assert (M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent));
            // A Finished is a non-cleartext TlsHandshake -> the carried snapshot gate.
            assert (~(CS.network_message_is_cleartext CL.Sent sent));
            assert (ASP.inflight_snap_handshake_write a);
            assert (R.Handshake? (ASP.snap_wr p).R.epoch);
            // `raw` is a single Application_data record (send-side, non-cleartext).
            assert (ASP.inflight_raw_delta_legal a /\ ASP.inflight_single_record a);
            assert (CS.network_message_raw_delta_legal snap
                      ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw);
            assert (CS.raw_records_exactly raw T.Application_data 1);
            HSP.lemma_rre_nonempty raw;
            CSL.lemma_raw_records_exactly_one_parse_record raw T.Application_data;
            W.lemma_parse_record_implies_parse_record_wire raw;
            // received `msg` is not cleartext (control/epoch-free helper).
            assert (CS.network_message_raw_delta_legal a.client.CS.cs_model
                      ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw);
            HSP.lemma_hsp_client_recv_not_cleartext a.client msg c'.CS.cs_model raw;
            assert (CS.network_message_is_cleartext CL.Received msg == false);
            // projection (~cleartext branch) -> the decode.
            assert (SMCan.received_single_protected_message_decode a.client.CS.cs_model msg raw);
            // RECORD-level read gate: decode -> key present -> ~Initial -> (with ~App) Handshake.
            lemma_protected_decode_read_key_present a.client.CS.cs_model msg raw;
            RKE.lemma_connection_consistent_read_key_present_not_initial a.client;
            assert (R.Handshake? (ASP.rd a.client).R.epoch);
            // Fire the bridge (hs_channel_seal_ok a) and the seq alignment (sc_hs_seq_ok a).
            assert (ASP.inflight_bridge_ready snap a.client.CS.cs_model sent raw);
            assert (HSP.snap_hs_wseq p == HSP.hs_rseq a.client);
            assert (snap.CS.model_record.CS.record_write.R.seq ==
                    a.client.CS.cs_model.CS.model_record.CS.record_read.R.seq);
            // FAITHFUL DECODE: msg == sent = Finished.
            CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
              snap a.client.CS.cs_model sent raw;
            ASP.lemma_decode_functional a.client.CS.cs_model msg sent raw;
            assert (msg == sent);
            // Finished receive installs App read epoch (role-free; ControlFailed blocks).
            lemma_recv_finished_installs_app_read a.client.CS.cs_model c'.CS.cs_model msg
          )
        )
      )
    )
#pop-options

(** A SERVER network RECEIVE preserves the server's `hs_server_finished` witness.
    Mirror of `lemma_recv_preserves_client_finished`: the ONLY `step_tls_message`
    `Received` arm that writes `hs_server_finished` is the CLIENT SF-receive, whose
    legality REQUIRES `ClientEndpoint`; so a legal SERVER receive cannot be at that
    control, and every other `Received` arm leaves the field untouched.  ROLE +
    LEGALITY are load-bearing.  Used at fdac's `deliver_to_server` FIRST half to
    forward `Some? hs_server_finished` unchanged across the receive. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_recv_preserves_server_finished
  (st st':CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_tls_message st.CS.cs_model CL.Received msg /\
        CS.step_tls_message st.CS.cs_model CL.Received msg == Some st'.CS.cs_model)
      (ensures
        st'.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        st.CS.cs_model.CS.model_handshake.CS.hs_server_finished)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    fdac DELIVER-TO-SERVER — THE SECOND CRUX (mirror of `lemma_fdac_deliver_to_client`).

    `deliver_to_server` consumes the in-flight `ToServer` payload (sealed by the
    CLIENT) and steps the SERVER; channel `ToServer -> Quiet`, so BOTH halves of
    fdac are active at `b` (`b.server = s'`, `b.client = a.client` frozen).

    FIRST half (passive): `Some? a.server.hs_server_finished ==> App(rd a.client)`.
    A server RECEIVE never touches `hs_server_finished`
    (`lemma_recv_preserves_server_finished`), so `s'.hs_server_finished ==
    a.server.hs_server_finished`; then `fdac a`'s first half (a is `ToServer`, so
    `~ToClient`) carries `App(rd a.client) = App(rd b.client)` (client frozen).

    SECOND half (the crux): `Some? a.client.hs_client_finished ==> App(rd s')`.
    Case split on the PRE-state server READ epoch `R.Application? (rd a.server)`:
      * APP case: the receive is monotone — `lemma_recv_app_preserves_record_material`
        (needs `~KeyUpdate`, from `lemma_recv_not_key_update`) forwards `App(rd s')`
        unconditionally.
      * ~APP case (RECORD-LEVEL faithful decode): under the antecedent,
        `cf_inflight_finished a` (ToServer, `~App(rd a.server)`, `Some?
        hs_client_finished`) pins `sent` to a Finished.  A Finished is a
        non-cleartext `TlsHandshake`, so the CARRIED clause
        `inflight_snap_handshake_write a` — whose ToServer arm rests on the
        RECORD-LEVEL `Some? record_write.R.key` conjunct of `legal_tls_message`'s
        client-Finished send arm — hands the SNAPSHOT gate `Handshake?(snap_wr p)`.
        `inflight_raw_delta_legal` + `inflight_single_record` make `raw` a single
        `Application_data` record, so the received `msg` is not cleartext
        (`HSP.lemma_hsp_client_recv_not_cleartext`, which is role- and control-free),
        whence the projection yields `received_single_protected_message_decode
        a.server msg raw`.  From that decode `lemma_protected_decode_read_key_present`
        gives `Some? (rd a.server).key`, and
        `RKE.lemma_connection_consistent_read_key_present_not_initial` gives
        `~Initial(rd a.server)`; with the ~App case that is `Handshake?(rd a.server)`
        — the RECORD-level read gate.  Both gate halves in hand,
        `hs_channel_seal_ok a`'s ToServer arm fires the bridge and `cs_hs_seq_ok a`
        (now ~terminal-free) supplies the cross-endpoint seq alignment; the
        peer-decode lemma pins `msg == sent = Finished`, and
        `lemma_recv_finished_installs_app_read` (role-free) lands `App(rd s')`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_fdac_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        SY.tls_step_deliver_to_server a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.finished_delivered_appread_coupling b)
  = SY.lemma_deliver_to_server_shape a b;
    assert (ASP.finished_delivered_appread_coupling a);
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns ASP.finished_delivered_appread_coupling b
    with _pf.
    (
      let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
      assert (a.channel == MP.ToServer p);
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent
            { CL.message_direction = CL.Received; CL.message_value = msg } in
         SMCan.canonical_wire_step a.server s' conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns ASP.finished_delivered_appread_coupling b
      with _pd.
      (
        let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        assert (CS.step_tls_message a.server.CS.cs_model CL.Received msg == Some s'.CS.cs_model);
        // FIRST half (passive): a server RECEIVE preserves `hs_server_finished`.
        assert (a.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert (CS.legal_tls_message a.server.CS.cs_model CL.Received msg);
        lemma_recv_preserves_server_finished a.server s' msg;
        // SECOND half (crux).
        introduce
          Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_client_finished
          ==> R.Application? (ASP.rd s').R.epoch
        with _hcf.
        (
          if R.Application? (ASP.rd a.server).R.epoch then
          (
            // APP case: monotone forward, unconditional.
            ASP.lemma_recv_not_key_update s' msg;
            ASP.lemma_recv_app_preserves_record_material a.server s' msg
          )
          else
          (
            // ~APP case: RECORD-LEVEL faithful decode.
            assert (M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent));
            assert (~(CS.network_message_is_cleartext CL.Sent sent));
            assert (ASP.inflight_snap_handshake_write a);
            assert (R.Handshake? (ASP.snap_wr p).R.epoch);
            // `raw` is a single Application_data record (send-side, non-cleartext).
            assert (ASP.inflight_raw_delta_legal a /\ ASP.inflight_single_record a);
            assert (CS.network_message_raw_delta_legal snap
                      ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw);
            assert (CS.raw_records_exactly raw T.Application_data 1);
            HSP.lemma_rre_nonempty raw;
            CSL.lemma_raw_records_exactly_one_parse_record raw T.Application_data;
            W.lemma_parse_record_implies_parse_record_wire raw;
            // received `msg` is not cleartext (role- and control-free helper).
            assert (CS.network_message_raw_delta_legal a.server.CS.cs_model
                      ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw);
            HSP.lemma_hsp_client_recv_not_cleartext a.server msg s'.CS.cs_model raw;
            assert (CS.network_message_is_cleartext CL.Received msg == false);
            // projection (~cleartext branch) -> the decode.
            assert (SMCan.received_single_protected_message_decode a.server.CS.cs_model msg raw);
            // RECORD-level read gate: decode -> key present -> ~Initial -> (with ~App) Handshake.
            lemma_protected_decode_read_key_present a.server.CS.cs_model msg raw;
            RKE.lemma_connection_consistent_read_key_present_not_initial a.server;
            assert (R.Handshake? (ASP.rd a.server).R.epoch);
            // Fire the bridge (hs_channel_seal_ok a) and the seq alignment (cs_hs_seq_ok a).
            assert (ASP.inflight_bridge_ready snap a.server.CS.cs_model sent raw);
            assert (HSP.snap_hs_wseq p == HSP.hs_rseq a.server);
            assert (snap.CS.model_record.CS.record_write.R.seq ==
                    a.server.CS.cs_model.CS.model_record.CS.record_read.R.seq);
            // FAITHFUL DECODE: msg == sent = Finished.
            CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
              snap a.server.CS.cs_model sent raw;
            ASP.lemma_decode_functional a.server.CS.cs_model msg sent raw;
            assert (msg == sent);
            // Finished receive installs App read epoch (role-free; ControlFailed blocks).
            lemma_recv_finished_installs_app_read a.server.CS.cs_model s'.CS.cs_model msg
          )
        )
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Application WRITE epoch FORWARD across a LOCAL step (empty byte-delta).

    The ONLY record-write-mutating local arm is a handshake-write key install,
    LEGAL only at `HsServerHelloReceived` (client) / `HsServerHelloSent` (server)
    (`traffic_install_allowed_at_stage[_for_role]`, StateMachine.fst:1160), which
    resets `record_write` to the Handshake epoch.  But the ORD marker shapes
    (`client_finished_marker_shape` conjunct (A) / `server_flight_marker_shape`),
    established from `connection_state_consistent` via RTC closure, pin
    `record_write.epoch =!= Application` at EXACTLY those handshaking stages.  So
    under the `App`-write hypothesis the acting endpoint is NOT at the de-install
    stage; every other local arm (app-data deliver, fail — StateMachine.fst:303 —
    and the client app-write install, a NO-OP on record_write) leaves the write
    epoch untouched, and an empty-delta network step leaves `model_record` fixed.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 3 --ifuel 8 --z3rlimit 120 --split_queries always"
let lemma_client_local_preserves_app_write
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty /\
        R.Application? (ASP.wr st).R.epoch)
      (ensures R.Application? (ASP.wr st').R.epoch)
  = ORD.lemma_consistent_client_finished_marker_shape st;
    match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM.  Empty byte delta ==> TAIL step (head refuted); a tail step
         restores/raises the read slot, freezes the write slot, and writes only the
         `hb_*` buffers. *)
      lemma_protected_head_impossible_empty st.CS.cs_model step
#pop-options

#push-options "--fuel 3 --ifuel 8 --z3rlimit 120 --split_queries always"
let lemma_server_local_preserves_app_write
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty /\
        R.Application? (ASP.wr st).R.epoch)
      (ensures R.Application? (ASP.wr st').R.epoch)
  = ORD.lemma_consistent_server_flight_marker_shape st;
    match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM, STRUCTURALLY VACUOUS.  `CS.legal_protected_handshake_step` pins
         `model_config.config_role == CS.ClientEndpoint` as its FIRST conjunct, so a
         SERVER can never take a protected-handshake step. *)
      ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    REACHABILITY MARKER: a consistent SERVER is NEVER at
    `ControlHandshaking HsClientFinishedReceived`.

    Rationale: NO `step_model` arm PRODUCES that control (the server receives the
    client Finished at `HsServerFinishedSent` and advances ATOMICALLY to
    `ControlApplicationData`, StateMachine.fst:774; the only mention of
    `HsClientFinishedReceived` is as the *pre*-control of `LocalVerifyClientFinished`
    (:561) and of the server app-READ install (:1182), neither of which is ever
    entered).  So the control is unreachable, and the exclusion is inductive: no
    transition lands there, and the initial control is `ControlNew`.  This lets the
    awc SERVER-local family conclude the server never FRESHLY reaches
    `ControlApplicationData` via a local step (the sole CAD-producing local arm,
    `LocalVerifyClientFinished`, is gated on this unreachable control).
    ───────────────────────────────────────────────────────────────────────── **)

let server_not_cfr_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
    m.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedReceived

#push-options "--fuel 2 --ifuel 5 --z3rlimit 100 --split_queries always"
let lemma_step_server_not_cfr_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        server_not_cfr_shape m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures server_not_cfr_shape m')
  = ()
#pop-options

let lemma_delta_server_not_cfr_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires
        server_not_cfr_shape st0.CS.cs_model /\
        SMR.connection_state_single_step st0 st1)
      (ensures server_not_cfr_shape st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_server_not_cfr_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_server_not_cfr (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures server_not_cfr_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = server_not_cfr_shape st.CS.cs_model in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ SMR.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _.
        lemma_delta_server_not_cfr_shape x y in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(** ─────────────────────────────────────────────────────────────────────────
    CAD-BACKWARD across a LOCAL step: the acting endpoint does not FRESHLY reach
    `ControlApplicationData` via a local step.  The ONLY local arm producing CAD
    is `LocalVerifyClientFinished` (StateMachine.fst:561), gated `ServerEndpoint`
    at `HsClientFinishedReceived`; for the client it is role-excluded, for the
    server it is excluded by the `server_not_cfr` marker.  Every other CAD is
    already-CAD (`LocalDeliverApplicationData`).  So `CAD st' ==> CAD st`.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_client_local_cad_backward
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty)
      (ensures
        CS.ControlApplicationData? st'.CS.cs_model.CS.model_control ==>
        CS.ControlApplicationData? st.CS.cs_model.CS.model_control)
  = match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM.  Empty byte delta ==> TAIL step (head refuted); a tail step
         restores/raises the read slot, freezes the write slot, and writes only the
         `hb_*` buffers. *)
      lemma_protected_head_impossible_empty st.CS.cs_model step
#pop-options

#push-options "--fuel 3 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_server_local_cad_backward
  (st st':CS.connection_state) (ce:CS.conn_event)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event st.CS.cs_model ce /\
        CS.step_model st.CS.cs_model ce == Some st'.CS.cs_model /\
        CS.event_raw_delta_legal st.CS.cs_model ce B.empty B.empty)
      (ensures
        CS.ControlApplicationData? st'.CS.cs_model.CS.model_control ==>
        CS.ControlApplicationData? st.CS.cs_model.CS.model_control)
  = lemma_consistent_server_not_cfr st;
    match ce with
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated
        st.CS.cs_model dm st'.CS.cs_model
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM, STRUCTURALLY VACUOUS.  `CS.legal_protected_handshake_step` pins
         `model_config.config_role == CS.ClientEndpoint` as its FIRST conjunct, so a
         SERVER can never take a protected-handshake step. *)
      ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    FOUR PURE `step_tls_message` FACTS behind the UNGATED conjunct 1 of
    `appdata_write_coupling`.  All four are statements about the SPEC'S OWN
    DISPATCH — no reachability, no invariant, no role — so each is a bare `()`
    over the arm enumeration.  This is the "get the fact from the step" law: the
    conjunct's establishment reads the transition, not the state. **)

(** (i) A SEND never un-installs the application WRITE epoch.  The only `Sent` arms
    that touch `record_write.epoch` are the two installers (the client Finished-send
    at StateMachine.fst:809 and the KeyUpdate-send), both of which SET it to
    `Application`; every other arm advances only the sequence number. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_send_preserves_app_write
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent sent == Some m' /\
        R.Application? m.CS.model_record.CS.record_write.R.epoch)
      (ensures R.Application? m'.CS.model_record.CS.record_write.R.epoch)
  = ()
#pop-options

(** (ii) CAD-BACKWARD ACROSS A SEND.  The unique `Sent` arm ENTERING
    `ControlApplicationData` is the client Finished-send (StateMachine.fst:809), whose
    pre-control is `HsServerFinishedVerified`.  So a send lands at CAD only from CAD
    itself or from HSFV — and HSFV is excluded at a consistent SERVER by
    `SNCFR.lemma_consistent_server_not_shsfv`, which is how the server_send family
    uses this. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_send_cad_backward
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent sent == Some m' /\
        CS.ControlApplicationData? m'.CS.model_control)
      (ensures
        CS.ControlApplicationData? m.CS.model_control \/
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = ()
#pop-options

(** (iii) THE TWO `Sent, Finished` ARMS.  Exactly two exist: StateMachine.fst:676
    (at `HsServerEncryptedFlightSent`, landing at the SERVER-only stage
    `HsServerFinishedSent`) and :809 (at `HsServerFinishedVerified`, landing at
    `ControlApplicationData`).  Consumer: the `deliver_to_server` crux, where
    `SY.client_stage_ok` (`| _ -> False` on server-only stages) kills the first
    disjunct and pins the CLIENT'S CONTROL at CAD. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_sent_finished_post_control
  (m m':CS.connection_model) (fin:GFin.finished)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent (M.TlsHandshake (M.Finished fin)) == Some m')
      (ensures
        m'.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
        m'.CS.model_control == CS.ControlApplicationData)
  = ()
#pop-options

(** (iv) A RECEIVE THAT ENTERS CAD CARRIES A FINISHED.  `StateMachine.fst:774` (the
    server's atomic client-Finished receive) is the unique `Received` arm producing
    `ControlApplicationData` from a different control.  Consumer: the
    `deliver_to_server` crux, to learn BOTH the in-flight message (a `Finished`) and
    the PRE-control (`HsServerFinishedSent`) from the STEP rather than from any
    carried message-identity clause.  The pre-control half is what licenses
    `CSL.lemma_handshaking_nonfinal_read_not_application` and hence the
    `~Application? (rd a.server)` side condition of the faithful-decode block. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_recv_entering_cad_is_finished
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Received msg == Some m' /\
        CS.ControlApplicationData? m'.CS.model_control)
      (ensures
        CS.ControlApplicationData? m.CS.model_control \/
        (m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
         M.TlsHandshake? msg /\ M.Finished? (M.TlsHandshake?._0 msg)))
  = ()
#pop-options

(** (v) A PROTECTED NON-HANDSHAKE SEND COMES FROM THE SETTLED REGION.  Once
    cleartext (`ClientHello`/`ServerHello`/CCS) and `TlsKeyUpdate` are excluded, the
    only remaining non-handshake sendable messages are `TlsApplicationData` (Sent arm
    live only at `ControlApplicationData`, StateMachine.fst:841) and
    `TlsAlert Close_notify` (Sent arm live only at `ControlApplicationData`, :929 —
    the `ControlClosing` arm is `Sent -> None` and, since the direction-explicit
    catch-all fix, every other `Sent` alert is `None`).  So such a send LANDS in
    `{CAD, Closing, Closed}`, from which
    `lemma_connection_appdata_keys_installed_for_role` /
    `lemma_connection_closing_closed_record_epochs_installed` give the RECORD-level
    `Application` write epoch. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_sent_nonhandshake_post_control
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent sent == Some m' /\
        ~(M.TlsHandshake? sent) /\ ~(M.TlsKeyUpdate? sent) /\
        CS.network_message_is_cleartext CL.Sent sent == false)
      (ensures
        CS.ControlApplicationData? m'.CS.model_control \/
        CS.ControlClosing? m'.CS.model_control \/
        CS.ControlClosed? m'.CS.model_control)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    awc CONJUNCT 2 FROM THE INVARIANT ALONE (no carried clause).

    At a `Quiet` channel with the CLIENT at `ControlApplicationData` and the server
    NOT `ControlFailed`, the server's application WRITE record epoch (RECORD level,
    not slot level) is installed.  Route — entirely from machinery that already
    existed:
      * `CSL.lemma_connection_appdata_keys_installed_for_role ClientEndpoint` turns
        the client's control into `SY.client_ready` (the `client_e2e` conjunct of
        `tls_system_inv` supplies the driver half);
      * `SY.client_clean` (a conjunct of `tls_system_inv`) + `Quiet` then gives
        `SY.server_post_cf` — the server has already stepped on the client's
        Finished;
      * per surviving server control: `ControlApplicationData` →
        appdata-keys + `lemma_connection_application_ready_record_epochs_installed`;
        `ControlClosing`/`ControlClosed` →
        `lemma_connection_closing_closed_record_epochs_installed`;
        `HsClientFinishedReceived`/`Verified` → these two controls are
        CANONICALLY UNREACHABLE (no arm of the state machine ever produces them —
        the server's client-Finished receive and `LocalVerifyClientFinished` both
        jump straight to `ControlApplicationData`), excluded by
        `SNCFR.lemma_consistent_not_cfr` / `lemma_consistent_not_cfv`.  That is a
        CONTROL-reachability fact, not a key-material one.
    `ControlFailed` is excluded by the conjunct's own gate (see the
    `appdata_write_coupling` doc comment in ASP for why it is TRUE but
    UNDERIVABLE there). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_awc_conjunct2_from_inv (s:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv s /\ MP.Quiet? s.channel /\
        CS.ControlApplicationData? (SY.ctrl s.client) /\
        ~(CS.ControlFailed? (SY.ctrl s.server)))
      (ensures R.Application? (ASP.wr s.server).R.epoch)
  = CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint s.client;
    (* Since the merge, `client_driver_application_ready` carries
       `CS.protected_handshake_buffer_empty`; supply it as a reachability fact. *)
    ADBE.lemma_connection_appdata_protected_handshake_buffer_empty s.client;
    assert (SY.client_ready s);
    assert (SY.server_post_cf s);
    SNCFR.lemma_consistent_not_cfr s.server;
    SNCFR.lemma_consistent_not_cfv s.server;
    match SY.ctrl s.server with
    | CS.ControlApplicationData ->
        CSL.lemma_connection_appdata_keys_installed_for_role CS.ServerEndpoint s.server;
        CSL.lemma_connection_application_ready_record_epochs_installed CS.ServerEndpoint s.server
    | CS.ControlClosing ->
        CSL.lemma_connection_closing_closed_record_epochs_installed CS.ServerEndpoint s.server
    | CS.ControlClosed ->
        CSL.lemma_connection_closing_closed_record_epochs_installed CS.ServerEndpoint s.server
    | _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    awc LOCAL families.  Channel stays `Quiet`.  For a client local (server
    frozen): conjunct 1 `CAD(server) ==> App(wr client)` — the antecedent is frozen
    (server), `awc a` gives `App(wr a.client)`, forwarded by the write-monotone
    `lemma_client_local_preserves_app_write`; conjunct 2 `CAD(client) ==> App(wr
    server)` — `lemma_client_local_cad_backward` pushes `CAD(c')` back to
    `CAD(a.client)`, and `awc a` gives `App(wr a.server)` (= frozen `wr b.server`).
    Server local is the mirror (write-forward on conjunct 2, marker-backed
    CAD-backward on conjunct 1). **)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_awc_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b)
      (ensures ASP.appdata_write_coupling b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns ASP.appdata_write_coupling b
    with _pf.
    (
      ASP.lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      returns ASP.appdata_write_coupling b
      with _pe.
      (
        introduce
          CS.ControlApplicationData? (SY.ctrl b.server)
          ==> R.Application? (ASP.wr b.client).R.epoch
        with _. lemma_client_local_preserves_app_write a.client c' ce;
        lemma_client_local_cad_backward a.client c' ce
      )
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_awc_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b)
      (ensures ASP.appdata_write_coupling b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns ASP.appdata_write_coupling b
    with _pf.
    (
      ASP.lemma_server_local_extract a.server s' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      returns ASP.appdata_write_coupling b
      with _pe.
      (
        introduce
          CS.ControlApplicationData? (SY.ctrl b.client) /\
          ~(CS.ControlFailed? (SY.ctrl b.server))
          ==> R.Application? (ASP.wr b.server).R.epoch
        with _.
        (
          // Gate transfer: `ControlFailed` alone is absorbing, so `~Failed(b.server)`
          // pushes back to `~Failed(a.server)`, re-enabling `awc a`'s conjunct 2.
          // DO NOT DELETE AS DEAD WEIGHT.  A two-run shows Z3 currently re-derives
          // this transfer inline (the call is not needed as a proof HINT), but the
          // call is the MACHINE-CHECKED DISCHARGE of the gate-monotonicity
          // obligation that makes the `~ControlFailed?` gate on `appdata_write_
          // coupling`'s conjunct 2 LEGAL AT ALL.  Without it the gate rests on an
          // unproven absorbing claim, and a future fuel/ifuel change could turn the
          // inline derivation into a failure with no record of why it was sound.
          HSP.lemma_step_control_failed_absorbing a.server.CS.cs_model s'.CS.cs_model ce;
          lemma_server_local_preserves_app_write a.server s' ce
        );
        lemma_server_local_cad_backward a.server s' ce
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    awc SEND families.  A send exits `Quiet` to `ToServer` (client) / `ToClient`
    (server), so conjunct 2 — which KEEPS its `MP.Quiet?` gate — is vacuous at `b`
    and only the post-channel head has to be pinned.  Conjunct 1 is UNGATED, so it
    is REAL here, and each direction forwards it with one pure step fact:
      * client_send: the server is frozen, so the antecedent `CAD(b.server)` is the
        antecedent at `a`; `awc a` gives `App(wr a.client)` and
        `lemma_send_preserves_app_write` carries it across the client's own send.
      * server_send: the client is frozen, so the consequent is the consequent at
        `a`; `lemma_send_cad_backward` pushes `CAD(s')` back to `CAD(a.server)` —
        its second disjunct `HsServerFinishedVerified` is excluded at a consistent
        server by `SNCFR.lemma_consistent_server_not_shsfv` — and `awc a` closes. **)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_awc_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.appdata_write_coupling b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns ASP.appdata_write_coupling b
    with _pf.
    (
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      assert (MP.ToServer? b.channel);
      introduce
        CS.ControlApplicationData? (SY.ctrl b.server)
        ==> R.Application? (ASP.wr b.client).R.epoch
      with _.
        lemma_send_preserves_app_write a.client.CS.cs_model c'.CS.cs_model sent
    )
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_awc_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.appdata_write_coupling b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns ASP.appdata_write_coupling b
    with _pf.
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      assert (MP.ToClient? b.channel);
      // Kept though decorative by two-run (Z3 re-derives it inline): it is the
      // machine-checked exclusion of the canonically-unreachable
      // `HsServerFinishedVerified` server stage, which is what makes
      // `lemma_send_cad_backward`'s two-case conclusion collapse to the CAD case.
      SNCFR.lemma_consistent_server_not_shsfv a.server;
      introduce
        CS.ControlApplicationData? (SY.ctrl b.server)
        ==> R.Application? (ASP.wr b.client).R.epoch
      with _.
        lemma_send_cad_backward a.server.CS.cs_model s'.CS.cs_model sent
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    awc DELIVER-TO-CLIENT.  Both conjuncts are easy in this direction:
      * conjunct 1 (UNGATED, which is exactly why the `Quiet` gate had to go): the
        SERVER is frozen, so the antecedent is unchanged, and `awc a` — which now
        SPEAKS at the `ToClient` pre-state — hands over `App(wr a.client)`;
        `AMF.lemma_recv_preserves_write_epoch` carries it across the client's
        receive (a receive never touches the write epoch).
      * conjunct 2: `b` is `Quiet`, so `lemma_awc_conjunct2_from_inv b` applies
        directly off `tls_system_inv b` — no carried clause. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_awc_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.appdata_write_coupling a /\
        SY.tls_step_deliver_to_client a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.appdata_write_coupling b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns ASP.appdata_write_coupling b
    with _pf.
    (
      EC.lemma_client_wire_step_inversion #CTy.client_local_event a.client c' wire out;
      eliminate exists (conn_ev0:CS.conn_event).
        (EC.client_wire_received_event a.client wire conn_ev0 /\
         SMCan.canonical_wire_step a.client c' conn_ev0
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev0 out.SM.so_local_outputs)
      returns ASP.appdata_write_coupling b
      with _inv.
      (
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        (* CONJUNCT 1 is a WRITE-EPOCH forward, and BOTH client wire arms freeze the
           client's write slot: a `CL.Received` network step
           (`AMF.lemma_recv_preserves_write_epoch`) and, since the merge, a HEAD
           `CS.ConnProtectedHandshake` step, which routes through
           `CS.step_handshake_message _ CL.Received _` and therefore never touches
           `record_write` (`HSP.lemma_protected_preserves_wr_full`).
           CONJUNCT 2 is channel-shape-only and reads `tls_system_inv b` directly, so
           it is arm-independent. *)
        introduce
          CS.ControlApplicationData? (SY.ctrl b.server)
          ==> R.Application? (ASP.wr b.client).R.epoch
        with _.
        (
          match conn_ev0 with
          | CS.ConnLocalEvent _ -> ()
          | CS.ConnProtectedHandshake step ->
            HSP.lemma_protected_preserves_wr_full
              a.client.CS.cs_model c'.CS.cs_model step
          | CS.ConnNetworkEvent tm ->
            AMF.lemma_recv_preserves_write_epoch
              a.client.CS.cs_model tm.CL.message_value c'.CS.cs_model
        );
        introduce
          ( MP.Quiet? b.channel /\
            CS.ControlApplicationData? (SY.ctrl b.client) /\
            ~(CS.ControlFailed? (SY.ctrl b.server)) )
          ==> R.Application? (ASP.wr b.server).R.epoch
        with _. lemma_awc_conjunct2_from_inv b
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    awc DELIVER-TO-SERVER — THE ONE NON-FORWARDING FAMILY, and the reason conjunct 1
    had to be ungated.  The client is frozen, so conjunct 1's CONSEQUENT is fixed;
    what moves is its ANTECEDENT, because this is the step that can put the server
    at `ControlApplicationData` for the first time.  Two cases:

      * `CAD(a.server)` already: the antecedent held at `a`, and `awc a` — speaking
        at the `ToServer` pre-state, which the `Quiet` gate used to forbid — hands
        over `App(wr a.client)`, and `b.client == a.client`.

      * the delivery ENTERS CAD: `lemma_recv_entering_cad_is_finished` reads off the
        step that the received `msg` is a `Finished` and that the server sat at
        `HsServerFinishedSent` (StateMachine.fst:774 is the unique arm).  That
        pre-control gives `~Application? (rd a.server)` via
        `CSL.lemma_handshaking_nonfinal_read_not_application`, which is the side
        condition of the RECORD-level faithful-decode block (the same block
        `lemma_fdac_deliver_to_server` runs, and it needs the same clause set:
        `inflight_snap_handshake_write`, `inflight_raw_delta_legal`,
        `inflight_single_record`, `hs_channel_seal_ok`, `cs_hs_seq_ok`).  Decode
        gives `msg == sent`, so the SEALED message was a `Finished`.  Now
        `inflight_sender_stepped a` carries
        `step_tls_message pl_snap CL.Sent pl_sent == Some a.client.cs_model`, and
        `lemma_sent_finished_post_control` leaves exactly two possible client
        controls: `HsServerFinishedSent` (SERVER-only, killed by
        `SY.client_stage_ok`'s `| _ -> False`) and `ControlApplicationData`.  So the
        CLIENT'S CONTROL is CAD — a control fact taken from the STEP — and the two
        consistency lemmas lift it to the RECORD-level `Application` write epoch.

    LEVEL NOTE: the conclusion is RECORD level (`model_record.record_write.epoch`),
    reached from a CONTROL fact via `lemma_connection_appdata_keys_installed_for_role`
    (which is itself reachability-only) and
    `lemma_connection_application_ready_record_epochs_installed`.  Nothing here
    infers record-level material from slot-level presence. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_awc_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        SY.tls_step_deliver_to_server a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.appdata_write_coupling b)
  = SY.lemma_deliver_to_server_shape a b;
    assert (ASP.appdata_write_coupling a);
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns ASP.appdata_write_coupling b
    with _pf.
    (
      let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
      assert (a.channel == MP.ToServer p);
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent
            { CL.message_direction = CL.Received; CL.message_value = msg } in
         SMCan.canonical_wire_step a.server s' conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns ASP.appdata_write_coupling b
      with _pd.
      (
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        assert (CS.step_tls_message a.server.CS.cs_model CL.Received msg == Some s'.CS.cs_model);
        assert (a.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert (CS.legal_tls_message a.server.CS.cs_model CL.Received msg);
        // CONJUNCT 2: `b` is Quiet, straight from `tls_system_inv b`.
        introduce
          ( MP.Quiet? b.channel /\
            CS.ControlApplicationData? (SY.ctrl b.client) /\
            ~(CS.ControlFailed? (SY.ctrl b.server)) )
          ==> R.Application? (ASP.wr b.server).R.epoch
        with _. lemma_awc_conjunct2_from_inv b;
        // CONJUNCT 1 (the crux).
        introduce
          CS.ControlApplicationData? (SY.ctrl b.server)
          ==> R.Application? (ASP.wr b.client).R.epoch
        with _.
        (
          if CS.ControlApplicationData? (SY.ctrl a.server) then ()
          else
          (
            lemma_recv_entering_cad_is_finished
              a.server.CS.cs_model s'.CS.cs_model msg;
            assert (a.server.CS.cs_model.CS.model_control ==
                      CS.ControlHandshaking CS.HsServerFinishedSent);
            CSL.lemma_handshaking_nonfinal_read_not_application a.server;
            assert (~(R.Application? (ASP.rd a.server).R.epoch));
            // ── STEP 1: the RECEIVED message is a Finished, hence NOT cleartext by
            //    computation, so the receive-side raw-delta takes its PROTECTED
            //    branch and `raw` is a single `Application_data` record.
            assert (CS.network_message_is_cleartext CL.Received msg == false);
            assert (CS.network_message_raw_delta_legal a.server.CS.cs_model
                      ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw);
            assert (CS.raw_records_exactly raw T.Application_data 1);
            HSP.lemma_rre_nonempty raw;
            CSL.lemma_raw_records_exactly_one_parse_record raw T.Application_data;
            W.lemma_parse_record_implies_parse_record_wire raw;
            // ── STEP 2: therefore the SENT message is not cleartext either — a
            //    cleartext send pins `raw` to a non-`Application_data` record.
            assert (ASP.inflight_raw_delta_legal a /\ ASP.inflight_single_record a);
            assert (CS.network_message_raw_delta_legal snap
                      ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw);
            (if CS.network_message_is_cleartext CL.Sent sent
             then HSP.lemma_cleartext_sent_raw_not_appdata sent raw
             else ());
            assert (CS.network_message_is_cleartext CL.Sent sent == false);
            assert (ASP.inflight_sender_stepped a);
            assert (CS.step_tls_message snap CL.Sent sent == Some a.client.CS.cs_model);
            // ── STEP 3: split on the SEALED message's class.
            if M.TlsHandshake? sent then
            (
              // RECORD-LEVEL FAITHFUL DECODE (the same block as fdac's ~APP case).
              assert (ASP.inflight_snap_handshake_write a);
              assert (R.Handshake? (ASP.snap_wr p).R.epoch);
              lemma_protected_decode_read_key_present a.server.CS.cs_model msg raw;
              RKE.lemma_connection_consistent_read_key_present_not_initial a.server;
              assert (R.Handshake? (ASP.rd a.server).R.epoch);
              assert (ASP.inflight_bridge_ready snap a.server.CS.cs_model sent raw);
              assert (HSP.snap_hs_wseq p == HSP.hs_rseq a.server);
              assert (snap.CS.model_record.CS.record_write.R.seq ==
                      a.server.CS.cs_model.CS.model_record.CS.record_read.R.seq);
              CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
                snap a.server.CS.cs_model sent raw;
              ASP.lemma_decode_functional a.server.CS.cs_model msg sent raw;
              assert (msg == sent);
              // Kept deliberately though a two-run shows Z3 re-derives it inline:
              // this call is the machine-checked record that a `Sent Finished`
              // lands only at `HsServerFinishedSent` or `ControlApplicationData`,
              // which (with `client_stage_ok` killing the server-only stage) is
              // what pins the client at CAD below.  Not a hint — do not delete.
              lemma_sent_finished_post_control
                snap a.client.CS.cs_model (M.Finished?._0 (M.TlsHandshake?._0 sent));
              assert (SY.client_stage_ok a.client);
              assert (CS.ControlApplicationData? (SY.ctrl a.client));
              CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint a.client;
              CSL.lemma_connection_application_ready_record_epochs_installed
                CS.ClientEndpoint a.client
            )
            else
            (
              // A protected NON-handshake send: app data or `Close_notify`, both of
              // which are live only from `ControlApplicationData`, so the client is
              // in the settled region and its app WRITE epoch is installed.
              // As above: a two-run shows Z3 re-derives this inline, but the call is
              // the machine-checked discharge of the message-class case split
              // (protected non-handshake ==> post-control in {CAD,Closing,Closed}),
              // which is what justifies the two-way branch below.  Do not delete.
              lemma_sent_nonhandshake_post_control snap a.client.CS.cs_model sent;
              if CS.ControlApplicationData? (SY.ctrl a.client) then
              (
                CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint a.client;
                CSL.lemma_connection_application_ready_record_epochs_installed
                  CS.ClientEndpoint a.client
              )
              else
                CSL.lemma_connection_closing_closed_record_epochs_installed
                  CS.ClientEndpoint a.client
            )
          )
        )
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    COMPANION `sf_inflight_finished` step families.  FIVE are VACUOUS (the
    post-state channel is `Quiet` or `ToServer`, so the `MP.ToClient` match arm
    does not fire): client_send (→ToServer), deliver_to_client/deliver_to_server
    (→Quiet), client_local/server_local (→Quiet).  Only `server_send` (→ToClient)
    is real.  For the vacuous ones we still establish the post-channel head via the
    shape lemma / destructuring so the match reduces to `True`. **)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_sfif_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures sf_inflight_finished b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns sf_inflight_finished b
    with _pf. (assert (MP.ToServer? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_sfif_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        SY.tls_step_deliver_to_client a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures sf_inflight_finished b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns sf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_sfif_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        SY.tls_step_deliver_to_server a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures sf_inflight_finished b)
  = SY.lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns sf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_sfif_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures sf_inflight_finished b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns sf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_sfif_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures sf_inflight_finished b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns sf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

(** COMPANION `sf_inflight_finished` — the ONLY real family: `server_send`
    (→ToClient).  b.channel = `ToClient p` with `p.pl_sent == sent`; b.client is
    frozen, b.server = s'.  The match reduces to
    `(~App(rd a.client) /\ Some? hs_server_finished s') ==> Finished sent`.
    Case on the PRE-state `hs_server_finished a.server`:
      * None (pre): the send takes the field None→Some, so by
        `lemma_send_none_to_some_server_finished` `sent` is a Finished — discriminator.
      * Some (pre): fdac's FIRST half at the Quiet pre-state (`~ToClient` holds)
        gives `App(rd a.client)` = `App(rd b.client)`, contradicting `~App(rd b.client)`
        — antecedent false, vacuous. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_sfif_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ sf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures sf_inflight_finished b)
  = SY.lemma_server_send_shape a b;
    assert (ASP.finished_delivered_appread_coupling a);
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns sf_inflight_finished b
    with _pf.
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      assert (MP.ToClient? b.channel);
      introduce
        ( ~ (R.Application? (ASP.rd b.client).R.epoch)
          /\ Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished )
        ==> ( M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent) )
      with _ante.
      (
        if None? a.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished
        then lemma_send_none_to_some_server_finished a.server.CS.cs_model s'.CS.cs_model sent
        else ()   // fdac first half ⟹ App(rd a.client) = App(rd b.client), contradiction
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    COMPANION `cf_inflight_finished` step families — the MIRROR of the `sf`
    families.  FIVE are VACUOUS (post-channel is `Quiet` or `ToClient`, so the
    `MP.ToServer` match arm does not fire): server_send (→ToClient),
    deliver_to_client/deliver_to_server (→Quiet), client_local/server_local
    (→Quiet).  Only `client_send` (→ToServer) is real, and it uses fdac's SECOND
    half at the Quiet pre-state to exclude the "CF already sent" case. **)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_cfif_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures cf_inflight_finished b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns cf_inflight_finished b
    with _pf. (assert (MP.ToClient? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_cfif_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        SY.tls_step_deliver_to_client a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures cf_inflight_finished b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns cf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_cfif_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        SY.tls_step_deliver_to_server a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures cf_inflight_finished b)
  = SY.lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns cf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_cfif_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures cf_inflight_finished b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns cf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_cfif_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures cf_inflight_finished b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns cf_inflight_finished b
    with _pf. (assert (MP.Quiet? b.channel))
#pop-options

(** COMPANION `cf_inflight_finished` — the ONLY real family: `client_send`
    (→ToServer).  Mirror of `lemma_sfif_server_send`, using fdac's SECOND half. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_cfif_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ cf_inflight_finished a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures cf_inflight_finished b)
  = SY.lemma_client_send_shape a b;
    assert (ASP.finished_delivered_appread_coupling a);
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns cf_inflight_finished b
    with _pf.
    (
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      assert (MP.ToServer? b.channel);
      introduce
        ( ~ (R.Application? (ASP.rd b.server).R.epoch)
          /\ Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_client_finished )
        ==> ( M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent) )
      with _ante.
      (
        if None? a.client.CS.cs_model.CS.model_handshake.CS.hs_client_finished
        then lemma_send_none_to_some_client_finished a.client.CS.cs_model c'.CS.cs_model sent
        else ()   // fdac second half ⟹ App(rd a.server) = App(rd b.server), contradiction
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    ESTABLISHMENT + PRESERVATION of `ASP.channel_seal_ok` — the six step families.

    `channel_seal_ok` is a property of the IN-FLIGHT payload, so it is VACUOUS at
    every `Quiet` post-state: the two locals keep the channel `Quiet` and the two
    deliveries exit to `Quiet`.  Only the two SENDS do work, and they must
    ESTABLISH all three components from scratch.  This mirrors the layout of
    `HSP.lemma_hscs_*` for the handshake-epoch sibling `hs_channel_seal_ok`.

    THE THREE COMPONENTS AT A SEND (stated for the client send; the server send is
    the mirror).  Write `snap == a.client.cs_model` (the PRE-send snapshot) and let
    the receiver be the frozen `a.server`.

      * FORWARD `App (snap_wr) ==> App (rd receiver)`.  RECORD-LEVEL on both sides.
        Route, and it is a "get the fact from the STEP/consistency, not the
        invariant" route on its first half:
          - `App (wr client)` ==> `Some? hs_client_finished` by
            `ORD.lemma_client_write_app_finished`, i.e. by the CLIENT-side
            write-once marker shape, which is available from
            `connection_state_consistent` alone.  This is exactly the fact that a
            client installs its application WRITE record keys ONLY atomically at
            its Finished send — `install_record_keys` is a NO-OP on
            `(TrafficApplication, TrafficWrite)` (StateMachine.fst:399-400) and
            `install_record_keys_for_role` special-cases app-write for the SERVER
            role only, so the optional `LocalInstallTrafficKeys` local CANNOT move
            the client's app write epoch.
          - `Some? hs_client_finished ==> App (rd server)` is `fdac`'s SECOND half,
            whose gate `~(MP.ToServer? channel)` is discharged by the `Quiet`
            pre-state.
        The server send is the mirror with `ORD.lemma_consistent_server_flight_
        marker_shape` (whose last conjunct is `App (wr server) ==> Some?
        hs_server_finished`) and `fdac`'s FIRST half.

      * CONTROL-GATED BACKWARD `CAD (ctrl receiver) ==> App (snap_wr)`.  This is
        LITERALLY `appdata_write_coupling` at the pre-state:
          - client send: conjunct 1, `CAD (ctrl server) ==> App (wr client)`.  This
            is precisely why conjunct 1 had to be UNGATED — under the old `Quiet?`
            gate it would still fire here (the pre-state IS Quiet), but it could not
            be established at the deliveries, so the clause was not available.
          - server send: conjunct 2, `Quiet /\ CAD (ctrl client) /\ ~Failed (ctrl
            server) ==> App (wr server)`.  All three gate halves are in hand: the
            pre-state is `Quiet`, `CAD (ctrl b.client) == CAD (ctrl a.client)` since
            the client is frozen, and `~ControlFailed (a.server)` comes FROM THE STEP
            via `HSP.lemma_sent_step_not_failed`.

      * BRIDGE under `App (snap_wr)`.  Three sub-facts:
          - key/iv material agreement — RECORD-LEVEL, `peer_record_material_agrees`
            at the application traffic id, taken from `app_material_agreement a`,
            which is gated on `cf_delivered a == App (wr client) /\ App (rd server)`.
            At the CLIENT send both halves are already in hand (the arm gate gives
            the first, FORWARD gives the second).  At the SERVER send neither is,
            so the send's own pre-control is enumerated first
            (`lemma_server_send_app_write_at_cad`) and `awc` conjunct 1 plus
            `CSL.lemma_connection_application_ready_record_epochs_installed` supply
            the two halves.
          - single-record protected seal + serialize/parse roundtrip, from the
            App-epoch analogues of `HSP.lemma_*_send_seal_rt` below.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** VACUITY — every `Quiet` post-state.  Covers all four non-send families. **)
let lemma_cso_quiet (s:SY.tls_system_state)
  : Lemma (requires MP.Quiet? s.channel) (ensures ASP.channel_seal_ok s)
  = ()

(** APP-EPOCH CLEARTEXT EXCLUSION (client).  The App-epoch analogue of
    `HSP.lemma_client_gate_excludes`.  The `Sent` cleartext messages are
    `ClientHello`, `ServerHello` and `ChangeCipherSpec`.  CCS is excluded by
    hypothesis (it comes from the send's message-class lemma); `ServerHello` has no
    `ClientEndpoint`-legal `Sent` arm; and `ClientHello` is `Sent`-legal only at
    `ControlNew`, where the client-side write-once marker shape forces the write
    epoch to be non-`Application`.

    NOTE the asymmetry with the handshake-epoch sibling: that one additionally
    concludes `~(M.TlsKeyUpdate? sent)` (a KeyUpdate send needs app keys, which a
    handshake-epoch sender lacks).  At the APPLICATION epoch a KeyUpdate send is
    perfectly legal, so `~KeyUpdate` is NOT derivable here and is instead taken as
    a hypothesis by the seal lemmas below and discharged at the call site from
    `tls_no_rekeying`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_client_app_gate_excludes (st0:CS.connection_state) (sent:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_tls_message st0.CS.cs_model CL.Sent sent /\
        ~(M.TlsChangeCipherSpec? sent) /\
        R.Application? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures CS.network_message_is_cleartext CL.Sent sent == false)
  = ORD.lemma_consistent_client_finished_marker_shape st0
#pop-options

(** APP-EPOCH CLEARTEXT EXCLUSION (server).  Mirror; `ServerHello` is `Sent`-legal
    only at `HsClientHelloReceived`, which the server-side flight marker shape
    pins to a non-`Application` write epoch, and `ClientHello` has no
    `ServerEndpoint`-legal `Sent` arm. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_server_app_gate_excludes (st0:CS.connection_state) (sent:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_tls_message st0.CS.cs_model CL.Sent sent /\
        ~(M.TlsChangeCipherSpec? sent) /\
        R.Application? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures CS.network_message_is_cleartext CL.Sent sent == false)
  = ORD.lemma_consistent_server_flight_marker_shape st0
#pop-options

(** SEND-TIME SEAL + ROUNDTRIP at the APPLICATION write epoch (client).  Body is
    the App-epoch transcription of `HSP.lemma_client_send_seal_rt`: the emitted
    `out` is a single wire record, so `ASP.lemma_client_send_count` gives
    `protected_record_count Sent sent == 1` (this holds even for a multi-fragment
    `TlsApplicationData` payload — the count is forced to 1 by the single emitted
    record, see `ASP.lemma_send_single_record_count`), the App gate lemma gives
    `~cleartext`, and `HSP.lemma_send_seal`/`HSP.lemma_send_roundtrip` are
    epoch-agnostic. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_client_send_seal_rt_app
  (st0 c':CS.connection_state) (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        EC.client_step st0 (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        c'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
        ~(M.TlsKeyUpdate? sent) /\
        R.Application? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures
        SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
        HSP.roundtrip sent)
  = ASP.lemma_client_send_count st0 c' local out w sent;
    HSP.lemma_client_send_msg_class st0 c' local out w sent;
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      EC.client_representation_matches st0 local conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 c' conn_ev raw_sent B.empty
    returns
      SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
      HSP.roundtrip sent
    with _pf.
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      SY.lemma_serialize_all_single w;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
      assert (CS.legal_tls_message st0.CS.cs_model CL.Sent sent);
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      lemma_client_app_gate_excludes st0 sent;
      assert (CS.raw_records_exactly raw_sent T.Application_data 1);
      HSP.lemma_rre_nonempty raw_sent;
      HSP.lemma_send_seal st0.CS.cs_model sent raw_sent;
      HSP.lemma_send_roundtrip st0.CS.cs_model sent
    )
#pop-options

(** SEND-TIME SEAL + ROUNDTRIP at the APPLICATION write epoch (server).  Mirror. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_server_send_seal_rt_app
  (st0 s':CS.connection_state) (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ES.server_step st0 (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        s'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
        ~(M.TlsKeyUpdate? sent) /\
        R.Application? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures
        SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
        HSP.roundtrip sent)
  = ASP.lemma_server_send_count st0 s' local out w sent;
    HSP.lemma_server_send_msg_class st0 s' local out w sent;
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ES.server_representation_matches local conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty
    returns
      SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
      HSP.roundtrip sent
    with _pf.
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      SY.lemma_serialize_all_single w;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
      assert (CS.legal_tls_message st0.CS.cs_model CL.Sent sent);
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      lemma_server_app_gate_excludes st0 sent;
      assert (CS.raw_records_exactly raw_sent T.Application_data 1);
      HSP.lemma_rre_nonempty raw_sent;
      HSP.lemma_send_seal st0.CS.cs_model sent raw_sent;
      HSP.lemma_send_roundtrip st0.CS.cs_model sent
    )
#pop-options

(** PRE-CONTROL ENUMERATION at a server send with the application WRITE epoch
    installed.  A `Sent` step is possible only from the controls that have a `Sent`
    arm in `step_tls_message`; the server flight marker shape kills every early
    server control (`ControlNew` .. `HsServerEncryptedFlightSent` all force a
    non-`Application` write epoch), `HsServerFinishedVerified` is a CLIENT stage
    that a consistent server never occupies (`lemma_consistent_server_not_shsfv`),
    `HsClientFinishedReceived`/`Verified` are canonically unreachable
    (`lemma_consistent_not_cfr` / `lemma_consistent_not_cfv`), and the closure
    controls have no `Sent` arm at all.  What is left is
    `ControlApplicationData`.

    TWO HYPOTHESES THAT ARE NOT DECORATIVE, both found by two-run (each one
    removed re-opens a control):

      * `SY.server_stage_ok st` — `connection_state_consistent` alone does NOT
        confine a server to server-side handshake stages, and the CCS arm below
        fires at `ControlHandshaking _` for EVERY stage, so without the stage
        predicate the client-side stages (`HsServerHelloReceived`,
        `HsCertificateReceived`, ...) all survive.  The server flight marker shape
        says nothing about them.

      * `~(M.TlsChangeCipherSpec? msg)` — `M.TlsChangeCipherSpec, ControlHandshaking
        _` (StateMachine.fst, the arm just above the catch-all) is `Some model` in
        BOTH directions and at EVERY handshake stage.  So a server sitting at
        `HsServerFinishedSent` with its application write keys already installed by
        the OPTIONAL role-local (`install_record_keys_for_role`,
        `traffic_install_allowed_at_stage_for_role` allows `(ServerEndpoint,
        TrafficApplication, TrafficWrite)` exactly at that stage — the 0.5-RTT
        window) can take a `Sent` CCS step with an `Application` write epoch.  That
        is a genuine `Some`-arm, not an artefact: the conclusion really is
        `CAD \/ (HsServerFinishedSent /\ CCS)`, and the CCS disjunct is discharged
        at the call site by `HSP.lemma_server_send_msg_class`, which proves the
        driver never emits a CCS record. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_server_send_app_write_at_cad
  (st:CS.connection_state) (m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        SY.server_stage_ok st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(M.TlsChangeCipherSpec? msg) /\
        R.Application? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch /\
        CS.step_tls_message st.CS.cs_model CL.Sent msg == Some m')
      (ensures CS.ControlApplicationData? st.CS.cs_model.CS.model_control)
  = ORD.lemma_consistent_server_flight_marker_shape st;
    SNCFR.lemma_consistent_not_cfr st;
    SNCFR.lemma_consistent_not_cfv st;
    SNCFR.lemma_consistent_server_not_shsfv st
#pop-options

(** SUBSTANTIVE — CLIENT SEND (post channel `MP.ToServer p`, `p.pl_snap ==
    a.client.cs_model`, `b.server == a.server`).  All three components as laid out
    in the section header. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_cso_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b /\ SY.tls_no_rekeying b)
      (ensures ASP.channel_seal_ok b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c';
                    channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns ASP.channel_seal_ok b
    with _pf.
    (
      let p : SY.tls_payload =
        { SY.pl_raw = SY.emitted_raw out;
          SY.pl_snap = a.client.CS.cs_model;
          SY.pl_sent = sent } in
      assert (b.channel == MP.ToServer p);
      assert (b.server == a.server);
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      // FORWARD — RECORD-level on both sides.
      introduce R.Application? (ASP.snap_wr p).R.epoch ==>
                R.Application? (ASP.rd b.server).R.epoch
      with _g.
      (
        ORD.lemma_client_write_app_finished a.client;
        assert (ASP.finished_delivered_appread_coupling a)
      );
      // CONTROL-GATED BACKWARD — `appdata_write_coupling a` conjunct 1 (ungated).
      introduce CS.ControlApplicationData? (SY.ctrl b.server) ==>
                R.Application? (ASP.snap_wr p).R.epoch
      with _g. (assert (ASP.appdata_write_coupling a));
      // BRIDGE.
      introduce R.Application? (ASP.snap_wr p).R.epoch ==>
                ASP.inflight_bridge_ready p.SY.pl_snap b.server.CS.cs_model
                  p.SY.pl_sent p.SY.pl_raw
      with _g.
      (
        // COMP 1 — RECORD-level key/iv agreement, via `cf_delivered a`.
        ORD.lemma_client_write_app_finished a.client;
        assert (ASP.finished_delivered_appread_coupling a);
        assert (ASP.cf_delivered a);
        assert (ASP.app_material_agreement a);
        assert (SMKM.peer_record_material_agrees
                  (SMKI.traffic_id CS.TrafficApplication CS.ClientTraffic) a.client a.server);
        // COMP 2 + COMP 3 — seal + roundtrip.  ~KeyUpdate from `tls_no_rekeying b`.
        assert (SMCorr.connection_state_no_key_update_trace c');
        ASP.lemma_sent_not_key_update c' sent;
        lemma_client_send_seal_rt_app a.client c' local out w sent
      )
    )
#pop-options

(** SUBSTANTIVE — SERVER SEND (post channel `MP.ToClient p`, `p.pl_snap ==
    a.server.cs_model`, `b.client == a.client`).  Mirror, except that the BRIDGE's
    `cf_delivered a` is NOT free here and is obtained by enumerating the send's own
    pre-control (see `lemma_server_send_app_write_at_cad`). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_cso_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b /\ SY.tls_no_rekeying b)
      (ensures ASP.channel_seal_ok b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s';
                    channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns ASP.channel_seal_ok b
    with _pf.
    (
      let p : SY.tls_payload =
        { SY.pl_raw = SY.emitted_raw out;
          SY.pl_snap = a.server.CS.cs_model;
          SY.pl_sent = sent } in
      assert (b.channel == MP.ToClient p);
      assert (b.client == a.client);
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      // FROM THE STEP: the sender is not failed.  Feeds `awc` conjunct 2's gate.
      // Two-run: DECORATIVE at ifuel 4 (Z3 enumerates the `Sent` arms inline).
      // DO NOT DELETE AS DEAD WEIGHT: it is the machine-checked discharge of the
      // `~ControlFailed?` half of conjunct 2's gate, without which the appeal to
      // `appdata_write_coupling` below has no recorded justification.
      HSP.lemma_sent_step_not_failed a.server.CS.cs_model s'.CS.cs_model sent;
      // FORWARD — RECORD-level on both sides.
      introduce R.Application? (ASP.snap_wr p).R.epoch ==>
                R.Application? (ASP.rd b.client).R.epoch
      with _g.
      (
        ORD.lemma_consistent_server_flight_marker_shape a.server;
        assert (ASP.finished_delivered_appread_coupling a)
      );
      // CONTROL-GATED BACKWARD — `appdata_write_coupling a` conjunct 2, whose three
      // gate halves are: `Quiet? a.channel` (hypothesis), `CAD (ctrl a.client)`
      // (the client is frozen, so `ctrl b.client == ctrl a.client`), and
      // `~ControlFailed (ctrl a.server)` (from the step, just above).
      introduce CS.ControlApplicationData? (SY.ctrl b.client) ==>
                R.Application? (ASP.snap_wr p).R.epoch
      with _g. (assert (ASP.appdata_write_coupling a));
      // BRIDGE.
      introduce R.Application? (ASP.snap_wr p).R.epoch ==>
                ASP.inflight_bridge_ready p.SY.pl_snap b.client.CS.cs_model
                  p.SY.pl_sent p.SY.pl_raw
      with _g.
      (
        // COMP 1 — RECORD-level key/iv agreement.  `cf_delivered a` is assembled
        // from the enumerated pre-control: CAD(server) gives App(wr client) by
        // `awc` conjunct 1, and App(rd server) by the CAD record-epoch producer.
        HSP.lemma_server_send_msg_class a.server s' local out w sent;
        lemma_server_send_app_write_at_cad a.server s'.CS.cs_model sent;
        assert (CS.ControlApplicationData? (SY.ctrl a.server));
        CSL.lemma_connection_appdata_keys_installed_for_role CS.ServerEndpoint a.server;
        CSL.lemma_connection_application_ready_record_epochs_installed
          CS.ServerEndpoint a.server;
        assert (ASP.appdata_write_coupling a);
        assert (ASP.cf_delivered a);
        assert (ASP.app_material_agreement a);
        assert (SMKM.peer_record_material_agrees
                  (SMKI.traffic_id CS.TrafficApplication CS.ServerTraffic) a.client a.server);
        // COMP 2 + COMP 3 — seal + roundtrip.  ~KeyUpdate from `tls_no_rekeying b`.
        assert (SMCorr.connection_state_no_key_update_trace s');
        ASP.lemma_sent_not_key_update s' sent;
        lemma_server_send_seal_rt_app a.server s' local out w sent
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    THE AGGREGATION — `lemma_app_extras_preserved` over all TWELVE clauses.

    Six per-family lemmas, one per honest transition, each discharging all twelve
    clauses of `ASP.app_extras`, then a single `move_requires_2` roll-up in the
    style of `SY.lemma_inv_preserved`.

    WHERE EACH CLAUSE'S FAMILY LIVES.  `app_seq_pairing`, the in-flight trio
    (`inflight_sender_stepped` / `inflight_single_record` /
    `inflight_raw_delta_legal`), `inflight_snap_handshake_write` and
    `read_write_coupling` are proved in ASP; `app_material_agreement` and
    `client_hs_write_record_slot_link` in AMF; `hs_material_agreement` in HMF;
    `channel_seal_ok`, `appdata_write_coupling` and
    `finished_delivered_appread_coupling` here.

    THE FIVE VACUITY ROUTES.  Four clauses are properties of the IN-FLIGHT payload
    and are therefore vacuous at a `Quiet` post-state (`ASP.lemma_quiet_inflight_
    vacuous` for the trio, `lemma_ishw_quiet` for the snapshot-write clause, and
    `lemma_cso_quiet` for the seal); `read_write_coupling` is vacuous at every
    non-`ToServer` post-state (`ASP.lemma_rwc_not_to_server`).  Between them these
    cover the two locals and the two deliveries for five of the twelve clauses,
    which is why only the sends carry real work there.

    THE THREE EXTRA HYPOTHESES beyond `app_extras a` itself:

      * `sf_inflight_finished a` / `cf_inflight_finished a` — consumed by the fdac
        deliveries (the companion message-identity clauses; they are preserved by
        their own families in this module and are carried alongside `app_extras`
        in `stream2_combined_inv`).
      * `HSP.hs_seq_pairing a` / `HSP.hs_channel_seal_ok a` — consumed by the fdac
        deliveries and by `lemma_awc_deliver_to_server` (the faithful-decode
        bridge).
      * `SY.server_config_valid_e2e a.server` — consumed ONLY by
        `AMF.lemma_ama_deliver_to_server`, which needs it at the POST server state.
        It is a function of the IMMUTABLE server config, so
        `SY.lemma_sys_step_preserves_server_config` transports it across the step;
        it is carried (not derived) for exactly the reason spelled out at
        `SY.tls_stream_inv` — the impl-side certificate-chain bound is not derivable
        from spec-level reachability, so it is assumed at entry and carried.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** VACUITY — `inflight_snap_handshake_write` at a `Quiet` post-state. **)
let lemma_ishw_quiet (s:SY.tls_system_state)
  : Lemma (requires MP.Quiet? s.channel)
          (ensures ASP.inflight_snap_handshake_write s)
  = ()

(** CLIENT SEND. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_ae_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = ASP.lemma_asp_client_send a b;
    AMF.lemma_ama_client_send a b;
    lemma_cso_client_send a b;
    ASP.lemma_asp_client_send_inflight a b;
    ASP.lemma_asp_client_send_snap_handshake_write a b;
    ASP.lemma_rwc_client_send a b;
    lemma_awc_client_send a b;
    HMF.lemma_hma_client_send a b;
    AMF.lemma_chwsl_client_send a b;
    lemma_fdac_client_send a b
#pop-options

(** SERVER SEND.  `read_write_coupling` is vacuous: the post channel is
    `ToClient`. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_ae_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = SY.lemma_server_send_shape a b;
    ASP.lemma_asp_server_send a b;
    AMF.lemma_ama_server_send a b;
    lemma_cso_server_send a b;
    ASP.lemma_asp_server_send_inflight a b;
    ASP.lemma_asp_server_send_snap_handshake_write a b;
    ASP.lemma_rwc_not_to_server b;
    lemma_awc_server_send a b;
    HMF.lemma_hma_server_send a b;
    AMF.lemma_chwsl_server_send a b;
    lemma_fdac_server_send a b
#pop-options

(** CLIENT LOCAL.  Channel unchanged (`Quiet`), so five clauses are vacuous. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_ae_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = assert (MP.Quiet? b.channel);
    ASP.lemma_asp_client_local a b;
    AMF.lemma_ama_client_local a b;
    lemma_cso_quiet b;
    ASP.lemma_quiet_inflight_vacuous b;
    lemma_ishw_quiet b;
    ASP.lemma_rwc_not_to_server b;
    lemma_awc_client_local a b;
    HMF.lemma_hma_client_local a b;
    AMF.lemma_chwsl_client_local a b;
    lemma_fdac_client_local a b
#pop-options

(** SERVER LOCAL.  Mirror. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_ae_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = assert (MP.Quiet? b.channel);
    ASP.lemma_asp_server_local a b;
    AMF.lemma_ama_server_local a b;
    lemma_cso_quiet b;
    ASP.lemma_quiet_inflight_vacuous b;
    lemma_ishw_quiet b;
    ASP.lemma_rwc_not_to_server b;
    lemma_awc_server_local a b;
    HMF.lemma_hma_server_local a b;
    AMF.lemma_chwsl_server_local a b;
    lemma_fdac_server_local a b
#pop-options

(** DELIVER TO CLIENT.  Post channel `Quiet`, so five clauses are vacuous.  Two
    clauses (`app_seq_pairing`, `app_material_agreement`) have UNBUNDLED families
    that take the delivery's components explicitly, so the shape is opened once
    here; `hs_material_agreement` splits on whether this delivery FLIPS the
    client's `hs_server_finished_verified` flag. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_ae_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        SY.tls_step_deliver_to_client a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns ASP.app_extras b
    with _pf.
    (
      ASP.lemma_asp_deliver_to_client a wire c' out raw snap sent;
      AMF.lemma_ama_deliver_to_client a wire c' out raw snap sent;
      lemma_cso_quiet b;
      ASP.lemma_quiet_inflight_vacuous b;
      lemma_ishw_quiet b;
      ASP.lemma_rwc_not_to_server b;
      lemma_awc_deliver_to_client a b;
      FStar.Classical.move_requires_2 HMF.lemma_hma_deliver_to_client_nonflip a b;
      FStar.Classical.move_requires_2 HMF.lemma_hma_deliver_to_client_flip a b;
      AMF.lemma_chwsl_deliver_to_client a b;
      lemma_fdac_deliver_to_client a b
    )
#pop-options

(** DELIVER TO SERVER.  Mirror.  `AMF.lemma_ama_deliver_to_server` additionally
    needs `SY.server_config_valid_e2e` at the POST server state; the config is
    immutable, so it transports across the step. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_ae_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        SY.server_config_valid_e2e a.server /\
        SY.tls_step_deliver_to_server a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = SY.lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns ASP.app_extras b
    with _pf.
    (
      // Two-run: DECORATIVE at the current fuel settings (Z3 re-derives config
      // immutability inline).  DO NOT DELETE AS DEAD WEIGHT: it is the
      // machine-checked transport of `server_config_valid_e2e` from `a.server`
      // to `s'`, which is what makes the `ASP.lemma_ama_deliver_to_server` call
      // below legal.  Without it that step rests on an inline derivation that a
      // future fuel change could silently lose.
      SY.lemma_cfg_pres_deliver_to_server a b;
      assert (SY.server_config_valid_e2e s');
      ASP.lemma_asp_deliver_to_server a wire s' out raw snap sent;
      ASP.lemma_ama_deliver_to_server a wire s' out raw snap sent;
      lemma_cso_quiet b;
      ASP.lemma_quiet_inflight_vacuous b;
      lemma_ishw_quiet b;
      ASP.lemma_rwc_not_to_server b;
      lemma_awc_deliver_to_server a b;
      HMF.lemma_hma_deliver_to_server a b;
      AMF.lemma_chwsl_deliver_to_server a b;
      lemma_fdac_deliver_to_server a b
    )
#pop-options

(** THE ROLL-UP.  Same shape as `SY.lemma_inv_preserved`: `move_requires_2` on the
    six families, letting the machine-product case analysis pick the one that
    applies.  The `MP.Quiet? a.channel` hypothesis carried by the four non-delivery
    families is supplied by `MP.lemma_step_channel_cases` (a step out of a directed
    channel is the matching delivery, and nothing else). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_app_extras_preserved (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        sf_inflight_finished a /\ cf_inflight_finished a /\
        HSP.hs_seq_pairing a /\ HSP.hs_channel_seal_ok a /\
        SY.server_config_valid_e2e a.server /\
        SY.tls_sys_step a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.app_extras b)
  = MP.lemma_step_channel_cases SY.tls_machine_iface a b;
    FStar.Classical.move_requires_2 lemma_ae_client_send a b;
    FStar.Classical.move_requires_2 lemma_ae_server_send a b;
    FStar.Classical.move_requires_2 lemma_ae_deliver_to_client a b;
    FStar.Classical.move_requires_2 lemma_ae_deliver_to_server a b;
    FStar.Classical.move_requires_2 lemma_ae_client_local a b;
    FStar.Classical.move_requires_2 lemma_ae_server_local a b
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    THE STREAM-2 INVARIANT LAYER.

    `stream2_extras` is the five-conjunct bundle that the application-data pairing
    argument runs on:

      `ASP.app_extras` (the twelve clauses) /\ `sf_inflight_finished` /\
      `cf_inflight_finished` /\ `HSP.hs_seq_pairing` /\ `HSP.hs_channel_seal_ok`

    The last four are NOT decoration.  They are MUTUALLY inductive with
    `app_extras`: the fdac deliveries and `lemma_awc_deliver_to_server` consume
    `hs_seq_pairing`/`hs_channel_seal_ok` (the faithful-decode bridge) and the two
    companion message-identity clauses, while `HSP.lemma_hsp_deliver_to_*` and the
    two `hscs` deliveries consume `app_extras`.  Neither half is inductive alone,
    so they must be carried — and preserved — TOGETHER.

    `stream2_combined_inv` layers this on `SY.stream_combined_inv` under the same
    `tls_no_rekeying` gate that `SY.combined_inv` uses, so that (i) `TLS13.System.fst`
    and its 26-conjunct `tls_system_inv` stay BYTE-IDENTICAL, and (ii) the RTC
    induction sees a predicate that is closed under the rekey-permitting step, with
    the gate recovered backwards by `SY.lemma_no_key_update_backward`.
    ═══════════════════════════════════════════════════════════════════════════ **)

let stream2_extras (s:SY.tls_system_state) : prop =
  ASP.app_extras s /\
  sf_inflight_finished s /\
  cf_inflight_finished s /\
  HSP.hs_seq_pairing s /\
  HSP.hs_channel_seal_ok s

(** CLIENT SEND. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_s2_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = lemma_ae_client_send a b;
    lemma_sfif_client_send a b;
    lemma_cfif_client_send a b;
    HSP.lemma_hsp_client_send a b;
    HSP.lemma_hscs_client_send a b
#pop-options

(** SERVER SEND. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_s2_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = lemma_ae_server_send a b;
    lemma_sfif_server_send a b;
    lemma_cfif_server_send a b;
    HSP.lemma_hsp_server_send a b;
    HSP.lemma_hscs_server_send a b
#pop-options

(** CLIENT LOCAL. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_s2_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = lemma_ae_client_local a b;
    lemma_sfif_client_local a b;
    lemma_cfif_client_local a b;
    HSP.lemma_hsp_client_local a b;
    HSP.lemma_hscs_client_local a b
#pop-options

(** SERVER LOCAL. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_s2_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = lemma_ae_server_local a b;
    lemma_sfif_server_local a b;
    lemma_cfif_server_local a b;
    HSP.lemma_hsp_server_local a b;
    HSP.lemma_hscs_server_local a b
#pop-options

(** DELIVER TO CLIENT.  `HSP`'s two families are UNBUNDLED, so the shape is opened
    once more here (the `app_extras` half already opened it inside
    `lemma_ae_deliver_to_client`; the two openings are independent). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_s2_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        SY.server_config_valid_e2e a.server /\
        SY.tls_step_deliver_to_client a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = lemma_ae_deliver_to_client a b;
    lemma_sfif_deliver_to_client a b;
    lemma_cfif_deliver_to_client a b;
    SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns HSP.hs_seq_pairing b /\ HSP.hs_channel_seal_ok b
    with _pf.
    (
      HSP.lemma_hsp_deliver_to_client a wire c' out raw snap sent;
      HSP.lemma_hscs_deliver_to_client a wire c' out raw snap sent
    )
#pop-options

(** DELIVER TO SERVER.  Mirror. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_s2_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        SY.server_config_valid_e2e a.server /\
        SY.tls_step_deliver_to_server a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = lemma_ae_deliver_to_server a b;
    lemma_sfif_deliver_to_server a b;
    lemma_cfif_deliver_to_server a b;
    SY.lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns HSP.hs_seq_pairing b /\ HSP.hs_channel_seal_ok b
    with _pf.
    (
      HSP.lemma_hsp_deliver_to_server a wire s' out raw snap sent;
      // Two-run: the `hscs` call is DECORATIVE (that lemma is itself `= ()`, the
      // post-state channel being `MP.Quiet`), unlike the `hsp` call above, whose
      // removal is an Error 19.  DO NOT DELETE AS DEAD WEIGHT: it records which
      // producer discharges `hs_channel_seal_ok b`, so that if that conjunct ever
      // stops being vacuous at a `Quiet` post-state the obligation is already wired.
      HSP.lemma_hscs_deliver_to_server a wire s' out raw snap sent
    )
#pop-options

(** THE FIVE-CONJUNCT ROLL-UP. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_stream2_extras_preserved (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ stream2_extras a /\
        SY.server_config_valid_e2e a.server /\
        SY.tls_sys_step a b /\
        SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures stream2_extras b)
  = MP.lemma_step_channel_cases SY.tls_machine_iface a b;
    FStar.Classical.move_requires_2 lemma_s2_client_send a b;
    FStar.Classical.move_requires_2 lemma_s2_server_send a b;
    FStar.Classical.move_requires_2 lemma_s2_deliver_to_client a b;
    FStar.Classical.move_requires_2 lemma_s2_deliver_to_server a b;
    FStar.Classical.move_requires_2 lemma_s2_client_local a b;
    FStar.Classical.move_requires_2 lemma_s2_server_local a b
#pop-options

(** The initial state satisfies all five conjuncts.  Each is vacuous or trivial
    there: the channel is `MP.Quiet` (killing every in-flight clause and both
    `hs_channel_seal_ok` arms), both endpoints are at `ControlNew` with zero
    sequence numbers and `Initial` record epochs, and every `Some?`-marker
    antecedent (`hs_client_finished`, `hs_server_finished`, `cf_delivered`) is
    `None`. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_initial_stream2_extras (cfg_c cfg_s:CS.connection_config)
  : Lemma (stream2_extras (SY.initial_tls_system cfg_c cfg_s))
  = ASP.lemma_initial_app_extras cfg_c cfg_s
#pop-options

(** The combined predicate carried through the RTC induction.  Same shape as
    `SY.stream_combined_inv`: the extras are gated on `SY.tls_no_rekeying`,
    because the step relation permits rekeying and the gate is only recovered
    BACKWARDS (by `SY.lemma_no_key_update_backward`) once the post-state is known
    to be non-rekeyed. **)
let stream2_combined_inv (s:SY.tls_system_state) : prop =
  SY.stream_combined_inv s /\
  (SY.tls_no_rekeying s ==> stream2_extras s)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_stream2_combined_inv_preserved (x y:SY.tls_system_state)
  : Lemma (requires stream2_combined_inv x /\ SY.tls_sys_step x y)
          (ensures stream2_combined_inv y)
  = SY.lemma_stream_combined_inv_preserved x y;
    introduce SY.tls_no_rekeying y ==> stream2_extras y
    with _nr.
    (
      // The gate travels backwards along the step, unlocking `combined_inv x`'s
      // structural invariant AND `stream2_extras x`.
      SY.lemma_no_key_update_backward x y;
      assert (SY.tls_system_inv x);
      assert (stream2_extras x);
      // `server_config_valid_e2e` is carried UNGATED by `SY.stream_combined_inv`,
      // which is exactly why `lemma_stream2_extras_preserved` can demand it.
      assert (SY.server_config_valid_e2e x.server);
      SY.lemma_inv_preserved x y;
      lemma_stream2_extras_preserved x y
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_initial_stream2_combined_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c /\
        SY.server_config_valid_e2e (CS.initial cfg_s))
      (ensures stream2_combined_inv (SY.initial_tls_system cfg_c cfg_s))
  = SY.lemma_initial_stream_combined_inv cfg_c cfg_s;
    lemma_initial_stream2_extras cfg_c cfg_s
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE REACHABILITY PAYOFF.

    Every reachable, non-rekeyed state with a valid server config satisfies the
    structural stream invariant AND the five-conjunct extras bundle — in
    particular `ASP.app_extras`, whose `app_seq_pairing` clause is the hypothesis
    of `lemma_app_pairing_implies_stream_integrity`.

    Mirror of `SY.lemma_reachable_stream_inv`, with the same entry hypotheses.
    ───────────────────────────────────────────────────────────────────────── **)
val lemma_reachable_stream2_inv (cfg_c cfg_s:CS.connection_config) (s:SY.tls_system_state)
  : Lemma (requires cfg_c.CS.config_role == CS.ClientEndpoint /\
                    cfg_s.CS.config_role == CS.ServerEndpoint /\
                    WFL.supported_client_config_wire_profile cfg_c /\
                    SY.server_config_valid_e2e (CS.initial cfg_s) /\
                    SY.tls_no_rekeying s /\
                    RTC.closure SY.tls_sys_step (SY.initial_tls_system cfg_c cfg_s) s)
          (ensures SY.tls_stream_inv s /\ stream2_extras s)
let lemma_reachable_stream2_inv cfg_c cfg_s s =
  lemma_initial_stream2_combined_inv cfg_c cfg_s;
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 lemma_stream2_combined_inv_preserved);
  RTC.stable_on_closure SY.tls_sys_step stream2_combined_inv ()
