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
module ID   = FStar.IndefiniteDescription
module RTC  = FStar.ReflexiveTransitiveClosure

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
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent
            { CL.message_direction = CL.Received; CL.message_value = msg } in
         SMCan.canonical_wire_step a.client c' conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.network_input_message_projection a.client wire msg /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns ASP.finished_delivered_appread_coupling b
      with _pd.
      (
        let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
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
    qawc SERVER-local family conclude the server never FRESHLY reaches
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
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    qawc LOCAL families.  Channel stays `Quiet`.  For a client local (server
    frozen): conjunct 1 `CAD(server) ==> App(wr client)` — the antecedent is frozen
    (server), `qawc a` gives `App(wr a.client)`, forwarded by the write-monotone
    `lemma_client_local_preserves_app_write`; conjunct 2 `CAD(client) ==> App(wr
    server)` — `lemma_client_local_cad_backward` pushes `CAD(c')` back to
    `CAD(a.client)`, and `qawc a` gives `App(wr a.server)` (= frozen `wr b.server`).
    Server local is the mirror (write-forward on conjunct 2, marker-backed
    CAD-backward on conjunct 1). **)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_qawc_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.quiet_appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b)
      (ensures ASP.quiet_appdata_write_coupling b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns ASP.quiet_appdata_write_coupling b
    with _pf.
    (
      ASP.lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      returns ASP.quiet_appdata_write_coupling b
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
let lemma_qawc_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.quiet_appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b)
      (ensures ASP.quiet_appdata_write_coupling b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns ASP.quiet_appdata_write_coupling b
    with _pf.
    (
      ASP.lemma_server_local_extract a.server s' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      returns ASP.quiet_appdata_write_coupling b
      with _pe.
      (
        introduce
          CS.ControlApplicationData? (SY.ctrl b.client)
          ==> R.Application? (ASP.wr b.server).R.epoch
        with _. lemma_server_local_preserves_app_write a.server s' ce;
        lemma_server_local_cad_backward a.server s' ce
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    qawc SEND families — both VACUOUS.  A send exits `Quiet` to `ToServer`
    (client) / `ToClient` (server), so `quiet_appdata_write_coupling`'s `MP.Quiet?`
    gate is FALSE at `b` and the whole conjunct is trivially true.  We only need to
    pin the post-channel head via the shape lemma / destructuring. **)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_qawc_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.quiet_appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b)
      (ensures ASP.quiet_appdata_write_coupling b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns ASP.quiet_appdata_write_coupling b
    with _pf. (assert (MP.ToServer? b.channel))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_qawc_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.quiet_appdata_write_coupling a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b)
      (ensures ASP.quiet_appdata_write_coupling b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns ASP.quiet_appdata_write_coupling b
    with _pf. (assert (MP.ToClient? b.channel))
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
