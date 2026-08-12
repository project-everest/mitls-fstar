module TLS13.System.HsMaterialFamilies

(**
  GATE 2a — conjunct 1 (`hs_material_agreement`) step-family PRESERVATION, plus
  the flip ESTABLISH producer (`lemma_establish`).

  `hs_material_agreement s` says: once the client has verified the server's
  Finished and both endpoints hold their client-handshake-traffic slot, the two
  slots' record material agrees.  Its ONLY writable field is the pair of
  `ks_client_handshake_traffic` slots (the consequent
  `key_schedule_traffic_record_material_agrees` reads nothing else — see
  `TLS13.Spec.StateMachine.KeyMaterial.key_schedule_traffic_record_material_agrees`),
  so preservation reduces to SLOT MONOTONICITY at the acting endpoint.

  The handshake-traffic slot is only ever OVERWRITTEN by a
  `LocalInstallTrafficKeys` install, which `traffic_install_allowed_at_stage_for_role`
  legalises at exactly `HsServerHelloReceived` (client) / `HsServerHelloSent`
  (server).  Hence `lemma_slot_frozen_offstage`: a step whose SOURCE control is
  neither install stage leaves the slot untouched.  The two install-stage
  exclusions are recovered per acting endpoint:
    * server side:  `SLM.lemma_flag_excludes_server_hello_sent` (flag ⇒ server ≠
      HsServerHelloSent) and `server_stage_ok` (server ≠ HsServerHelloReceived).
    * client side:  `lemma_client_flag_excludes_shr` (flag ⇒ client ≠
      HsServerHelloReceived, proved by RECV-potential trace induction, reusing
      `SLM.lemma_client_flag_facts`) and `client_stage_ok` (client ≠
      HsServerHelloSent).

  Five of the six families PRESERVE (server_send / server_local /
  deliver_to_server / client_send / client_local).  The sixth,
  `deliver_to_client`, is where the client flag can FLIP false→true (atomic
  Finished receipt, HsCertificateVerifyVerified → HsServerFinishedVerified); its
  NON-FLIP branch preserves (here, `lemma_hma_deliver_to_client_nonflip`), and its
  FLIP branch must ESTABLISH via `lemma_establish`.  See the module report for the
  remaining server-control-recovery obligation of the flip branch.
**)

module CS   = TLS13.Spec.StateMachine
module M    = TLS13.Messages
module CL   = TLS13.ConnectionLog
module R    = TLS13.Record.Spec
module B    = TLS13.Bytes
module Seq  = FStar.Seq
module SMR  = TLS13.Spec.StateMachine.Reachability
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module SMCorr = TLS13.Spec.StateMachine.Correspondence
module SY   = TLS13.System
module MP   = Common.MachineProduct
module ASP  = TLS13.System.AppSeqPairing
module WStep = TLS13.System.WireStep
module ES   = TLS13.Spec.Endpoint.Server
module EC   = TLS13.Spec.Endpoint.Client
module CTy  = TLS13.Impl.CanonicalTypes
module CW   = TLS13.Spec.Endpoint.Wire
module EAPI = TLS13.Spec.Endpoint.API
module SM   = Common.StateMachine
module SLM  = TLS13.System.SlotMono
module HANR = TLS13.ConnectionState.HandshakeAgreementNonReady
module WFL  = TLS13.Spec.WireFormatLemmas
module CCS  = TLS13.ConnectionState.ClientCanonicalShape
module SCS  = TLS13.ConnectionState.ServerCanonicalShape
module CNCP = TLS13.ConnectionState.ClientNoCcsFromPairing
module SNCP = TLS13.ConnectionState.ServerNoCcsFromPairing
module SSR  = TLS13.System.ServerSfsRecovery
module CSLemmas = TLS13.ConnectionState.Lemmas
module W    = TLS13.Wire.Spec
module L    = FStar.List.Tot
module SMCan = TLS13.Spec.StateMachine.Canonical

(* ================================================================== *)
(* The traffic id and the consequent predicate                         *)
(* ================================================================== *)

let tid : SMKI.labeled_traffic_epoch = SMKI.traffic_id CS.TrafficHandshake CS.ClientTraffic

let ks_agree (client server:CS.connection_state) : prop =
  SMKM.key_schedule_traffic_record_material_agrees tid client server

(* ================================================================== *)
(* Slot monotonicity: off both install stages the client-handshake-    *)
(* traffic slot is unchanged (in BOTH directions).                     *)
(* ================================================================== *)

#push-options "--fuel 4 --ifuel 10 --z3rlimit 300 --split_queries always"
let lemma_slot_frozen_offstage
  (m0 m1:CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m0 ce /\ CS.step_model m0 ce == Some m1 /\
        m0.CS.model_control =!= CS.ControlHandshaking CS.HsServerHelloReceived /\
        m0.CS.model_control =!= CS.ControlHandshaking CS.HsServerHelloSent)
      (ensures
        m1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic
          == m0.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
  = ()
#pop-options

(* ================================================================== *)
(* Client flag ⇒ control ≠ HsServerHelloReceived  (RECV-potential)     *)
(* ================================================================== *)

(** A legal client model step preserves the "verified ⇒ recv-potential ≥ 4 or
    Failed" property (potential is non-increasing except through a fail, and a
    fresh verified-flag lands at recv-potential ≥ 4). **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 100 --split_queries always"
let lemma_potential_step
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ce /\ CS.step_model m ce == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        (WStep.client_recv_potential m.CS.model_control >= 4 \/
         CS.ControlFailed? m.CS.model_control))
      (ensures
        (WStep.client_recv_potential m'.CS.model_control >= 4 \/
         CS.ControlFailed? m'.CS.model_control))
  = ()
#pop-options

let flag_pot_ok (m:CS.connection_model) : prop =
  m.CS.model_handshake.CS.hs_server_finished_verified ==>
    (WStep.client_recv_potential m.CS.model_control >= 4 \/
     CS.ControlFailed? m.CS.model_control)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_flag_pot_step
  (st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        flag_pot_ok st0.CS.cs_model)
      (ensures flag_pot_ok st1.CS.cs_model)
  = WStep.lemma_client_step_model_stepped st0 ev st1 out;
    eliminate exists (ce:CS.conn_event).
      CS.legal_event st0.CS.cs_model ce /\
      CS.step_model st0.CS.cs_model ce == Some st1.CS.cs_model
    with
    (
      SLM.lemma_client_flag_facts st0.CS.cs_model ce st1.CS.cs_model;
      if st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified then
        lemma_potential_step st0.CS.cs_model st1.CS.cs_model ce
      else ()
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_flag_pot_trace
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        flag_pot_ok st0.CS.cs_model)
      (ensures flag_pot_ok st1.CS.cs_model)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      WStep.lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_flag_pot_step st0 s' tr.SM.tr_event tr.SM.tr_output;
      lemma_flag_pot_trace init s' st1 rest
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_flag_excludes_shr
  (cfg:CS.connection_config) (client:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial cfg) client /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
        cfg.CS.config_role == CS.ClientEndpoint)
      (ensures
        client.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerHelloReceived)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = WStep.client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    with
    (
      assert (flag_pot_ok init.CS.cs_model);
      lemma_flag_pot_trace init init client trace
    )
#pop-options

(* ================================================================== *)
(* Client reachability excludes HsServerFinishedReceived               *)
(* (the atomic client SM never enters it), so a client LOCAL step      *)
(* cannot freshly set the verified flag.                               *)
(* ================================================================== *)

#push-options "--fuel 4 --ifuel 10 --z3rlimit 400 --split_queries always"
let lemma_client_step_not_sfr
  (st0 st1:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived)
      (ensures st1.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_not_sfr_trace
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived)
      (ensures
        st1.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      lemma_client_step_not_sfr st0 s' tr.SM.tr_event tr.SM.tr_output;
      lemma_client_not_sfr_trace init s' st1 rest
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_reachable_not_sfr
  (cfg:CS.connection_config) (client:CS.connection_state)
  : Lemma
      (requires WStep.client_reachable (CS.initial cfg) client)
      (ensures
        client.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived)
  = let sm = WStep.client_sm (CS.initial cfg) in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm (CS.initial cfg) trace client
    with
      lemma_client_not_sfr_trace (CS.initial cfg) (CS.initial cfg) client trace
#pop-options

(** A client LOCAL-event step from a non-SFR control never freshly sets the
    verified flag ... EXCEPT via the coalesced protected handshake.

    ── STATEMENT CHANGE, FORCED BY A SPEC CHANGE WE DID NOT MAKE ───────────────
    This lemma used to conclude plain monotonicity
      `st1.flag ==> st0.flag`.
    That is now FALSE.  `origin/agentic` added the client local event
    `CTy.ClientProcessPendingHandshake`, which `EC.client_local_event_matches`
    maps to a TAIL `CS.ConnProtectedHandshake` step:

        | ClientProcessPendingHandshake, CS.ConnProtectedHandshake step ->
            step.protected_handshake_head == false

    A client sitting at `HsCertificateVerifyVerified` (which is NOT
    `HsServerFinishedReceived`, so the old hypothesis does not exclude it) with a
    buffered server `Finished` can therefore drain it with a LOCAL event and set
    `hs_server_finished_verified` in one step.

    The conclusion is weakened to a DISJUNCTION: either the flag was already set,
    or the step landed at `HsServerFinishedVerified` -- which is where the atomic
    `CL.Received, M.Finished` arm of `CS.step_handshake_message` puts a client, and
    is exactly the entry condition of the ControlFailed-aware flip producer
    `lemma_establish_cf`.  Both call sites below discharge the new disjunct with
    that producer, so no downstream statement changes. **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 400 --split_queries always"
let lemma_client_localevent_flag_mono
  (st0 st1:CS.connection_state) (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived)
      (ensures
        (st1.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==>
         (st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified \/
          st1.CS.cs_model.CS.model_control
            == CS.ControlHandshaking CS.HsServerFinishedVerified)))
  = ()
#pop-options

(** At a client SEND the flip disjunct above is IMPOSSIBLE: the emitted event is
    pinned to `SMKM.sent_tls_event sent` by the event-log shape
    (`CS.legal_connection_delta` appends exactly `delta_event`), and
    `sent_tls_event` is a `CS.ConnNetworkEvent`.  A `ClientProcessPendingHandshake`
    would append a `CS.ConnProtectedHandshake`, so it cannot be this step, and
    plain flag monotonicity is recovered. **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 400 --split_queries always"
let lemma_client_sendevent_flag_mono
  (st0 st1:CS.connection_state) (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (sent:M.tls_message)
  : Lemma
      (requires EC.client_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedReceived /\
        st1.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent])
      (ensures
        (st1.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==>
         st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified))
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CTy.client_local_event_matches st0 local conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
    with
    (
      assert (st1.CS.cs_event_log == st0.CS.cs_event_log @ [conn_ev]);
      L.append_length_inv_tail st0.CS.cs_event_log [conn_ev]
                               st0.CS.cs_event_log [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent)
    )
#pop-options

(* ================================================================== *)
(* The FLIP producer: at (client @ HsServerFinishedVerified,           *)
(* server @ HsServerFinishedSent, both slots present, Quiet), the two  *)
(* client-handshake-traffic slots agree.                               *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_establish (s:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv s /\ MP.Quiet? s.channel /\
        s.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        s.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        (* CROSS-RECORD REASSEMBLY.  `lemma_client_reachable_sfv_shared_secret_present`
           reconstructs the client's exact spine by forward induction, and a BUFFERING
           protected-handshake step has no slot in that spine.  In the paired system the
           client provably never buffers (the ATLAS server emits one record per handshake
           message, so the STEP-1 guard makes buffering illegal), but proving it needs the
           cross-endpoint record-material agreement, which lives ABOVE `TLS13.System`.
           Taken as an input; discharged by callers at that layer. *)
        CCS.no_buffering_steps s.client.CS.cs_event_log /\
        Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
      (ensures ks_agree s.client s.server)
  = let client = s.client in
    let server = s.server in
    assert (SY.client_byte_reachable s);
    assert (SY.server_byte_reachable s);
    assert (SY.byte_pairing s);
    assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent server.CS.cs_wire_log.CL.raw_received);
    assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received);
    CNCP.lemma_no_received_ccs_from_pairing_client client server;
    SNCP.lemma_no_received_ccs_from_pairing client server;
    CCS.lemma_client_reachable_sfv_shared_secret_present client.CS.cs_model.CS.model_config client;
    SCS.lemma_server_reachable_sfs_shared_secret_present server.CS.cs_model.CS.model_config server;
    assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    assert (SY.hello_key_shares_ok s);
    assert (WFL.paired_cleartext_hello_key_shares client server);
    assert (SY.ch_wire_equiv s);
    assert (SY.sh_wire_equiv s);
    WStep.lemma_consistent_server_hello_wire_bound server;
    (match client.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
           server.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
           client.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
           server.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
       eliminate exists raw1.
         CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw1 /\
         CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw1
       with
         eliminate exists raw2.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
         with
           WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
             client server client_ch server_ch client_sh server_sh
             raw1 raw1 raw2 raw2
     | _ -> ());
    assert (SMCorr.same_key_derivation_checkpoint SMKI.DeriveHandshakeTraffic client server);
    HANR.lemma_handshake_client_traffic_key_schedule_material_agrees_nonready client server
#pop-options

(* ================================================================== *)
(* ControlFailed-aware FLIP producer.  Same conclusion as             *)
(* [lemma_establish] but WITHOUT requiring the server at              *)
(* HsServerFinishedSent: the server's shared secret is recovered      *)
(* control-independently from its present client-handshake-traffic    *)
(* slot (Lemmas.lemma_consistent_client_handshake_traffic_slot_shared_secret), *)
(* and the slot-level agreement is discharged by the ControlFailed-aware *)
(* HANR variant, which never consults record-key consistency.  This    *)
(* eliminates the [~(ControlFailed? server)] residual at the flip.     *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_establish_cf (s:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv s /\ MP.Quiet? s.channel /\
        s.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        (* CROSS-RECORD REASSEMBLY.  `lemma_client_reachable_sfv_shared_secret_present`
           reconstructs the client's exact spine by forward induction, and a BUFFERING
           protected-handshake step has no slot in that spine.  In the paired system the
           client provably never buffers (the ATLAS server emits one record per handshake
           message, so the STEP-1 guard makes buffering illegal), but proving it needs the
           cross-endpoint record-material agreement, which lives ABOVE `TLS13.System`.
           Taken as an input; discharged by callers at that layer. *)
        CCS.no_buffering_steps s.client.CS.cs_event_log /\
        Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
      (ensures ks_agree s.client s.server)
  = let client = s.client in
    let server = s.server in
    assert (SY.client_byte_reachable s);
    assert (SY.server_byte_reachable s);
    assert (SY.byte_pairing s);
    assert (Seq.equal client.CS.cs_wire_log.CL.raw_sent server.CS.cs_wire_log.CL.raw_received);
    assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received);
    CNCP.lemma_no_received_ccs_from_pairing_client client server;
    SNCP.lemma_no_received_ccs_from_pairing client server;
    CCS.lemma_client_reachable_sfv_shared_secret_present client.CS.cs_model.CS.model_config client;
    // server shared secret from the present slot, control-independently.
    CSLemmas.lemma_consistent_client_handshake_traffic_slot_shared_secret server;
    // server's hellos from the present slot, control-independently (survives
    // ControlFailed via model_handshake preservation under fail_model).
    SCS.lemma_server_reachable_traffic_slot_hellos_present
      server.CS.cs_model.CS.model_config server;
    assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
    assert (SY.hello_key_shares_ok s);
    assert (WFL.paired_cleartext_hello_key_shares client server);
    assert (SY.ch_wire_equiv s);
    assert (SY.sh_wire_equiv s);
    WStep.lemma_consistent_server_hello_wire_bound server;
    (match client.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
           server.CS.cs_model.CS.model_handshake.CS.hs_client_hello,
           client.CS.cs_model.CS.model_handshake.CS.hs_server_hello,
           server.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
     | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
       eliminate exists raw1.
         CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw1 /\
         CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw1
       with
         eliminate exists raw2.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
         with
           WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
             client server client_ch server_ch client_sh server_sh
             raw1 raw1 raw2 raw2
     | _ -> ());
    assert (SMCorr.same_key_derivation_checkpoint SMKI.DeriveHandshakeTraffic client server);
    HANR.lemma_handshake_client_traffic_key_schedule_material_agrees_nonready_cf client server
#pop-options

(* ================================================================== *)
(* Monotone-transfer helpers                                           *)
(* ================================================================== *)

(** SERVER-acting transfer: the client is frozen; the server's slot is frozen
    (its control excludes both install stages: HsServerHelloSent by the client's
    verified flag via SLM, HsServerHelloReceived by `server_stage_ok`). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_server_transfer (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\ SY.tls_system_inv b /\
        b.client == a.client /\
        WStep.model_stepped a.server.CS.cs_model b.server.CS.cs_model)
      (ensures ASP.hs_material_agreement b)
  = introduce
      ( b.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
        Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic )
      ==> ks_agree b.client b.server
    with
    (
      SLM.lemma_flag_excludes_server_hello_sent a;
      assert (SY.server_stage_ok a.server);
      assert (a.server.CS.cs_model.CS.model_control
                =!= CS.ControlHandshaking CS.HsServerHelloReceived);
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some b.server.CS.cs_model
      with
      (
        lemma_slot_frozen_offstage a.server.CS.cs_model b.server.CS.cs_model ce;
        assert (ks_agree a.client a.server)
      )
    )
#pop-options

(** CLIENT-acting transfer: the server is frozen; the client's slot is frozen
    (its control excludes both install stages: HsServerHelloReceived by the
    verified flag via `lemma_client_flag_excludes_shr`, HsServerHelloSent by
    `client_stage_ok`).  The flag-monotonicity hypothesis rules out a fresh flag
    set (only `deliver_to_client` can do that — handled separately). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_client_transfer (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\ SY.tls_system_inv b /\
        b.server == a.server /\
        WStep.model_stepped a.client.CS.cs_model b.client.CS.cs_model /\
        (b.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==>
         a.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified))
      (ensures ASP.hs_material_agreement b)
  = introduce
      ( b.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
        Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic )
      ==> ks_agree b.client b.server
    with
    (
      lemma_client_flag_excludes_shr a.client.CS.cs_model.CS.model_config a.client;
      assert (SY.client_stage_ok a.client);
      assert (a.client.CS.cs_model.CS.model_control
                =!= CS.ControlHandshaking CS.HsServerHelloSent);
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some b.client.CS.cs_model
      with
      (
        lemma_slot_frozen_offstage a.client.CS.cs_model b.client.CS.cs_model ce;
        assert (ks_agree a.client a.server)
      )
    )
#pop-options

(* ================================================================== *)
(* SERVER families (client frozen)                                     *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.hs_material_agreement b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (w:CW.wire_message) (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    with
    (
      WStep.lemma_server_step_model_stepped a.server (SM.LocalEvent local) s' out;
      lemma_hma_server_transfer a b
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_local a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.hs_material_agreement b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    with
    (
      WStep.lemma_server_step_model_stepped a.server (SM.LocalEvent local) s' out;
      lemma_hma_server_transfer a b
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\
        SY.tls_step_deliver_to_server a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.hs_material_agreement b)
  = SY.lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    with
    (
      WStep.lemma_server_step_model_stepped a.server (SM.WireEvent wire) s' out;
      lemma_hma_server_transfer a b
    )
#pop-options

(* ================================================================== *)
(* CLIENT families (server frozen)                                     *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.hs_material_agreement b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (w:CW.wire_message) (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    with
    (
      WStep.lemma_client_step_model_stepped a.client (SM.LocalEvent local) c' out;
      lemma_client_reachable_not_sfr a.client.CS.cs_model.CS.model_config a.client;
      lemma_client_sendevent_flag_mono a.client c' local out sent;
      lemma_hma_client_transfer a b
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_local a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b /\
        (* CROSS-RECORD REASSEMBLY: needed by `lemma_establish_cf` below.  A client
           LOCAL step never appends a buffering entry (buffering arises only on record
           delivery), so this is preserved from `a`; it is discharged one layer up,
           where the protected-record seal is in scope. *)
        CCS.no_buffering_steps b.client.CS.cs_event_log)
      (ensures ASP.hs_material_agreement b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    with
    (
      WStep.lemma_client_step_model_stepped a.client (SM.LocalEvent local) c' out;
      lemma_client_reachable_not_sfr a.client.CS.cs_model.CS.model_config a.client;
      lemma_client_localevent_flag_mono a.client c' local out;
      (* NEW DISJUNCT (coalesced protected handshake): a `ClientProcessPendingHandshake`
         local event can drain a buffered server `Finished` and set the verified
         flag FRESH, landing at `HsServerFinishedVerified`.  The channel is still
         `Quiet` here (`tls_step_client_local` emits no wire output), and
         `SY.tls_system_inv b` is a hypothesis, so the ControlFailed-AWARE flip
         producer `lemma_establish_cf` applies directly -- it needs only the client
         control plus both slots, NOT the server at `HsServerFinishedSent`.  Note
         this is a SLOT-level producer; no record-level material is inferred. *)
      if a.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified
      then lemma_hma_client_transfer a b
      else
        introduce
          ( b.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
            Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
            Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic )
          ==> ks_agree b.client b.server
        with
          lemma_establish_cf b
    )
#pop-options

(** DELIVER TO CLIENT — NON-FLIP branch (the client's verified flag already held
    in `a`).  The client's slot is frozen (a wire receipt never installs the
    handshake-traffic slot) and the server is frozen, so the material agreement
    carries.  The FLIP branch (flag false→true) is handled by `lemma_establish`
    once the server is recovered at `HsServerFinishedSent` (see report). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_deliver_to_client_nonflip (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.hs_material_agreement a /\
        a.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
        SY.tls_step_deliver_to_client a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b)
      (ensures ASP.hs_material_agreement b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    with
    (
      WStep.lemma_client_step_model_stepped a.client (SM.WireEvent wire) c' out;
      lemma_hma_client_transfer a b
    )
#pop-options

(** A client WireEvent step that FRESHLY sets the verified flag (false in the
    pre-state) lands EXACTLY at `HsServerFinishedVerified`: the only RECEIVED
    transition that sets the flag is the atomic
    `Received, Finished @ HsCertificateVerifyVerified -> HsServerFinishedVerified`
    (StateMachine.fst:740).  (The other flag-set, `LocalVerifyFinished`, is a
    LOCAL event, excluded here.) **)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
(** Model-level: the ONLY two transitions that set the verified flag from unset
    (`LocalVerifyFinished` at HsServerFinishedReceived, and the atomic
    `Received, Finished` at HsCertificateVerifyVerified — StateMachine.fst:551,740)
    BOTH land at `HsServerFinishedVerified`; `fail_model` preserves the (unset)
    flag.  Hence any single step that freshly sets the flag lands at SFV. **)
let lemma_client_model_flag_flip_sfv
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\ CS.step_model m ev == Some m' /\
        ~(m.CS.model_handshake.CS.hs_server_finished_verified))
      (ensures
        m'.CS.model_handshake.CS.hs_server_finished_verified ==>
          m'.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = ()
#pop-options

(** A client WireEvent step that FRESHLY sets the verified flag lands EXACTLY at
    `HsServerFinishedVerified`. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_wire_flag_flip_sfv
  (st0 st1:CS.connection_state) (wire:CW.wire_message)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step #CTy.client_local_event st0 (SM.WireEvent wire) st1 out /\
        ~(st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified))
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified ==>
          st1.CS.cs_model.CS.model_control
            == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = WStep.lemma_client_step_model_stepped st0 (SM.WireEvent wire) st1 out;
    eliminate exists (ev:CS.conn_event).
      CS.legal_event st0.CS.cs_model ev /\
      CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model
    with
      lemma_client_model_flag_flip_sfv st0.CS.cs_model ev st1.CS.cs_model
#pop-options

(** DELIVER TO CLIENT — FLIP branch (the client's verified flag was FALSE in `a`
    and becomes TRUE in `b`).  The delivered record is the server Finished; the
    client lands at `HsServerFinishedVerified`.  `ks_agree` is established by
    `lemma_establish_cf`, which recovers the server's shared secret
    control-independently from its present client-handshake-traffic slot and
    discharges the slot-level agreement via the ControlFailed-aware HANR variant.
    NO residual hypothesis on the server's control is required. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hma_deliver_to_client_flip (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        ~(a.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified) /\
        SY.tls_step_deliver_to_client a b /\ SY.tls_no_rekeying b /\ SY.tls_system_inv b /\
        (* CROSS-RECORD REASSEMBLY: needed by `lemma_establish_cf` below.  Discharged
           one layer up, where the protected-record seal shows the paired client never
           buffers (the ATLAS server emits one record per handshake message). *)
        CCS.no_buffering_steps b.client.CS.cs_event_log)
      (ensures ASP.hs_material_agreement b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    with
    (
      // hs_material_agreement is an implication; introduce its antecedent.
      introduce
        ( b.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
          Some? b.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
          Some? b.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic )
        ==> SMKM.key_schedule_traffic_record_material_agrees tid b.client b.server
      with
      (
        // FLIP ⇒ the client lands at HsServerFinishedVerified.
        lemma_client_wire_flag_flip_sfv a.client c' wire out;
        assert (b.client.CS.cs_model.CS.model_control
                  == CS.ControlHandshaking CS.HsServerFinishedVerified);
        // deliver_to_client freezes the server and quiets the channel.
        assert (b.server == a.server);
        assert (MP.Quiet? b.channel);
        // Both slots present (antecedent) + client@SFV ⇒ ks_agree, with the
        // server's shared secret recovered control-independently from its slot.
        lemma_establish_cf b
      )
    )
#pop-options
