module TLS13.System.ServerSfsRecovery

(**
  STATUS (Gate 2a, post-ControlFailed-generalization): this module is currently
  UNCONSUMED.  The forward-direction flip establishment
  (`HsMaterialFamilies.lemma_hma_deliver_to_client_flip`) now closes at the
  SLOT level with NO residual — `lemma_establish_cf` recovers the server's
  shared secret and both hellos from its present `ks_client_handshake_traffic`
  slot, control-independently, and discharges the agreement via the
  ControlFailed-aware HANR variant (which never consults record-key
  consistency).  So the SFS-counting server-control recovery below is not needed
  for the forward direction and its `~(ControlFailed? ...)` residual is moot.

  RETAINED (do NOT delete): the REVERSE-direction (server-side mirror) agreement
  is still outstanding, and an SFS-counting recovery of this shape is the
  plausible tool for it.  Kept in ROOT_FILES so it stays verified and ready.

  GATE 2a — the deliver_to_client FLIP server-control recovery, via the SlotMono
  record-counting technique (NON-circular: record counts, NOT crypto decode).

  This module discharges the counting HALF of the flip's server-control
  obligation.  Given a Quiet post-flip state `b` whose CLIENT sits at
  `HsServerFinishedVerified`, it proves two byte-count facts about the SERVER:

    * SENT ≥ 1 :  `raw_appdata_count b.server.raw_sent >= 1`
                  (client verified ⇒ client received ≥ 1 protected record
                   [SlotMono.lemma_client_flag_recv_ge1]; byte-pairing at Quiet
                   transfers the count to the server's SENT log).
                  NOTE: this was ≥ 4 until the coalesced-protected-flight spec
                  change; a TAIL `ConnProtectedHandshake` step is charged ZERO
                  received bytes, so the client-side `≥ 4` is now FALSE.  See
                  `lemma_flip_server_sent_ge1` and RESIDUAL 2 at
                  `lemma_flip_recovers_server_sfs`.

    * RECV = 0 :  `raw_appdata_count b.server.raw_received == 0`
                  (a client at `HsServerFinishedVerified` is pre-application-data,
                   so it has SENT 0 protected records
                   [WStep.lemma_client_preappdata_sent_no_appdata]; byte-pairing
                   transfers 0 to the server's RECEIVED log).

  From SENT ≥ 1 the server is past the pre-flight region, so it is NOT at
  `HsClientHelloReceived` (see `lemma_flip_server_not_client_hello_received`),
  which is one of the two server exclusions the non-ready handshake agreement
  producer needs.

  RESIDUAL (reported, NOT closed here).  The counting route pins the server to
  the set { HsServerFinishedSent } ∪ { post-client-Finished controls } ∪
  { ControlFailed }.  The post-client-Finished controls are excludable by
  RECV = 0 (they require having received the client Finished, an appdata record),
  but `ControlFailed` is NOT excludable by counts: a reachable server can send a
  PROTECTED `Close_notify` alert from `HsServerEncryptedFlightSent`
  (StateMachine.fst `M.TlsAlert alert, _ -> fail_model`), which is an
  ApplicationData-typed single record (`protected_record_count CL.Sent
  (TlsAlert Close_notify) == 1`), landing at `ControlFailed` with
  `raw_appdata_count raw_sent == 4` (3 flight records + 1 alert) and
  `hs_server_finished == None`.  That state satisfies BOTH SENT ≥ 4 and RECV = 0
  yet is `ControlFailed`.  It is ruled out in the ACTUAL flip only because the
  client could not have reached `HsServerFinishedVerified` by DECODING that
  record (a `Close_notify`, not a `Finished`) — a protected-message decode /
  key-agreement fact that is (a) absent from `SY.tls_system_inv`
  (`channel_consistent` constrains only the CLEARTEXT hellos) and (b) circular
  with the handshake-key agreement this whole gate is establishing.  See the
  module report.
**)

module CS    = TLS13.Spec.StateMachine
module SY    = TLS13.System
module MP    = Common.MachineProduct
module WStep = TLS13.System.WireStep
module SLM   = TLS13.System.SlotMono
module SMR   = TLS13.Spec.StateMachine.Reachability
module CL    = TLS13.ConnectionLog
module B     = TLS13.Bytes
module Seq   = FStar.Seq
module SM    = Common.StateMachine
module CW    = TLS13.Spec.Endpoint.Wire
module CTy   = TLS13.Impl.CanonicalTypes
module EAPI  = TLS13.Spec.Endpoint.API
module EC    = TLS13.Spec.Endpoint.Client
module WFL   = TLS13.Spec.WireFormatLemmas
module RTC   = FStar.ReflexiveTransitiveClosure
module ID    = FStar.IndefiniteDescription
module WFSM  = Common.WireFormatStateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module WF    = Common.WireFormat
module L     = FStar.List.Tot
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module ES    = TLS13.Spec.Endpoint.Server
module M     = TLS13.Messages
module T     = TLS13.Types

(* ================================================================== *)
(* Client shape: control == HsServerFinishedVerified ==> the verified  *)
(* flag is set.  Both transitions that land at HsServerFinishedVerified *)
(* (the atomic Received-Finished at HsCertificateVerifyVerified, and    *)
(* LocalVerifyFinished at HsServerFinishedReceived) set the flag, and   *)
(* no step clears it — so this is single-step inductive.                *)
(* ================================================================== *)

let client_sfv_flag_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
  (m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified ==>
     m.CS.model_handshake.CS.hs_server_finished_verified)

#push-options "--fuel 2 --ifuel 5 --z3rlimit 60"
let lemma_step_client_sfv_flag_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        client_sfv_flag_shape m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures client_sfv_flag_shape m')
  = ()
#pop-options

let lemma_delta_client_sfv_flag_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires
        client_sfv_flag_shape st0.CS.cs_model /\
        SMR.connection_state_single_step st0 st1)
      (ensures client_sfv_flag_shape st1.CS.cs_model)
  = assert (exists delta. CS.legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_client_sfv_flag_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_client_sfv_flag_shape (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures client_sfv_flag_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = client_sfv_flag_shape st.CS.cs_model in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ SMR.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with
        lemma_delta_client_sfv_flag_shape x y in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(* ================================================================== *)
(* SENT >= 1 : the server has SENT at least one protected record.      *)
(*                                                                     *)
(* THIS LEMMA USED TO SAY `>= 4`, AND THAT IS NOW FALSE.               *)
(* The old derivation read the client's RECEIVED record count off its  *)
(* control (`HsServerFinishedVerified` ==> four protected records      *)
(* received) and transported it to the server through `byte_pairing`.  *)
(* The coalesced-protected-flight spec change killed the client half:  *)
(* a TAIL `CS.ConnProtectedHandshake` step is charged                  *)
(* `Seq.equal raw_received B.empty` by `CS.event_raw_delta_legal`, so  *)
(* a client can drain EncryptedExtensions|Certificate|CertificateVerify*)
(* |Finished out of ONE record (one HEAD step plus three TAIL steps)   *)
(* and reach `HsServerFinishedVerified` having received exactly ONE    *)
(* record.  `SLM.lemma_client_flag_recv_ge1` is the strongest true     *)
(* client-side bound, hence `>= 1` here.                               *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_flip_server_sent_ge1 (b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv b /\ MP.Quiet? b.channel /\
        b.client.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified)
      (ensures
        WStep.raw_appdata_count b.server.CS.cs_wire_log.CL.raw_sent >= 1)
  = // roles + reachability + byte pairing come out of the transparent invariant
    assert (SY.client_byte_reachable b);
    assert (SY.byte_pairing b);
    assert (b.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert (SMR.connection_state_consistent b.client);
    // control HsServerFinishedVerified ==> the verified flag is set
    lemma_consistent_client_sfv_flag_shape b.client;
    assert (b.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified);
    // flag ==> client has RECEIVED >= 1 protected record
    SLM.lemma_client_flag_recv_ge1 b.client.CS.cs_model.CS.model_config b.client;
    // byte pairing at Quiet: server.raw_sent == client.raw_received
    let ss = b.server.CS.cs_wire_log.CL.raw_sent in
    let cr = b.client.CS.cs_wire_log.CL.raw_received in
    assert (Seq.equal ss cr);
    WStep.lemma_raw_appdata_count_seq_equal ss cr
#pop-options

(* ================================================================== *)
(* RECV == 0 : the server has RECEIVED zero protected records.         *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_flip_server_recv_eq0 (b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv b /\ MP.Quiet? b.channel /\
        b.client.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified)
      (ensures
        WStep.raw_appdata_count b.server.CS.cs_wire_log.CL.raw_received == 0)
  = assert (SY.client_byte_reachable b);
    assert (SY.byte_pairing b);
    assert (b.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert (WFL.supported_client_config_wire_profile b.client.CS.cs_model.CS.model_config);
    // a client at HsServerFinishedVerified is pre-application-data, so SENT 0
    // protected records
    assert (WStep.pre_appdata_ctrl b.client.CS.cs_model.CS.model_control);
    WStep.lemma_client_preappdata_sent_no_appdata
      b.client.CS.cs_model.CS.model_config b.client;
    // byte pairing at Quiet: client.raw_sent == server.raw_received
    let cs = b.client.CS.cs_wire_log.CL.raw_sent in
    let sr = b.server.CS.cs_wire_log.CL.raw_received in
    assert (Seq.equal cs sr);
    WStep.lemma_raw_appdata_count_seq_equal cs sr
#pop-options

(* ================================================================== *)
(* SERVER-SIDE MESSAGE-FAITHFUL COUNT: SENT <= marker (pre-appdata).   *)
(*                                                                     *)
(* SOUNDNESS ARGUMENT (this is the fact that survived the coalesced-   *)
(* flight spec change, and WHY it survived):                           *)
(*                                                                     *)
(*  (3) `CS.protected_record_count` reads                              *)
(*        | CL.Sent, M.TlsApplicationData bytes -> ...                 *)
(*        | _, _                                -> 1                   *)
(*      so every `CL.Sent` HANDSHAKE message emits EXACTLY ONE          *)
(*      Application_data record.  The server's record count is          *)
(*      therefore message-faithful: records sent == flight markers set. *)
(*                                                                     *)
(*  (4) `CS.legal_protected_handshake_step` pins                        *)
(*        model.model_config.config_role == CS.ClientEndpoint          *)
(*      as its FIRST conjunct.  A server can therefore NEVER take a     *)
(*      `ConnProtectedHandshake` step, so the zero-byte TAIL path --    *)
(*      the path that de-synchronises records from messages on the      *)
(*      client -- is STRUCTURALLY UNAVAILABLE on the send side.         *)
(*                                                                     *)
(* IF EITHER (3) OR (4) EVER CHANGES -- if a `CL.Sent` handshake        *)
(* message comes to emit other than one record, or if a server is ever  *)
(* allowed to take a protected-handshake step -- THIS LEMMA DIES, and   *)
(* with it every server-side control exclusion below.                   *)
(*                                                                     *)
(* This is a strictly server-side statement: it mentions only the       *)
(* server's own reachability, control and wire log.  It does NOT route  *)
(* through the client and does NOT use byte-pairing.                    *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_preappdata_sent_le_marker
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            WStep.server_reachable (CS.initial cfg) server /\
            WStep.pre_appdata_ctrl server.CS.cs_model.CS.model_control /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures
            WStep.server_flight_shape server.CS.cs_model /\
            WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_sent
              <= WStep.server_sent_marker_count server.CS.cs_model)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    with
    (
      WStep.lemma_server_trace_sent_marker init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (WStep.server_sent_marker_count init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent sm_bytes);
      WStep.lemma_raw_appdata_count_serialize_all out_msgs;
      WStep.lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_sent sm_bytes
    )
#pop-options

(* ================================================================== *)
(* SERVER NOT PRE-FLIGHT: every `server_pre_flight_ctrl` control has   *)
(* all four flight markers unset, hence (by the message-faithful count *)
(* above) SENT == 0, contradicting SENT >= 1.                          *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_flip_server_not_pre_flight (b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv b /\ MP.Quiet? b.channel /\
        b.client.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified)
      (ensures
        ~(WStep.server_pre_flight_ctrl b.server.CS.cs_model.CS.model_control))
  = lemma_flip_server_sent_ge1 b;
    assert (SY.server_byte_reachable b);
    assert (b.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    introduce
      WStep.server_pre_flight_ctrl b.server.CS.cs_model.CS.model_control ==> False
    with
      lemma_server_preappdata_sent_le_marker
        b.server.CS.cs_model.CS.model_config b.server
#pop-options

(* ================================================================== *)
(* SERVER != HsClientHelloReceived, a non-ready-agreement exclusion.   *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_flip_server_not_client_hello_received (b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv b /\ MP.Quiet? b.channel /\
        b.client.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified)
      (ensures
        b.server.CS.cs_model.CS.model_control
          =!= CS.ControlHandshaking CS.HsClientHelloReceived)
  = // HsClientHelloReceived is a `server_pre_flight_ctrl` control.
    lemma_flip_server_not_pre_flight b
#pop-options

(* ================================================================== *)
(* SERVER RECEIVE FLOOR over S = post_cf \ ControlFailed.              *)
(* A reachable server whose control is in                             *)
(*   { HsClientFinishedReceived, HsClientFinishedVerified,            *)
(*     ControlApplicationData, ControlClosing, ControlClosed }         *)
(* has RECEIVED at least one ApplicationData record (the client        *)
(* Finished).  Keyed on the CONTROL set S (not the field, and not      *)
(* control-keyed on the strict CF 3-set): entering S from OUTSIDE      *)
(* requires the protected client-Finished receive, and moving WITHIN S *)
(* (…→Closing→Closed) keeps the flag up.  Mirrors the existing         *)
(* `server_cf_region_prior` telescoping.                              *)
(* ================================================================== *)

(** 1 iff the server control is in S = post_cf \ ControlFailed. **)
let server_s_flag (m:CS.connection_model) : nat =
  match m.CS.model_control with
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed -> 1
  | _ -> 0

#push-options "--fuel 2 --ifuel 5 --z3rlimit 60"
(** Per-step S-region LOWER fact: entering S from outside requires a protected
    ApplicationData receive (the client Finished); sends, local events and
    cleartext receives never raise the flag; leaving S (to ControlFailed) only
    lowers it. **)
let lemma_server_s_flag_step
  (m:CS.connection_model) (conn_ev:CS.conn_event)
  (m':CS.connection_model) (raw_sent raw_received:B.bytes)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        WStep.server_ctrl_ok m.CS.model_control /\
        CS.event_raw_delta_legal m conn_ev raw_sent raw_received)
      (ensures
        server_s_flag m'
          <= WStep.raw_appdata_count raw_received + server_s_flag m)
  = match conn_ev with
    | CS.ConnLocalEvent _ ->
      Seq.lemma_eq_elim raw_received B.empty;
      WStep.lemma_raw_appdata_count_empty ();
      WStep.lemma_raw_appdata_count_seq_equal raw_received B.empty
    (* A cleartext buffering step leaves [model_control] alone, so the flag is
       unchanged and the bound holds outright. *)
    | CS.ConnCleartextHandshake step ->
      assert_norm (CS.step_model m (CS.ConnCleartextHandshake step) ==
                   CS.step_cleartext_handshake m step);
      CS.lemma_step_cleartext_handshake_inert m step
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         Seq.lemma_eq_elim raw_received B.empty;
         WStep.lemma_raw_appdata_count_empty ();
         WStep.lemma_raw_appdata_count_seq_equal raw_received B.empty
       | CL.Received ->
         if CS.network_message_is_cleartext CL.Received dm.CL.message_value
         then WStep.lemma_received_cleartext_count_zero m dm.CL.message_value raw_received
         else
           (assert (CS.protected_record_count CL.Received dm.CL.message_value == 1);
            WStep.lemma_protected_raw_count_one raw_received))
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
(** Server-step S-region LOWER fact, lifted to `server_step`. **)
let lemma_server_step_s_flag
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        WStep.server_ctrl_ok st0.CS.cs_model.CS.model_control)
      (ensures
        server_s_flag st1.CS.cs_model
          <= WStep.list_appdata_count (WFSM.event_input_messages ev)
             + server_s_flag st0.CS.cs_model)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (ES.server_wire_received_event conn_ev /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection
           st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection
           st0.CS.cs_model conn_ev (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      with
      (
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        WStep.lemma_list_appdata_count_single_wire wire;
        lemma_server_s_flag_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent (CW.wire_serialize wire)
      )
    | SM.LocalEvent local ->
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_local_event_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta
           st0
           {
             CS.delta_event = conn_ev;
             CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty;
           }
           st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      with
        lemma_server_s_flag_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** Trace-level S-region LOWER telescoping. **)
let rec lemma_server_trace_s_flag
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            WStep.server_ctrl_ok st0.CS.cs_model.CS.model_control)
          (ensures
            server_s_flag st1.CS.cs_model
              <= WStep.list_appdata_count (WFSM.trace_input_messages trace)
                 + server_s_flag st0.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      WStep.lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_step_s_flag st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_s_flag init s' st1 rest;
      WStep.lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(** SERVER at a control in S ⇒ RECEIVED ≥ 1 ApplicationData record. **)
let lemma_server_S_received_ge1
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            WStep.server_reachable (CS.initial cfg) server /\
            server_s_flag server.CS.cs_model == 1 /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_received >= 1)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    with
    (
      lemma_server_trace_s_flag init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (server_s_flag init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      WStep.lemma_raw_appdata_count_serialize_all in_msgs;
      WStep.lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

(* ================================================================== *)
(* Some? hs_server_finished from SENT >= 4 in the pre-appdata region.  *)
(* SENT <= marker (pre-appdata) and marker <= 4 force marker == 4,     *)
(* hence all four flight fields — including hs_server_finished — set.  *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_preappdata_sent_ge4_finished
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            WStep.server_reachable (CS.initial cfg) server /\
            WStep.pre_appdata_ctrl server.CS.cs_model.CS.model_control /\
            WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_sent >= 4 /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_finished)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    with
    (
      WStep.lemma_server_trace_sent_marker init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (WStep.server_sent_marker_count init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent sm_bytes);
      WStep.lemma_raw_appdata_count_serialize_all out_msgs;
      WStep.lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_sent sm_bytes;
      // sent <= marker <= 4 and sent >= 4  ⇒  marker == 4  ⇒  hs_server_finished set
      assert (WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_sent
                <= WStep.server_sent_marker_count server.CS.cs_model)
    )
#pop-options

(* ================================================================== *)
(* THE EXACT-SFS PIN (under the explicit ControlFailed residual).      *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
(**
  Recover the server's control as EXACTLY `HsServerFinishedSent` at the
  deliver-to-client FLIP post-state, MODULO the TWO residuals the sanctioned
  record-counting method cannot discharge.

  Exclusions:
   * `server_stage_shape b.server`  — reachable-server control→field shape:
       kills every non-server control (`_ -> False`) and pins fields per control.
   * S-region floor + RECV = 0       — kills
       { HsClientFinishedReceived, HsClientFinishedVerified,
         ControlApplicationData, ControlClosing, ControlClosed }.
   * `~ControlFailed?`  (hypothesis)  — kills ControlFailed (RESIDUAL 1).
   * SENT >= 1 + the server-side message-faithful count — kills the four
       `server_pre_flight_ctrl` controls { ControlNew, HsAwaitingClientHello,
       HsClientHelloReceived, HsServerHelloSent }, all of which have marker 0
       and hence SENT == 0.
   * `~(HsServerEncryptedFlightSent)`  (hypothesis)  — RESIDUAL 2, NEW.

  ── RESIDUAL 2 IS NEW AND IS FORCED BY A SPEC CHANGE, NOT BY PROOF DEBT ──────
  `HsServerEncryptedFlightSent` used to be excluded by SENT >= 4 (the server
  there has `hs_server_finished == None`, so marker <= 3, so SENT <= 3).  That
  exclusion is GONE because the client-side `>= 4` it rested on is now FALSE:
  `CS.event_raw_delta_legal` charges a TAIL `CS.ConnProtectedHandshake` step
  `Seq.equal raw_received B.empty`, and `CS.legal_protected_handshake_step`
  places NO constraint tying `protected_handshake_fragment` to the bytes of the
  record the HEAD step was charged.  So a client can reach
  `HsServerFinishedVerified` after receiving a single record, against a server
  that has sent only its EncryptedExtensions.  Under the present model the
  conclusion WITHOUT residual 2 is not merely unproven, it is FALSE.

  Closing residual 2 needs a genuine record→message bridge on the client side
  (the `TLS13.ConnectionState.ProtectedWire*` round-trip), i.e. a client floor
  keyed on MESSAGES delivered rather than on records received.  It cannot be
  recovered by counting.
**)
let lemma_flip_recovers_server_sfs (b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv b /\ MP.Quiet? b.channel /\
        b.client.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        ~(CS.ControlFailed? b.server.CS.cs_model.CS.model_control) /\
        b.server.CS.cs_model.CS.model_control
          =!= CS.ControlHandshaking CS.HsServerEncryptedFlightSent)
      (ensures
        b.server.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedSent)
  = lemma_flip_server_sent_ge1 b;
    lemma_flip_server_not_pre_flight b;
    lemma_flip_server_recv_eq0 b;
    assert (SY.server_byte_reachable b);
    assert (b.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    assert (SMR.connection_state_consistent b.server);
    WStep.lemma_connection_state_consistent_server_stage_shape b.server;
    // RECV = 0 excludes the whole S region (a control in S would force RECV >= 1).
    introduce server_s_flag b.server.CS.cs_model == 1 ==> False
    with
      lemma_server_S_received_ge1
        b.server.CS.cs_model.CS.model_config b.server
#pop-options
