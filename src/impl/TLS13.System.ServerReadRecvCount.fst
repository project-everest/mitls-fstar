module TLS13.System.ServerReadRecvCount

(** STANDALONE SPIKE — the epoch/count bridge for `app_material_agreement`'s
    `client_send` case 3.  Target:
      `R.Application? (rd server).epoch ==> raw_appdata_count(received) >= 1`
    at ALL server controls (INCLUDING the closure controls `ControlClosing`/
    `Closed`/`Failed`, where the read epoch persists field-keyed but the existing
    control-keyed potential `server_cf_region_prior` collapses to 0).

    WHY NOT a pure epoch-keyed potential (the first, WRONG, instrument):
      `R.install_keys ... record_read R.Application` fires not only in the atomic
      client-Finished RECEIVE (`StateMachine.fst:774`, a protected/appdata-counted
      record) but also in the LOCAL event `LocalInstallTrafficKeysForRole
      (ServerEndpoint, TrafficApplication, TrafficRead)`, legal at
      `HsClientFinishedReceived` (`traffic_install_allowed_at_stage_for_role`,
      StateMachine.fst:1176; `legal_local_event` :1233; `install_record_keys_for_role`
      :418 -> :410).  That LOCAL install raises the read epoch with received-count
      delta 0, so a pure `app_read` potential is NOT bounded by the count.

    WHY NOT the control-keyed `server_cf_region_prior` alone: it is 1 only at
    {HsClientFinishedReceived, HsClientFinishedVerified, ControlApplicationData}
    and COLLAPSES to 0 at the closure controls, where `App(rd)` still holds.

    THE CORRECT INSTRUMENT is the MAX of the two:
      `server_recv_pot m = max (app_read_ind m) (server_cf_region_prior m)`.
    Monotone-increase-bounded-by-count:
      * `app_read_ind` catches the closure collapse (epoch is field-keyed, survives
        `fail_model` which preserves `model_record`);
      * `server_cf_region_prior = 1` at `HsClientFinishedReceived` catches the LOCAL
        app-read install (control unchanged there, so the potential is already 1).
    The only way the max jumps 0->1 is (a) the atomic Finished receive
    (appdata-counted, delta >= 1) or (b) entering the CF region, which the existing
    `lemma_server_cf_region_step` already shows requires an appdata-counted record. **)

module CS   = TLS13.Spec.StateMachine
module M    = TLS13.Messages
module CL   = TLS13.ConnectionLog
module B    = TLS13.Bytes
module Seq  = FStar.Seq
module R    = TLS13.Record.Spec
module SM   = Common.StateMachine
module CW   = TLS13.Spec.Endpoint.Wire
module CTy  = TLS13.Impl.CanonicalTypes
module EAPI = TLS13.Spec.Endpoint.API
module ES   = TLS13.Spec.Endpoint.Server
module WFSM = Common.WireFormatStateMachine
module WF   = Common.WireFormat
module WStep = TLS13.System.WireStep
module SMCan = TLS13.Spec.StateMachine.Canonical
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs

let app_read_ind (m:CS.connection_model) : nat =
  if R.Application? m.CS.model_record.CS.record_read.R.epoch then 1 else 0

let server_recv_pot (m:CS.connection_model) : nat =
  let a = app_read_ind m in
  let b = WStep.server_cf_region_prior m in
  if a >= b then a else b

(** PER-STEP (model level): the max potential's increase is bounded by the step's
    appdata RECV-delta count.  Reuses `lemma_server_cf_region_step` for the
    `server_cf_region_prior` half; the `app_read_ind` half needs the installer
    enumeration (only a protected receive or a local install at
    `HsClientFinishedReceived` raises the read epoch). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_server_recv_pot_step
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
        server_recv_pot m'
          <= WStep.raw_appdata_count raw_received + server_recv_pot m)
  = WStep.lemma_server_cf_region_step m conn_ev m' raw_sent raw_received
#pop-options

(** STEP-LEVEL (server_step): lifts the per-step bound over a `server_step`,
    extracting the underlying `conn_ev`/raw delta.  Mirrors
    `WStep.lemma_server_step_cf_region_lower`. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_step_recv_pot_lower
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
        server_recv_pot st1.CS.cs_model
          <= WStep.list_appdata_count (WFSM.event_input_messages ev)
             + server_recv_pot st0.CS.cs_model)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
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
      returns
        (server_recv_pot st1.CS.cs_model
          <= WStep.list_appdata_count (WFSM.event_input_messages ev)
             + server_recv_pot st0.CS.cs_model)
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs in
        WStep.lemma_list_appdata_count_single_wire wire;
        lemma_server_recv_pot_step
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
      returns
        (server_recv_pot st1.CS.cs_model
          <= WStep.list_appdata_count (WFSM.event_input_messages ev)
             + server_recv_pot st0.CS.cs_model)
      with _.
        lemma_server_recv_pot_step
          st0.CS.cs_model conn_ev st1.CS.cs_model raw_sent B.empty
#pop-options

(** TRACE-LEVEL telescoping.  Mirrors `WStep.lemma_server_trace_cf_region_lower`. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_server_trace_recv_pot_lower
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            WStep.server_ctrl_ok st0.CS.cs_model.CS.model_control)
          (ensures
            server_recv_pot st1.CS.cs_model
              <= WStep.list_appdata_count (WFSM.trace_input_messages trace)
                 + server_recv_pot st0.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      WStep.lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_step_recv_pot_lower st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_trace_recv_pot_lower init s' st1 rest;
      WStep.lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

(** ═══ THE BRIDGE — a reachable server whose application READ epoch is
    `Application` (at ANY control, including the closure controls) has RECEIVED at
    least one ApplicationData record (the client's protected Finished).  Mirrors
    `WStep.lemma_server_appdata_received_appdata`, but keyed on the read EPOCH
    (via the closure-robust `server_recv_pot`) rather than the appdata CONTROL. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_app_read_received_ge1
  (cfg:CS.connection_config)
  (server:CS.connection_state)
  : Lemma (requires
            WStep.server_reachable (CS.initial cfg) server /\
            R.Application? server.CS.cs_model.CS.model_record.CS.record_read.R.epoch /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_received >= 1)
  = let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_received >= 1
    with _.
    (
      lemma_server_trace_recv_pot_lower init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      WStep.lemma_raw_appdata_count_serialize_all in_msgs;
      WStep.lemma_raw_appdata_count_seq_equal server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options
