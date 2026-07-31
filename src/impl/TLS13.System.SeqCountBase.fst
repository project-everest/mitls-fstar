module TLS13.System.SeqCountBase

(**
  STAGE 2a — the per-endpoint handshake-region seq-counting invariant, as a
  STANDALONE module (NOT yet wired into `tls_system_inv`).

  Founds `H_seq` (sender.record_write.seq == receiver.record_read.seq) on the
  existing `byte_pairing`, via the counting invariants proved here.  See the
  the payoff `lemma_hseq_from_counts` (bottom of this file) for how these found H_seq.

  This file is being built incrementally; the pure per-endpoint delta lemmas come
  first, then the system-level lifting.
**)

module B     = TLS13.Bytes
module CL    = TLS13.ConnectionLog
module CS    = TLS13.Spec.StateMachine
module SMKM  = TLS13.Spec.StateMachine.KeyMaterial
module SMR   = TLS13.Spec.StateMachine.Reachability
module SMCan = TLS13.Spec.StateMachine.Canonical
module M     = TLS13.Messages
module R     = TLS13.Record.Spec
module Seq   = FStar.Seq
module T     = TLS13.Types
module CW    = TLS13.Spec.Endpoint.Wire
module WF    = Common.WireFormat
module WStep = TLS13.System.WireStep
module CSL   = TLS13.ConnectionState.Lemmas
module PC    = TLS13.System.ProgressCount
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module ES   = TLS13.Spec.Endpoint.Server
module EAPI = TLS13.Spec.Endpoint.API
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module SM    = Common.StateMachine
module WFSM  = Common.WireFormatStateMachine
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module CTy   = TLS13.Impl.CanonicalTypes
module RTC   = FStar.ReflexiveTransitiveClosure
module ID    = FStar.IndefiniteDescription
module W     = TLS13.Wire.Spec
module PNI   = TLS13.Impl.Driver.PairingNoTailInversion
module SWR   = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank
module WFL   = TLS13.Spec.WireFormatLemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(** WRITE-side handshake-region counting invariant (two clauses).

    GATED under `pre_appdata_control` — the same predicate that guards
    `client_len_ok`/`server_len_ok`.  A mid-handshake `Close_notify`/`fail_model`
    freezes `record_write` at `Handshake` while forcing one protected
    (ApplicationData) record onto the sent log, so the raw ungated clause is FALSE
    exactly at those close/fail exits (machine-checked counterexample).  Gating
    makes the clause active precisely on the honest pre-application-data region,
    where the seq/count pairing is genuinely maintained. **)
let pwrite_ok (st:CS.connection_state) : prop =
  PC.pre_appdata_control st.CS.cs_model.CS.model_control ==>
  ( (st.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
       st.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
         WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_sent) /\
    (st.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Initial ==>
       WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_sent == 0) )

(** READ-side handshake-region counting invariant (two clauses).  Gated exactly
    like `pwrite_ok`. **)
let pread_ok (st:CS.connection_state) : prop =
  PC.pre_appdata_control st.CS.cs_model.CS.model_control ==>
  ( (st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
       st.CS.cs_model.CS.model_record.CS.record_read.R.seq ==
         WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_received) /\
    (st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Initial ==>
       WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_received == 0) )

(** FORWARD-CLOSURE bridge (model level, lifted to `pre_appdata_control`): a legal
    delta cannot re-enter the pre-application-data region once it has left it, so
    a post-state that is still pre-application-data forces the pre-state to be as
    well.  This UNLOCKS the (gated) hypothesis `pwrite_ok`/`pread_ok st0` whenever
    the (gated) goal at `st1` is active.  Contrapositive of
    `WStep.lemma_step_notpreappdata_stable`; the two `pre_appdata` predicates are
    byte-identical definitions in `PC` and `WStep`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_pre_appdata_back
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  : Lemma
      (requires CS.legal_connection_delta st0 d st1)
      (ensures
        PC.pre_appdata_control st1.CS.cs_model.CS.model_control ==>
        PC.pre_appdata_control st0.CS.cs_model.CS.model_control)
  = if PC.pre_appdata_control st0.CS.cs_model.CS.model_control
    then ()
    else begin
      assert (PC.pre_appdata_control st0.CS.cs_model.CS.model_control ==
              WStep.pre_appdata_ctrl st0.CS.cs_model.CS.model_control);
      WStep.lemma_step_notpreappdata_stable
        st0.CS.cs_model d.CS.delta_event st1.CS.cs_model;
      assert (PC.pre_appdata_control st1.CS.cs_model.CS.model_control ==
              WStep.pre_appdata_ctrl st1.CS.cs_model.CS.model_control)
    end
#pop-options

(** Per-connection-state pair conjunct over both endpoints. **)
let seq_count_ok_pair (client server:CS.connection_state) : prop =
  pwrite_ok client /\ pread_ok client /\ pwrite_ok server /\ pread_ok server

(** ─────────────────────────────────────────────────────────────────────────
    PROBE 1 — RECEIVED network event preserves `pwrite_ok`.

    Every `Received` network event modifies only `record_read`; `record_write`
    and `raw_sent` are untouched (delta sent bytes empty).  So `pwrite_ok`
    transports trivially.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pwrite_received
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msg:M.tls_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        d.CS.delta_event == SMKM.received_tls_event msg /\
        pwrite_ok st0)
      (ensures pwrite_ok st1)
  = assert (CS.event_raw_delta_legal st0.CS.cs_model d.CS.delta_event
              d.CS.delta_raw_sent d.CS.delta_raw_received);
    assert (Seq.equal d.CS.delta_raw_sent B.empty);
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent);
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent;
    assert (st1.CS.cs_model.CS.model_record.CS.record_write ==
            st0.CS.cs_model.CS.model_record.CS.record_write);
    // control may change (received event): unlock pwrite_ok st0 whenever the gated
    // goal at st1 is active, via forward-closure of pre_appdata_control.
    lemma_pre_appdata_back st0 d st1
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    COUNTING-ALGEBRA CORE (write side).

    `pwrite_ok` is preserved by any legal delta, GIVEN three per-event facts that
    isolate exactly what a discharger must prove:

      P_seqdelta  : if the write epoch stays Handshake across the step, the write
                    seq rises by exactly the appdata-record count of the sent
                    byte-delta   (the counting crux — protected sends +1/+1;
                    non-write events +0/+0).
      P_installHS : if the step ENTERS the Handshake write epoch (a key install),
                    the new seq is 0 and no appdata has been sent yet
                    (the region fact: `raw_appdata_count(raw_sent)==0`).
      P_initial   : if the step is at the Initial write epoch, no appdata sent.

    The append law `lemma_raw_appdata_count_append` (needing the sent log to parse
    cleanly into records — supplied by `client/server_byte_reachable`) transports
    the count across the wire-log append.  Everything else is pure arithmetic.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40 --split_queries always"
let lemma_pwrite_algebra
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msgs:list CW.wire_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        pwrite_ok st0 /\
        WF.parses_as CW.tls_record_wire_format
          st0.CS.cs_wire_log.CL.raw_sent msgs Seq.empty /\
        // P_seqdelta (gated on the goal being active at st1):
        (PC.pre_appdata_control st1.CS.cs_model.CS.model_control /\
         st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         st1.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
         st1.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
           st0.CS.cs_model.CS.model_record.CS.record_write.R.seq +
           WStep.raw_appdata_count d.CS.delta_raw_sent) /\
        // P_installHS (gated):
        (PC.pre_appdata_control st1.CS.cs_model.CS.model_control /\
         st1.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         ~(st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake) ==>
         st1.CS.cs_model.CS.model_record.CS.record_write.R.seq == 0 /\
         WStep.raw_appdata_count st1.CS.cs_wire_log.CL.raw_sent == 0) /\
        // P_initial (gated):
        (PC.pre_appdata_control st1.CS.cs_model.CS.model_control /\
         st1.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Initial ==>
         WStep.raw_appdata_count st1.CS.cs_wire_log.CL.raw_sent == 0))
      (ensures pwrite_ok st1)
  = // st1.raw_sent == st0.raw_sent ++ d.delta_raw_sent (from legal_connection_delta)
    WStep.lemma_raw_appdata_count_append
      st0.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent msgs;
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent);
    // whenever the gated goal at st1 is active, pwrite_ok st0 is unlocked.
    lemma_pre_appdata_back st0 d st1
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    SENT network event preserves `pread_ok` (read side untouched).
    Mirror of `lemma_pwrite_received`: a Sent event modifies only `record_write`
    and `raw_sent`; `record_read` and `raw_received` are unchanged.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pread_sent
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msg:M.tls_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        d.CS.delta_event == SMKM.sent_tls_event msg /\
        pread_ok st0)
      (ensures pread_ok st1)
  = assert (CS.event_raw_delta_legal st0.CS.cs_model d.CS.delta_event
              d.CS.delta_raw_sent d.CS.delta_raw_received);
    assert (Seq.equal d.CS.delta_raw_received B.empty);
    assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received
                      st0.CS.cs_wire_log.CL.raw_received);
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received;
    assert (st1.CS.cs_model.CS.model_record.CS.record_read ==
            st0.CS.cs_model.CS.model_record.CS.record_read);
    lemma_pre_appdata_back st0 d st1
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    COUNTING-ALGEBRA CORE (read side) — mirror of `lemma_pwrite_algebra`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40 --split_queries always"
let lemma_pread_algebra
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msgs:list CW.wire_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        pread_ok st0 /\
        WF.parses_as CW.tls_record_wire_format
          st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty /\
        // P_seqdelta (gated):
        (PC.pre_appdata_control st1.CS.cs_model.CS.model_control /\
         st0.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         st1.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
         st1.CS.cs_model.CS.model_record.CS.record_read.R.seq ==
           st0.CS.cs_model.CS.model_record.CS.record_read.R.seq +
           WStep.raw_appdata_count d.CS.delta_raw_received) /\
        // P_installHS (gated):
        (PC.pre_appdata_control st1.CS.cs_model.CS.model_control /\
         st1.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         ~(st0.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake) ==>
         st1.CS.cs_model.CS.model_record.CS.record_read.R.seq == 0 /\
         WStep.raw_appdata_count st1.CS.cs_wire_log.CL.raw_received == 0) /\
        // P_initial (gated):
        (PC.pre_appdata_control st1.CS.cs_model.CS.model_control /\
         st1.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Initial ==>
         WStep.raw_appdata_count st1.CS.cs_wire_log.CL.raw_received == 0))
      (ensures pread_ok st1)
  = WStep.lemma_raw_appdata_count_append
      st0.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received msgs;
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received);
    lemma_pre_appdata_back st0 d st1
#pop-options


(** ─────────────────────────────────────────────────────────────────────────
    SERVER REACHABLE PARSES — the server analogues of
    `WStep.lemma_client_reachable_raw_sent_parses` / `_raw_received_parses`.
    A reachable server's outgoing / incoming byte log cleanly decomposes into a
    wire-record list (the append witness for `lemma_raw_appdata_count_append`).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_raw_sent_parses
  (cfg:CS.connection_config) (server:CS.connection_state)
  : Lemma (requires
            WStep.server_reachable (CS.initial cfg) server /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures
            (exists (msgs:list CW.wire_message).
              WF.parses_as CW.tls_record_wire_format
                server.CS.cs_wire_log.CL.raw_sent msgs Seq.empty))
  = let init = CS.initial cfg in
    let sm = ES.server_state_machine init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns
      (exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_sent msgs Seq.empty)
    with _.
    (
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let out_msgs = SM.trace_wire_outputs trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format out_msgs in
      assert (init.CS.cs_wire_log.CL.raw_sent == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_sent sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent sm_bytes);
      Seq.lemma_eq_elim server.CS.cs_wire_log.CL.raw_sent sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse out_msgs;
      introduce exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
      with out_msgs and ()
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_raw_received_parses
  (cfg:CS.connection_config) (server:CS.connection_state)
  : Lemma (requires
            WStep.server_reachable (CS.initial cfg) server /\
            cfg.CS.config_role == CS.ServerEndpoint)
          (ensures
            (exists (msgs:list CW.wire_message).
              WF.parses_as CW.tls_record_wire_format
                server.CS.cs_wire_log.CL.raw_received msgs Seq.empty))
  = let init = CS.initial cfg in
    let sm = ES.server_state_machine init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns
      (exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_received msgs Seq.empty)
    with _.
    (
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      Seq.lemma_eq_elim server.CS.cs_wire_log.CL.raw_received sm_bytes;
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      introduce exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          server.CS.cs_wire_log.CL.raw_received msgs Seq.empty
      with in_msgs and ()
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    KEY/EPOCH COUPLING (record layer).  On reachable states, a record direction
    is at the `Initial` epoch iff it has no key installed: `install_keys` always
    sets a non-`Initial` epoch together with a key, `next_seq`/`advance` preserve
    both, and every other step leaves the record untouched.  Used to exclude a
    protected server send at an `Initial` write epoch (the seal projection forces
    a key, hence a non-`Initial` epoch).
    ───────────────────────────────────────────────────────────────────────── **)
let record_key_epoch_coupling (m:CS.connection_model) : prop =
  (m.CS.model_record.CS.record_write.R.epoch == R.Initial ==>
     m.CS.model_record.CS.record_write.R.key == None) /\
  (m.CS.model_record.CS.record_read.R.epoch == R.Initial ==>
     m.CS.model_record.CS.record_read.R.key == None)

let rec lemma_advance_preserves_key_epoch (st:R.direction_state) (n:nat)
  : Lemma (ensures (CS.advance_direction_records st n).R.key == st.R.key /\
                   (CS.advance_direction_records st n).R.epoch == st.R.epoch)
          (decreases n)
          [SMTPat (CS.advance_direction_records st n)]
  = if n = 0 then () else lemma_advance_preserves_key_epoch st (n - 1)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_record_key_epoch_coupling
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        record_key_epoch_coupling m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures record_key_epoch_coupling m')
  = ()
#pop-options

let lemma_delta_record_key_epoch_coupling
  (st0 st1:CS.connection_state)
  : Lemma
      (requires
        record_key_epoch_coupling st0.CS.cs_model /\
        SMR.connection_state_single_step st0 st1)
      (ensures record_key_epoch_coupling st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_record_key_epoch_coupling
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_single_step_record_key_epoch_coupling ()
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (record_key_epoch_coupling y.CS.cs_model);
                     (SMR.connection_state_single_step x y)}
          record_key_epoch_coupling x.CS.cs_model /\
          SMR.connection_state_single_step x y ==>
          record_key_epoch_coupling y.CS.cs_model)
  = introduce forall x y.
      record_key_epoch_coupling x.CS.cs_model /\
      SMR.connection_state_single_step x y ==>
      record_key_epoch_coupling y.CS.cs_model
    with
      introduce _ ==> _ with _.
      lemma_delta_record_key_epoch_coupling x y

let lemma_consistent_record_key_epoch_coupling
  (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures record_key_epoch_coupling st.CS.cs_model)
  = let p (st:CS.connection_state) = record_key_epoch_coupling st.CS.cs_model in
    lemma_single_step_record_key_epoch_coupling ();
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure
      SMR.connection_state_single_step
      p
      stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(** ─────────────────────────────────────────────────────────────────────────
    RECORD/KEY-SCHEDULE COUPLING (handshake epoch).  On reachable states, a
    record direction is at the `Handshake` epoch only once the corresponding
    handshake-traffic key-schedule slot is populated.  A handshake key install
    sets BOTH the record epoch (`Handshake`) and the matching schedule slot;
    `next_seq`/`advance` preserve the epoch and never touch the schedule; and no
    step ever clears a schedule slot.  Part of the record/schedule coupling used
    by the reachable seq-count preservation argument (the redundant handshake key
    re-install is handled by the count==0-at-install-stage reachability facts, not
    by any progress guard).
    ───────────────────────────────────────────────────────────────────────── **)
let hs_traffic_slot
  (keys:CS.key_schedule_state) (label:CS.traffic_label)
  : option CS.traffic_key_material =
  match label with
  | CS.ClientTraffic -> keys.CS.ks_client_handshake_traffic
  | CS.ServerTraffic -> keys.CS.ks_server_handshake_traffic

let record_schedule_coupling (m:CS.connection_model) : prop =
  let role = m.CS.model_config.CS.config_role in
  let keys = m.CS.model_handshake.CS.hs_keys in
  (m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
     Some? (hs_traffic_slot keys
             (CS.traffic_label_for_endpoint_direction role CS.TrafficWrite))) /\
  (m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
     Some? (hs_traffic_slot keys
             (CS.traffic_label_for_endpoint_direction role CS.TrafficRead)))

#push-options "--fuel 4 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_step_record_schedule_coupling
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        record_schedule_coupling m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures record_schedule_coupling m')
  = match ev with
    | CS.ConnNetworkEvent _ -> ()
    | CS.ConnProtectedHandshake _ -> ()
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalInstallTrafficKeys install -> ()
       | CS.LocalInstallTrafficKeysForRole role_install -> ()
       | _ -> ())
#pop-options

let lemma_delta_record_schedule_coupling
  (st0 st1:CS.connection_state)
  : Lemma
      (requires
        record_schedule_coupling st0.CS.cs_model /\
        SMR.connection_state_single_step st0 st1)
      (ensures record_schedule_coupling st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_record_schedule_coupling
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_single_step_record_schedule_coupling ()
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (record_schedule_coupling y.CS.cs_model);
                     (SMR.connection_state_single_step x y)}
          record_schedule_coupling x.CS.cs_model /\
          SMR.connection_state_single_step x y ==>
          record_schedule_coupling y.CS.cs_model)
  = introduce forall x y.
      record_schedule_coupling x.CS.cs_model /\
      SMR.connection_state_single_step x y ==>
      record_schedule_coupling y.CS.cs_model
    with
      introduce _ ==> _ with _.
      lemma_delta_record_schedule_coupling x y

let lemma_consistent_record_schedule_coupling
  (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures record_schedule_coupling st.CS.cs_model)
  = let p (st:CS.connection_state) = record_schedule_coupling st.CS.cs_model in
    lemma_single_step_record_schedule_coupling ();
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure
      SMR.connection_state_single_step
      p
      stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(** ─────────────────────────────────────────────────────────────────────────
    MODEL FACTS for a SENT network event (write side).  Under the gated
    pre-application-data region, a Sent event's write-record seq rises by exactly
    the appdata count of the sent byte-delta; it never installs handshake write
    keys; and at the Initial write epoch it emits no appdata (cleartext hellos /
    ChangeCipherSpec).  Protected sends at an Initial write epoch are excluded by
    the seal projection + key/epoch coupling (a seal forces a key, hence a
    non-Initial epoch).  The two cleartext-hello count-0 facts are supplied by the
    caller from reachability (ServerHello wire bound / ClientHello wire profile).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_sent_write_model_facts
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.legal_event m (SMKM.sent_tls_event msg) /\
        CS.step_model m (SMKM.sent_tls_event msg) == Some m' /\
        CS.event_raw_delta_legal m (SMKM.sent_tls_event msg) rs rr /\
        record_key_epoch_coupling m /\
        SMCan.sent_event_nonempty_seal_projection m (SMKM.sent_tls_event msg) rs /\
        ((M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) ==>
           WStep.raw_appdata_count rs == 0) /\
        ((M.TlsHandshake? msg /\ M.ClientHello? (M.TlsHandshake?._0 msg)) ==>
           WStep.raw_appdata_count rs == 0))
      (ensures
        (let w0 = m.CS.model_record.CS.record_write in
         let w1 = m'.CS.model_record.CS.record_write in
         (PC.pre_appdata_control m'.CS.model_control /\
          w0.R.epoch == R.Handshake /\ w1.R.epoch == R.Handshake ==>
            w1.R.seq == w0.R.seq + WStep.raw_appdata_count rs) /\
         (PC.pre_appdata_control m'.CS.model_control /\
          w1.R.epoch == R.Handshake ==> w0.R.epoch == R.Handshake) /\
         (PC.pre_appdata_control m'.CS.model_control /\
          w1.R.epoch == R.Initial ==> w0.R.epoch == R.Initial) /\
         (PC.pre_appdata_control m'.CS.model_control /\
          w1.R.epoch == R.Initial ==> WStep.raw_appdata_count rs == 0)))
  = match msg with
    | M.TlsChangeCipherSpec ->
      WStep.lemma_cleartext_raw_count_zero msg rs
    | M.TlsHandshake (M.EncryptedExtensions _)
    | M.TlsHandshake (M.Certificate _)
    | M.TlsHandshake (M.CertificateVerify _)
    | M.TlsHandshake (M.Finished _) ->
      WStep.lemma_protected_raw_count_one rs;
      // protected ⟹ seal Some ⟹ write key Some ⟹ (coupling) write epoch ≠ Initial.
      assert (CS.raw_records_exactly rs T.Application_data 1);
      assert (B.length rs > 0);
      assert (SMCan.sent_event_seal_projection m (SMKM.sent_tls_event msg) rs);
      assert (SMCan.sent_single_protected_message_seal m msg rs);
      assert (Some? m.CS.model_record.CS.record_write.R.key)
    | _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    MODEL FACTS for a RECEIVED network event (read side).  Mirror of
    `lemma_sent_write_model_facts`.  A received protected record advances the read
    seq by one (count 1); a received cleartext record (ClientHello / ServerHello /
    HelloRetryRequest / ChangeCipherSpec) has count 0.  Protected receives at an
    Initial read epoch are excluded by the decode projection + key/epoch coupling
    (an open forces a read key, hence a non-Initial epoch).  The ServerHello wire
    bound is supplied by the caller from reachability.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_recv_read_model_facts
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.legal_event m (SMKM.received_tls_event msg) /\
        CS.step_model m (SMKM.received_tls_event msg) == Some m' /\
        CS.event_raw_delta_legal m (SMKM.received_tls_event msg) rs rr /\
        record_key_epoch_coupling m /\
        SMCan.received_event_nonempty_decode_projection m (SMKM.received_tls_event msg) rr /\
        ((M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) ==>
           B.length (W.serialize_handshake (M.ServerHello (M.ServerHello?._0 (M.TlsHandshake?._0 msg)))) <= 16640))
      (ensures
        (let r0 = m.CS.model_record.CS.record_read in
         let r1 = m'.CS.model_record.CS.record_read in
         (PC.pre_appdata_control m'.CS.model_control /\
          r0.R.epoch == R.Handshake /\ r1.R.epoch == R.Handshake ==>
            r1.R.seq == r0.R.seq + WStep.raw_appdata_count rr) /\
         (PC.pre_appdata_control m'.CS.model_control /\
          r1.R.epoch == R.Handshake ==> r0.R.epoch == R.Handshake) /\
         (PC.pre_appdata_control m'.CS.model_control /\
          r1.R.epoch == R.Initial ==> r0.R.epoch == R.Initial) /\
         (PC.pre_appdata_control m'.CS.model_control /\
          r1.R.epoch == R.Initial ==> WStep.raw_appdata_count rr == 0)))
  = match msg with
    | M.TlsChangeCipherSpec ->
      WStep.lemma_received_cleartext_count_zero msg rr
    | M.TlsHandshake (M.ClientHello _) ->
      WStep.lemma_received_cleartext_count_zero msg rr
    | M.TlsHandshake (M.ServerHello _) ->
      WStep.lemma_received_cleartext_count_zero msg rr
    | M.TlsHandshake M.HelloRetryRequest ->
      WStep.lemma_received_cleartext_count_zero msg rr
    | M.TlsHandshake (M.EncryptedExtensions _)
    | M.TlsHandshake (M.Certificate _)
    | M.TlsHandshake (M.CertificateVerify _)
    | M.TlsHandshake (M.Finished _) ->
      WStep.lemma_protected_raw_count_one rr;
      assert (CS.raw_records_exactly rr T.Application_data 1);
      assert (B.length rr > 0);
      assert (SMCan.received_event_decode_projection m (SMKM.received_tls_event msg) rr);
      assert (SMCan.received_single_protected_message_decode m msg rr);
      assert (Some? m.CS.model_record.CS.record_read.R.key)
    | _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    SMALL BRIDGES for the per-transition helpers.
    ───────────────────────────────────────────────────────────────────────── **)

(** A wire record serialises to a non-empty byte string. **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_wire_serialize_nonempty (w:CW.wire_message)
  : Lemma (B.length (CW.wire_serialize w) > 0)
  = W.lemma_parse_record_wire_some_consumed_positive
      w.CW.wm_raw w.CW.wm_content_type w.CW.wm_fragment (B.length w.CW.wm_raw)
#pop-options

(** With a legal raw delta, a non-empty SENT byte-delta forces a Sent network
    event (a ConnLocalEvent / Received event has an empty sent byte-delta). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_nonempty_sent_event
  (m:CS.connection_model) (ev:CS.conn_event) (rs rr:B.bytes)
  : Lemma
      (requires CS.event_raw_delta_legal m ev rs rr /\ B.length rs > 0)
      (ensures (exists (msg:M.tls_message). ev == SMKM.sent_tls_event msg))
  = match ev with
    | CS.ConnLocalEvent _ -> ()
    | CS.ConnProtectedHandshake _ -> ()
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         introduce exists (msg:M.tls_message). ev == SMKM.sent_tls_event msg
         with dm.CL.message_value
         and ()
       | CL.Received -> ())
#pop-options



(** ─────────────────────────────────────────────────────────────────────────
    PER-TRANSITION HELPER : server SEND.
    ───────────────────────────────────────────────────────────────────────── **)

(** A Sent ClientHello is only legal at the client-only `HsStarted` stage; the
    server (whose `server_stage_ok` excludes that stage) therefore never sends
    one — used to discharge the ClientHello arm vacuously. **)
#push-options "--fuel 4 --ifuel 6 --z3rlimit 40"
let lemma_sent_client_hello_forces_hsstarted
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        (M.TlsHandshake? msg /\ M.ClientHello? (M.TlsHandshake?._0 msg)) /\
        CS.step_model m (SMKM.sent_tls_event msg) == Some m')
      (ensures m.CS.model_control == CS.ControlHandshaking CS.HsStarted)
  = ()
#pop-options

(** A Sent ServerHello stores itself in `hs_server_hello`. **)
#push-options "--fuel 4 --ifuel 6 --z3rlimit 40"
let lemma_sent_server_hello_stored
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        (M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) /\
        CS.step_model m (SMKM.sent_tls_event msg) == Some m')
      (ensures m'.CS.model_handshake.CS.hs_server_hello ==
               Some (M.ServerHello?._0 (M.TlsHandshake?._0 msg)))
  = ()
#pop-options

(** A Received ServerHello stores itself in `hs_server_hello`. **)
#push-options "--fuel 4 --ifuel 6 --z3rlimit 40"
let lemma_recv_server_hello_stored
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        (M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) /\
        CS.step_model m (SMKM.received_tls_event msg) == Some m')
      (ensures m'.CS.model_handshake.CS.hs_server_hello ==
               Some (M.ServerHello?._0 (M.TlsHandshake?._0 msg)))
  = ()
#pop-options


(** ─────────────────────────────────────────────────────────────────────────
    LOCAL record-seq stability (client / server).  A LOCAL step changes the
    record ONLY via a key install (all other locals leave `model_record` fixed).
    The only install that resets a direction `seq` while KEEPING that direction's
    epoch at `Handshake` is a REDUNDANT idempotent handshake re-install
    (`R.install_keys` unconditionally resets seq to 0).  Such a re-install
    preserves the seq exactly when the pre-install seq was already 0.  The GATE
    predicates below capture that per-direction premise; they are TRUE at every
    reachable install stage — where the direction's appdata count (hence, via
    `pwrite_ok`/`pread_ok`, its seq) is 0 — and are discharged there by
    `lemma_discharge_local_redundant_{client,server}`.  The genuine
    (epoch-changing) `Initial -> Handshake` install has the "both epochs Handshake"
    antecedent false, so it is vacuous; every non-install local leaves the record
    fixed, so the gate is vacuously `True`.
    ───────────────────────────────────────────────────────────────────────── **)

(** WRITE-direction gate: a redundant handshake WRITE re-install preserves the
    write seq (its pre-install write seq is 0). **)
let install_write_seq_zero
  (m:CS.connection_model) (install:CS.traffic_key_install) : prop =
  install.CS.install_epoch == CS.TrafficHandshake /\
  install.CS.install_direction == CS.TrafficWrite /\
  m.CS.model_record.CS.record_write.R.epoch == R.Handshake
  ==> m.CS.model_record.CS.record_write.R.seq == 0

(** READ-direction gate: mirror of `install_write_seq_zero`. **)
let install_read_seq_zero
  (m:CS.connection_model) (install:CS.traffic_key_install) : prop =
  install.CS.install_epoch == CS.TrafficHandshake /\
  install.CS.install_direction == CS.TrafficRead /\
  m.CS.model_record.CS.record_read.R.epoch == R.Handshake
  ==> m.CS.model_record.CS.record_read.R.seq == 0

(** The WRITE gate lifted to a whole local event (vacuous on non-install locals). **)
let local_write_seq_zero
  (m:CS.connection_model) (local:CS.local_event) : prop =
  match local with
  | CS.LocalInstallTrafficKeys install -> install_write_seq_zero m install
  | CS.LocalInstallTrafficKeysForRole ri -> install_write_seq_zero m ri.CS.install_payload
  | _ -> True

(** The READ gate lifted to a whole local event. **)
let local_read_seq_zero
  (m:CS.connection_model) (local:CS.local_event) : prop =
  match local with
  | CS.LocalInstallTrafficKeys install -> install_read_seq_zero m install
  | CS.LocalInstallTrafficKeysForRole ri -> install_read_seq_zero m ri.CS.install_payload
  | _ -> True

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_install_seq_stable_write
  (m:CS.connection_model) (install:CS.traffic_key_install) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_schedule_coupling m /\
        CS.ControlHandshaking? m.CS.model_control /\
        install_write_seq_zero m install /\
        m' == { m with
                  CS.model_record = CS.install_record_keys m.CS.model_record install;
                  CS.model_handshake =
                    { m.CS.model_handshake with
                        CS.hs_keys =
                          CS.update_key_schedule_with_install
                            m.CS.model_handshake.CS.hs_keys install } })
      (ensures
        (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_write.R.seq
           == m.CS.model_record.CS.record_write.R.seq))
  = introduce (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
               m.CS.model_record.CS.record_write.R.epoch == R.Handshake)
              ==> m'.CS.model_record.CS.record_write.R.seq
                    == m.CS.model_record.CS.record_write.R.seq
    with _pf.
      (match install.CS.install_epoch, install.CS.install_direction with
       | CS.TrafficHandshake, CS.TrafficWrite -> ()
       | _, _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_install_seq_stable_read
  (m:CS.connection_model) (install:CS.traffic_key_install) (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_schedule_coupling m /\
        CS.ControlHandshaking? m.CS.model_control /\
        install_read_seq_zero m install /\
        m' == { m with
                  CS.model_record = CS.install_record_keys m.CS.model_record install;
                  CS.model_handshake =
                    { m.CS.model_handshake with
                        CS.hs_keys =
                          CS.update_key_schedule_with_install
                            m.CS.model_handshake.CS.hs_keys install } })
      (ensures
        (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_read.R.seq
           == m.CS.model_record.CS.record_read.R.seq))
  = introduce (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
               m.CS.model_record.CS.record_read.R.epoch == R.Handshake)
              ==> m'.CS.model_record.CS.record_read.R.seq
                    == m.CS.model_record.CS.record_read.R.seq
    with _pf.
      (match install.CS.install_epoch, install.CS.install_direction with
       | CS.TrafficHandshake, CS.TrafficRead -> ()
       | _, _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_install_for_role_seq_stable_write
  (m:CS.connection_model) (role_install:CS.role_traffic_key_install)
  (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        role_install.CS.install_role == CS.ClientEndpoint /\
        record_schedule_coupling m /\
        CS.ControlHandshaking? m.CS.model_control /\
        install_write_seq_zero m role_install.CS.install_payload /\
        m' == { m with
                  CS.model_record =
                    CS.install_record_keys_for_role
                      role_install.CS.install_role
                      m.CS.model_record role_install.CS.install_payload;
                  CS.model_handshake =
                    { m.CS.model_handshake with
                        CS.hs_keys =
                          CS.update_key_schedule_with_install_for_role
                            role_install.CS.install_role
                            m.CS.model_handshake.CS.hs_keys
                            role_install.CS.install_payload } })
      (ensures
        (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_write.R.seq
           == m.CS.model_record.CS.record_write.R.seq))
  = lemma_client_local_install_seq_stable_write m role_install.CS.install_payload m'
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_install_for_role_seq_stable_read
  (m:CS.connection_model) (role_install:CS.role_traffic_key_install)
  (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        role_install.CS.install_role == CS.ClientEndpoint /\
        record_schedule_coupling m /\
        CS.ControlHandshaking? m.CS.model_control /\
        install_read_seq_zero m role_install.CS.install_payload /\
        m' == { m with
                  CS.model_record =
                    CS.install_record_keys_for_role
                      role_install.CS.install_role
                      m.CS.model_record role_install.CS.install_payload;
                  CS.model_handshake =
                    { m.CS.model_handshake with
                        CS.hs_keys =
                          CS.update_key_schedule_with_install_for_role
                            role_install.CS.install_role
                            m.CS.model_handshake.CS.hs_keys
                            role_install.CS.install_payload } })
      (ensures
        (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_read.R.seq
           == m.CS.model_record.CS.record_read.R.seq))
  = lemma_client_local_install_seq_stable_read m role_install.CS.install_payload m'
#pop-options

(** Client LOCAL record-seq stability (dispatch on the local event).  Only the two
    key-install locals touch `model_record`; everything else leaves it fixed. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_record_seq_stable_write
  (m:CS.connection_model) (local:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_local_event m local /\
        CS.step_local_event m local == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_schedule_coupling m /\
        local_write_seq_zero m local)
      (ensures
        (PC.pre_appdata_control m'.CS.model_control /\
         m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_write.R.seq
           == m.CS.model_record.CS.record_write.R.seq))
  = match local with
    | CS.LocalInstallTrafficKeys install ->
      lemma_client_local_install_seq_stable_write m install m'
    | CS.LocalInstallTrafficKeysForRole role_install ->
      lemma_client_local_install_for_role_seq_stable_write m role_install m'
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_record_seq_stable_read
  (m:CS.connection_model) (local:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_local_event m local /\
        CS.step_local_event m local == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_schedule_coupling m /\
        local_read_seq_zero m local)
      (ensures
        (PC.pre_appdata_control m'.CS.model_control /\
         m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_read.R.seq
           == m.CS.model_record.CS.record_read.R.seq))
  = match local with
    | CS.LocalInstallTrafficKeys install ->
      lemma_client_local_install_seq_stable_read m install m'
    | CS.LocalInstallTrafficKeysForRole role_install ->
      lemma_client_local_install_for_role_seq_stable_read m role_install m'
    | _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    LOCAL record-seq stability (server).  A server installs traffic keys via
    `LocalInstallTrafficKeysForRole` with `install_role == ServerEndpoint`.  The
    `(ServerEndpoint,TrafficApplication,TrafficWrite)` install moves the write
    epoch to `Application` (so the `Handshake` antecedent is vacuous); the handshake
    installs are excluded from resetting a `Handshake` seq by the gate.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_install_for_role_seq_stable_write
  (m:CS.connection_model) (role_install:CS.role_traffic_key_install)
  (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        role_install.CS.install_role == CS.ServerEndpoint /\
        record_schedule_coupling m /\
        CS.ControlHandshaking? m.CS.model_control /\
        install_write_seq_zero m role_install.CS.install_payload /\
        m' == { m with
                  CS.model_record =
                    CS.install_record_keys_for_role
                      role_install.CS.install_role
                      m.CS.model_record role_install.CS.install_payload;
                  CS.model_handshake =
                    { m.CS.model_handshake with
                        CS.hs_keys =
                          CS.update_key_schedule_with_install_for_role
                            role_install.CS.install_role
                            m.CS.model_handshake.CS.hs_keys
                            role_install.CS.install_payload } })
      (ensures
        (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_write.R.seq
           == m.CS.model_record.CS.record_write.R.seq))
  = introduce (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
               m.CS.model_record.CS.record_write.R.epoch == R.Handshake)
              ==> m'.CS.model_record.CS.record_write.R.seq
                    == m.CS.model_record.CS.record_write.R.seq
    with _pf.
      (match role_install.CS.install_payload.CS.install_epoch,
             role_install.CS.install_payload.CS.install_direction with
       | CS.TrafficHandshake, CS.TrafficWrite -> ()
       | _, _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_install_for_role_seq_stable_read
  (m:CS.connection_model) (role_install:CS.role_traffic_key_install)
  (m':CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        role_install.CS.install_role == CS.ServerEndpoint /\
        record_schedule_coupling m /\
        CS.ControlHandshaking? m.CS.model_control /\
        install_read_seq_zero m role_install.CS.install_payload /\
        m' == { m with
                  CS.model_record =
                    CS.install_record_keys_for_role
                      role_install.CS.install_role
                      m.CS.model_record role_install.CS.install_payload;
                  CS.model_handshake =
                    { m.CS.model_handshake with
                        CS.hs_keys =
                          CS.update_key_schedule_with_install_for_role
                            role_install.CS.install_role
                            m.CS.model_handshake.CS.hs_keys
                            role_install.CS.install_payload } })
      (ensures
        (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_read.R.seq
           == m.CS.model_record.CS.record_read.R.seq))
  = introduce (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
               m.CS.model_record.CS.record_read.R.epoch == R.Handshake)
              ==> m'.CS.model_record.CS.record_read.R.seq
                    == m.CS.model_record.CS.record_read.R.seq
    with _pf.
      (match role_install.CS.install_payload.CS.install_epoch,
             role_install.CS.install_payload.CS.install_direction with
       | CS.TrafficHandshake, CS.TrafficRead -> ()
       | _, _ -> ())
#pop-options

(** Server LOCAL record-seq stability (dispatch).  Only key-install locals touch
    `model_record`; the plain `LocalInstallTrafficKeys` is client-only (legality),
    so a server install is always the `_ForRole` variant. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_record_seq_stable_write
  (m:CS.connection_model) (local:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_local_event m local /\
        CS.step_local_event m local == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        record_schedule_coupling m /\
        local_write_seq_zero m local)
      (ensures
        (PC.pre_appdata_control m'.CS.model_control /\
         m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_write.R.seq
           == m.CS.model_record.CS.record_write.R.seq))
  = match local with
    | CS.LocalInstallTrafficKeysForRole role_install ->
      lemma_server_local_install_for_role_seq_stable_write m role_install m'
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_record_seq_stable_read
  (m:CS.connection_model) (local:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_local_event m local /\
        CS.step_local_event m local == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        record_schedule_coupling m /\
        local_read_seq_zero m local)
      (ensures
        (PC.pre_appdata_control m'.CS.model_control /\
         m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
         m'.CS.model_record.CS.record_read.R.seq
           == m.CS.model_record.CS.record_read.R.seq))
  = match local with
    | CS.LocalInstallTrafficKeysForRole role_install ->
      lemma_server_local_install_for_role_seq_stable_read m role_install m'
    | _ -> ()
#pop-options

(** A cleartext network step (ClientHello / ServerHello / HelloRetryRequest /
    ChangeCipherSpec, either direction) leaves the record layer UNCHANGED: no
    `next_seq` (that is for protected records) and no key install (those are local
    events).  Hence such a step trivially preserves both record seqs. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 50 --split_queries always"
let lemma_cleartext_step_record_unchanged
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnNetworkEvent dm) /\
        CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
        CS.network_message_is_cleartext dm.CL.message_direction dm.CL.message_value)
      (ensures m'.CS.model_record == m.CS.model_record)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    RECORD/APPLICATION-KEY COUPLING.  On reachable states, a record direction is
    at the `Application` epoch only once the matching APPLICATION-traffic key
    slot is populated: the epoch is set to `Application` exactly by the app-key
    install (`install_record_keys`/`install_record_keys_for_role`), which also
    populates the app slot; `next_seq`/`advance` preserve the epoch and never
    touch the schedule, and no network event ever moves a record to `Application`.
    Combined with the per-stage `application_record_epoch_reachable_shape` (app
    slots are `None` at the early handshake-install stages), this EXCLUDES a
    backward `Application -> Handshake` key install: a handshake install is pinned
    (`legal_local_event`) to an early stage where the app slot is `None`, so the
    record cannot already be at `Application`.
    ───────────────────────────────────────────────────────────────────────── **)
let app_traffic_slot
  (keys:CS.key_schedule_state) (label:CS.traffic_label)
  : option CS.traffic_key_material =
  match label with
  | CS.ClientTraffic -> keys.CS.ks_client_application_traffic
  | CS.ServerTraffic -> keys.CS.ks_server_application_traffic

let record_app_epoch_coupling (m:CS.connection_model) : prop =
  let role = m.CS.model_config.CS.config_role in
  let keys = m.CS.model_handshake.CS.hs_keys in
  (m.CS.model_record.CS.record_write.R.epoch == R.Application ==>
     Some? (app_traffic_slot keys
             (CS.traffic_label_for_endpoint_direction role CS.TrafficWrite))) /\
  (m.CS.model_record.CS.record_read.R.epoch == R.Application ==>
     Some? (app_traffic_slot keys
             (CS.traffic_label_for_endpoint_direction role CS.TrafficRead)))

#push-options "--fuel 4 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_step_record_app_epoch_coupling
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        record_app_epoch_coupling m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures record_app_epoch_coupling m')
  = match ev with
    | CS.ConnNetworkEvent _ -> ()
    | CS.ConnProtectedHandshake _ -> ()
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalInstallTrafficKeys install -> ()
       | CS.LocalInstallTrafficKeysForRole role_install -> ()
       | _ -> ())
#pop-options

let lemma_delta_record_app_epoch_coupling
  (st0 st1:CS.connection_state)
  : Lemma
      (requires
        record_app_epoch_coupling st0.CS.cs_model /\
        SMR.connection_state_single_step st0 st1)
      (ensures record_app_epoch_coupling st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_record_app_epoch_coupling
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_single_step_record_app_epoch_coupling ()
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (record_app_epoch_coupling y.CS.cs_model);
                     (SMR.connection_state_single_step x y)}
          record_app_epoch_coupling x.CS.cs_model /\
          SMR.connection_state_single_step x y ==>
          record_app_epoch_coupling y.CS.cs_model)
  = introduce forall x y.
      record_app_epoch_coupling x.CS.cs_model /\
      SMR.connection_state_single_step x y ==>
      record_app_epoch_coupling y.CS.cs_model
    with
      introduce _ ==> _ with _.
      lemma_delta_record_app_epoch_coupling x y

let lemma_consistent_record_app_epoch_coupling
  (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures record_app_epoch_coupling st.CS.cs_model)
  = let p (st:CS.connection_state) = record_app_epoch_coupling st.CS.cs_model in
    lemma_single_step_record_app_epoch_coupling ();
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure
      SMR.connection_state_single_step
      p
      stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(** ─────────────────────────────────────────────────────────────────────────
    APP-SLOTS-NONE per-stage shape (self-contained RTC coupling).  At the early
    handshake stages — those at or before a handshake key install and strictly
    before any application key install — BOTH application-traffic key slots are
    empty.  Application slots are populated ONLY by an application key install,
    which `legal_local_event` pins to a LATE stage (client:
    HsServerFinishedVerified; server: HsServerFinishedSent / HsClientFinishedReceived);
    so at the early stages the app slots stay `None`.  Combined with
    `record_app_epoch_coupling`, this forces the SOURCE record epoch of a handshake
    install (pinned to an early stage) to be non-`Application` — the key fact that
    discharges the `P_installHS` premise of the counting-algebra core for a LOCAL
    step.
    ───────────────────────────────────────────────────────────────────────── **)
let client_app_slots_none_stage (control:CS.connection_control_state) : bool =
  match control with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsStarted
  | CS.ControlHandshaking CS.HsClientHelloSent
  | CS.ControlHandshaking CS.HsServerHelloReceived
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
  | CS.ControlHandshaking CS.HsCertificateReceived
  | CS.ControlHandshaking CS.HsCertificateValidated
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified
  | CS.ControlHandshaking CS.HsServerFinishedReceived -> true
  | _ -> false

let server_app_slots_none_stage (control:CS.connection_control_state) : bool =
  match control with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsAwaitingClientHello
  | CS.ControlHandshaking CS.HsClientHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> true
  | _ -> false

let app_slots_none_shape (m:CS.connection_model) : prop =
  let keys = m.CS.model_handshake.CS.hs_keys in
  (m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
   client_app_slots_none_stage m.CS.model_control == true ==>
     keys.CS.ks_client_application_traffic == None /\
     keys.CS.ks_server_application_traffic == None) /\
  (m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
   server_app_slots_none_stage m.CS.model_control == true ==>
     keys.CS.ks_client_application_traffic == None /\
     keys.CS.ks_server_application_traffic == None)

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_step_app_slots_none_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        app_slots_none_shape m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures app_slots_none_shape m')
  = ()
#pop-options

let lemma_delta_app_slots_none_shape
  (st0 st1:CS.connection_state)
  : Lemma
      (requires
        app_slots_none_shape st0.CS.cs_model /\
        SMR.connection_state_single_step st0 st1)
      (ensures app_slots_none_shape st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_app_slots_none_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_single_step_app_slots_none_shape ()
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (app_slots_none_shape y.CS.cs_model);
                     (SMR.connection_state_single_step x y)}
          app_slots_none_shape x.CS.cs_model /\
          SMR.connection_state_single_step x y ==>
          app_slots_none_shape y.CS.cs_model)
  = introduce forall x y.
      app_slots_none_shape x.CS.cs_model /\
      SMR.connection_state_single_step x y ==>
      app_slots_none_shape y.CS.cs_model
    with
      introduce _ ==> _ with _.
      lemma_delta_app_slots_none_shape x y

let lemma_consistent_app_slots_none_shape
  (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures app_slots_none_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = app_slots_none_shape st.CS.cs_model in
    lemma_single_step_app_slots_none_shape ();
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (SMR.connection_state_single_step x y)}
          p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure
      SMR.connection_state_single_step
      p
      stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(** ─────────────────────────────────────────────────────────────────────────
    A network step whose byte-delta is EMPTY, taken from a pre-application-data
    control state, leaves `model_record` UNCHANGED.  With empty raw the message
    cannot be protected (a protected record needs at least one ApplicationData
    record, whose serialization is non-empty — refuted by
    `lemma_ws_raw_records_nonempty_parse_record`); the only protected message with
    a possibly-zero record count is a `Sent` `TlsApplicationData`, which is legal
    ONLY at `ControlApplicationData` (excluded by `pre_appdata`).  Hence the
    message is cleartext, and `lemma_cleartext_step_record_unchanged` applies.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_network_empty_delta_record_unchanged
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnNetworkEvent dm) /\
        CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
        CS.event_raw_delta_legal m (CS.ConnNetworkEvent dm) B.empty B.empty /\
        PC.pre_appdata_control m.CS.model_control)
      (ensures m'.CS.model_record == m.CS.model_record)
  = if CS.network_message_is_cleartext dm.CL.message_direction dm.CL.message_value
    then lemma_cleartext_step_record_unchanged m dm m'
    else begin
      (match dm.CL.message_direction with
       | CL.Sent ->
         assert (CS.network_message_raw_delta_legal m dm B.empty);
         assert (CS.raw_records_exactly B.empty T.Application_data
                   (CS.protected_record_count CL.Sent dm.CL.message_value));
         (match dm.CL.message_value with
          | M.TlsApplicationData _ -> ()
          | _ ->
            WStep.lemma_ws_raw_records_nonempty_parse_record
              B.empty T.Application_data
              (CS.protected_record_count CL.Sent dm.CL.message_value))
       | CL.Received ->
         assert (CS.network_message_raw_delta_legal m dm B.empty);
         assert (CS.raw_records_exactly B.empty T.Application_data
                   (CS.protected_record_count CL.Received dm.CL.message_value));
         WStep.lemma_ws_raw_records_nonempty_parse_record
           B.empty T.Application_data
           (CS.protected_record_count CL.Received dm.CL.message_value))
    end
#pop-options

(** A buffered protected-handshake drain has no raw bytes.  Non-Finished
    drains restore the source read-record state; Finished atomically installs
    the application read state, making all handshake/initial post-state gates
    vacuous. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_protected_empty_delta_read_facts
  (m:CS.connection_model) (step:CS.protected_handshake_step)
  (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnProtectedHandshake step) /\
        CS.step_model m (CS.ConnProtectedHandshake step) == Some m' /\
        CS.event_raw_delta_legal m (CS.ConnProtectedHandshake step) B.empty B.empty)
      (ensures
        (PC.pre_appdata_control m'.CS.model_control /\
         m.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         m'.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
           m'.CS.model_record.CS.record_read.R.seq ==
             m.CS.model_record.CS.record_read.R.seq) /\
        (PC.pre_appdata_control m'.CS.model_control /\
         m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         ~(m.CS.model_record.CS.record_read.R.epoch == R.Handshake) ==>
           m'.CS.model_record.CS.record_read.R.seq == 0) /\
        (PC.pre_appdata_control m'.CS.model_control /\
         m'.CS.model_record.CS.record_read.R.epoch == R.Initial ==>
           m.CS.model_record.CS.record_read.R.epoch == R.Initial))
  =
  if step.CS.protected_handshake_head
  then
    ( assert (CS.raw_records_exactly B.empty T.Application_data 1);
      WStep.lemma_ws_raw_records_nonempty_parse_record B.empty T.Application_data 1 )
  else
    match step.CS.protected_handshake_message with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _ ->
      assert (m'.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read)
    | M.Finished _ ->
      assert (m'.CS.model_record.CS.record_read.R.epoch == R.Application)
    | _ ->
      assert False
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    CLIENT LOCAL install characterization (P_installHS + P_initial, model level).
    A client LOCAL step changes `model_record` ONLY via a key install; a write
    install that MOVES the epoch to `Handshake` must be a `(TrafficHandshake,
    TrafficWrite)` install (others leave the write direction fixed or move it to
    `Application`), which `R.install_keys` sets to seq 0.  Its SOURCE epoch cannot
    be `Application`: `legal_local_event` pins a handshake install to the early
    stage `HsServerHelloReceived`, where `app_slots_none_shape` forces both
    application-traffic slots `None`, so `record_app_epoch_coupling` rules out a
    pre-existing `Application` record — hence the source epoch is `Initial`.  The
    read direction is the mirror.  A write/read that STAYS at `Initial` was left
    untouched (installs never yield `Initial`), so the source epoch is `Initial`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_record_install_char
  (m:CS.connection_model) (local:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_local_event m local /\
        CS.step_local_event m local == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_app_epoch_coupling m /\
        app_slots_none_shape m)
      (ensures
        (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         ~(m.CS.model_record.CS.record_write.R.epoch == R.Handshake) ==>
         m'.CS.model_record.CS.record_write.R.seq == 0 /\
         m.CS.model_record.CS.record_write.R.epoch == R.Initial) /\
        (m'.CS.model_record.CS.record_write.R.epoch == R.Initial ==>
         m.CS.model_record.CS.record_write.R.epoch == R.Initial) /\
        (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         ~(m.CS.model_record.CS.record_read.R.epoch == R.Handshake) ==>
         m'.CS.model_record.CS.record_read.R.seq == 0 /\
         m.CS.model_record.CS.record_read.R.epoch == R.Initial) /\
        (m'.CS.model_record.CS.record_read.R.epoch == R.Initial ==>
         m.CS.model_record.CS.record_read.R.epoch == R.Initial))
  = ()
#pop-options

(** SERVER LOCAL install characterization — mirror of the client version.  A server
    installs traffic keys ONLY via `LocalInstallTrafficKeysForRole` with
    `install_role == ServerEndpoint`.  A write install that reaches the `Handshake`
    epoch is the `(TrafficHandshake, TrafficWrite)` install (the app-write install
    moves the write record to `Application`, not `Handshake`), pinned by
    `legal_local_event` to `HsServerHelloSent`; there `app_slots_none_shape` +
    `record_app_epoch_coupling` exclude a pre-existing `Application` record, so the
    source epoch is `Initial`.  The read direction is the mirror (handshake read
    install pinned to `HsServerHelloSent`). **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_record_install_char
  (m:CS.connection_model) (local:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_local_event m local /\
        CS.step_local_event m local == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        record_app_epoch_coupling m /\
        app_slots_none_shape m)
      (ensures
        (m'.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         ~(m.CS.model_record.CS.record_write.R.epoch == R.Handshake) ==>
         m'.CS.model_record.CS.record_write.R.seq == 0 /\
         m.CS.model_record.CS.record_write.R.epoch == R.Initial) /\
        (m'.CS.model_record.CS.record_write.R.epoch == R.Initial ==>
         m.CS.model_record.CS.record_write.R.epoch == R.Initial) /\
        (m'.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
         ~(m.CS.model_record.CS.record_read.R.epoch == R.Handshake) ==>
         m'.CS.model_record.CS.record_read.R.seq == 0 /\
         m.CS.model_record.CS.record_read.R.epoch == R.Initial) /\
        (m'.CS.model_record.CS.record_read.R.epoch == R.Initial ==>
         m.CS.model_record.CS.record_read.R.epoch == R.Initial))
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    DISCHARGE of the redundant-handshake-install GATE at reachable states.  Each
    helper proves the per-direction `local_{write,read}_seq_zero` gate for the
    actual local event `local'` of a REACHABLE endpoint whose control is still in
    the pre-application-data region.  The proof: a handshake install is legal only
    at a single control per endpoint (`traffic_install_allowed_at_stage[_for_role]`
    pins CLIENT handshake installs to `HsServerHelloReceived` and SERVER handshake
    installs to `HsServerHelloSent`), where the direction's appdata count is 0
    (WireStep count-at-stage FACTs), so `pwrite_ok`/`pread_ok` forces the pre-install
    seq to 0.  Non-install locals leave the record fixed, so the gate is vacuous.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_discharge_client_write
  (a:CS.connection_state) (local':CS.local_event)
  : Lemma
      (requires
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        pwrite_ok a /\
        PC.pre_appdata_control a.CS.cs_model.CS.model_control /\
        WStep.client_reachable (CS.initial a.CS.cs_model.CS.model_config) a /\
        WFL.supported_client_config_wire_profile a.CS.cs_model.CS.model_config)
      (ensures local_write_seq_zero a.CS.cs_model local')
  = let m = a.CS.cs_model in
    assert (WStep.pre_appdata_ctrl m.CS.model_control);
    WStep.lemma_client_preappdata_sent_no_appdata m.CS.model_config a;
    // count(a.raw_sent)==0, and pwrite_ok (pre_appdata) => write seq == count == 0
    (match local' with
     | CS.LocalInstallTrafficKeys install -> ()
     | CS.LocalInstallTrafficKeysForRole ri -> ()
     | _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_discharge_client_read
  (a:CS.connection_state) (local':CS.local_event)
  : Lemma
      (requires
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        pread_ok a /\
        PC.pre_appdata_control a.CS.cs_model.CS.model_control /\
        WStep.client_reachable (CS.initial a.CS.cs_model.CS.model_config) a /\
        CS.legal_local_event a.CS.cs_model local')
      (ensures local_read_seq_zero a.CS.cs_model local')
  = let m = a.CS.cs_model in
    match local' with
    | CS.LocalInstallTrafficKeys install ->
      introduce (install.CS.install_epoch == CS.TrafficHandshake /\
                 install.CS.install_direction == CS.TrafficRead /\
                 m.CS.model_record.CS.record_read.R.epoch == R.Handshake)
                ==> m.CS.model_record.CS.record_read.R.seq == 0
      with _pf.
        ( assert (CS.ControlHandshaking? m.CS.model_control);
          assert (m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
          WStep.lemma_client_hsserverhelloreceived_recv_zero m.CS.model_config a )
    | CS.LocalInstallTrafficKeysForRole ri ->
      introduce (ri.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
                 ri.CS.install_payload.CS.install_direction == CS.TrafficRead /\
                 m.CS.model_record.CS.record_read.R.epoch == R.Handshake)
                ==> m.CS.model_record.CS.record_read.R.seq == 0
      with _pf.
        ( assert (CS.ControlHandshaking? m.CS.model_control);
          assert (m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
          WStep.lemma_client_hsserverhelloreceived_recv_zero m.CS.model_config a )
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_discharge_server_write
  (a:CS.connection_state) (local':CS.local_event)
  : Lemma
      (requires
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        pwrite_ok a /\
        PC.pre_appdata_control a.CS.cs_model.CS.model_control /\
        WStep.server_reachable (CS.initial a.CS.cs_model.CS.model_config) a /\
        CS.legal_local_event a.CS.cs_model local')
      (ensures local_write_seq_zero a.CS.cs_model local')
  = let m = a.CS.cs_model in
    match local' with
    | CS.LocalInstallTrafficKeysForRole ri ->
      introduce (ri.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
                 ri.CS.install_payload.CS.install_direction == CS.TrafficWrite /\
                 m.CS.model_record.CS.record_write.R.epoch == R.Handshake)
                ==> m.CS.model_record.CS.record_write.R.seq == 0
      with _pf.
        ( assert (CS.ControlHandshaking? m.CS.model_control);
          assert (m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
          WStep.lemma_server_hsserverhellosent_sent_zero m.CS.model_config a )
    | CS.LocalInstallTrafficKeys install ->
      // client-only install; legal_local_event forces role ClientEndpoint,
      // contradicting the ServerEndpoint requires — vacuous.
      ()
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_discharge_server_read
  (a:CS.connection_state) (local':CS.local_event)
  : Lemma
      (requires
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        pread_ok a /\
        PC.pre_appdata_control a.CS.cs_model.CS.model_control /\
        WStep.server_reachable (CS.initial a.CS.cs_model.CS.model_config) a /\
        CS.legal_local_event a.CS.cs_model local')
      (ensures local_read_seq_zero a.CS.cs_model local')
  = let m = a.CS.cs_model in
    match local' with
    | CS.LocalInstallTrafficKeysForRole ri ->
      introduce (ri.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
                 ri.CS.install_payload.CS.install_direction == CS.TrafficRead /\
                 m.CS.model_record.CS.record_read.R.epoch == R.Handshake)
                ==> m.CS.model_record.CS.record_read.R.seq == 0
      with _pf.
        ( assert (CS.ControlHandshaking? m.CS.model_control);
          assert (m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
          WStep.lemma_server_hsserverhellosent_recv_zero m.CS.model_config a )
    | CS.LocalInstallTrafficKeys install ->
      ()
    | _ -> ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    CLIENT LOCAL, WRITE side.  Given a legal LOCAL delta (empty byte-deltas) from
    a client state whose model couplings hold and which is reachable, `pwrite_ok`
    transports to the post-state.  The three gated premises of
    `lemma_pwrite_algebra` are discharged from the per-transition record facts:
    `lemma_client_local_record_seq_stable_write` (P_seqdelta — its redundant-install
    gate discharged reachably below), `lemma_client_local_record_install_char`
    (P_installHS/P_initial),
    and `lemma_network_empty_delta_record_unchanged` (network conn-events leave the
    record fixed).  The `raw_sent` log is unchanged (empty delta), so
    `raw_appdata_count c'.raw_sent == raw_appdata_count a.raw_sent`; when the source
    write epoch is `Initial` this is 0 by `pwrite_ok a`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_pwrite
  (a:CS.connection_state) (d:CS.connection_delta) (c':CS.connection_state)
  : Lemma
      (requires
        CS.legal_connection_delta a d c' /\
        Seq.equal d.CS.delta_raw_sent B.empty /\
        Seq.equal d.CS.delta_raw_received B.empty /\
        pwrite_ok a /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_schedule_coupling a.CS.cs_model /\
        record_app_epoch_coupling a.CS.cs_model /\
        app_slots_none_shape a.CS.cs_model /\
        WFL.supported_client_config_wire_profile a.CS.cs_model.CS.model_config /\
        WStep.client_reachable (CS.initial a.CS.cs_model.CS.model_config) a)
      (ensures pwrite_ok c')
  = if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then
    (
      lemma_pre_appdata_back a d c';
      WStep.lemma_client_reachable_raw_sent_parses a.CS.cs_model.CS.model_config a;
      eliminate exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          a.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
      returns pwrite_ok c'
      with _pf.
      (
        // count(c'.raw_sent) == count(a.raw_sent)  (empty sent delta)
        WStep.lemma_raw_appdata_count_seq_equal d.CS.delta_raw_sent B.empty;
        WStep.lemma_raw_appdata_count_empty ();
        WStep.lemma_raw_appdata_count_append
          a.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent msgs;
        WStep.lemma_raw_appdata_count_seq_equal
          c'.CS.cs_wire_log.CL.raw_sent
          (B.append a.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent);
        // per-transition record facts
        (match d.CS.delta_event with
         | CS.ConnLocalEvent local' ->
           assert (CS.legal_local_event a.CS.cs_model local');
           assert (CS.step_local_event a.CS.cs_model local' == Some c'.CS.cs_model);
           lemma_discharge_client_write a local';
           lemma_client_local_record_seq_stable_write a.CS.cs_model local' c'.CS.cs_model;
           lemma_client_local_record_install_char a.CS.cs_model local' c'.CS.cs_model
         | CS.ConnProtectedHandshake _ -> ()
         | CS.ConnNetworkEvent dm ->
           lemma_network_empty_delta_record_unchanged a.CS.cs_model dm c'.CS.cs_model);
        lemma_pwrite_algebra a d c' msgs
      )
    )
    else ()
#pop-options

(** CLIENT LOCAL, READ side — mirror of `lemma_client_local_pwrite` on
    `record_read` / `raw_received`. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_client_local_pread
  (a:CS.connection_state) (d:CS.connection_delta) (c':CS.connection_state)
  : Lemma
      (requires
        CS.legal_connection_delta a d c' /\
        Seq.equal d.CS.delta_raw_sent B.empty /\
        Seq.equal d.CS.delta_raw_received B.empty /\
        pread_ok a /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        record_schedule_coupling a.CS.cs_model /\
        record_app_epoch_coupling a.CS.cs_model /\
        app_slots_none_shape a.CS.cs_model /\
        WStep.client_reachable (CS.initial a.CS.cs_model.CS.model_config) a)
      (ensures pread_ok c')
  = if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then
    (
      lemma_pre_appdata_back a d c';
      WStep.lemma_client_reachable_raw_received_parses a.CS.cs_model.CS.model_config a;
      eliminate exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          a.CS.cs_wire_log.CL.raw_received msgs Seq.empty
      returns pread_ok c'
      with _pf.
      (
        WStep.lemma_raw_appdata_count_seq_equal d.CS.delta_raw_received B.empty;
        WStep.lemma_raw_appdata_count_empty ();
        WStep.lemma_raw_appdata_count_append
          a.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received msgs;
        WStep.lemma_raw_appdata_count_seq_equal
          c'.CS.cs_wire_log.CL.raw_received
          (B.append a.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received);
        (match d.CS.delta_event with
         | CS.ConnLocalEvent local' ->
           assert (CS.legal_local_event a.CS.cs_model local');
           assert (CS.step_local_event a.CS.cs_model local' == Some c'.CS.cs_model);
           lemma_discharge_client_read a local';
           lemma_client_local_record_seq_stable_read a.CS.cs_model local' c'.CS.cs_model;
           lemma_client_local_record_install_char a.CS.cs_model local' c'.CS.cs_model
         | CS.ConnProtectedHandshake step ->
           assert (CS.legal_event a.CS.cs_model (CS.ConnProtectedHandshake step));
           assert (CS.step_model a.CS.cs_model (CS.ConnProtectedHandshake step) ==
                   Some c'.CS.cs_model);
           assert (CS.event_raw_delta_legal a.CS.cs_model
                     (CS.ConnProtectedHandshake step) B.empty B.empty);
           lemma_client_protected_empty_delta_read_facts
             a.CS.cs_model step c'.CS.cs_model
         | CS.ConnNetworkEvent dm ->
           lemma_network_empty_delta_record_unchanged a.CS.cs_model dm c'.CS.cs_model);
        lemma_pread_algebra a d c' msgs
      )
    )
    else ()
#pop-options


(** ─────────────────────────────────────────────────────────────────────────
    SERVER LOCAL, WRITE / READ sides — mirrors of the client helpers, using the
    server per-transition record facts and the local server reachability
    parse-witness helpers.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_pwrite
  (a:CS.connection_state) (d:CS.connection_delta) (c':CS.connection_state)
  : Lemma
      (requires
        CS.legal_connection_delta a d c' /\
        Seq.equal d.CS.delta_raw_sent B.empty /\
        Seq.equal d.CS.delta_raw_received B.empty /\
        pwrite_ok a /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        record_schedule_coupling a.CS.cs_model /\
        record_app_epoch_coupling a.CS.cs_model /\
        app_slots_none_shape a.CS.cs_model /\
        WStep.server_reachable (CS.initial a.CS.cs_model.CS.model_config) a)
      (ensures pwrite_ok c')
  = if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then
    (
      lemma_pre_appdata_back a d c';
      lemma_server_reachable_raw_sent_parses a.CS.cs_model.CS.model_config a;
      eliminate exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          a.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
      returns pwrite_ok c'
      with _pf.
      (
        WStep.lemma_raw_appdata_count_seq_equal d.CS.delta_raw_sent B.empty;
        WStep.lemma_raw_appdata_count_empty ();
        WStep.lemma_raw_appdata_count_append
          a.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent msgs;
        WStep.lemma_raw_appdata_count_seq_equal
          c'.CS.cs_wire_log.CL.raw_sent
          (B.append a.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent);
        (match d.CS.delta_event with
         | CS.ConnLocalEvent local' ->
           assert (CS.legal_local_event a.CS.cs_model local');
           assert (CS.step_local_event a.CS.cs_model local' == Some c'.CS.cs_model);
           lemma_discharge_server_write a local';
           lemma_server_local_record_seq_stable_write a.CS.cs_model local' c'.CS.cs_model;
           lemma_server_local_record_install_char a.CS.cs_model local' c'.CS.cs_model
         | CS.ConnProtectedHandshake _ -> ()
         | CS.ConnNetworkEvent dm ->
           lemma_network_empty_delta_record_unchanged a.CS.cs_model dm c'.CS.cs_model);
        lemma_pwrite_algebra a d c' msgs
      )
    )
    else ()
#pop-options

#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_server_local_pread
  (a:CS.connection_state) (d:CS.connection_delta) (c':CS.connection_state)
  : Lemma
      (requires
        CS.legal_connection_delta a d c' /\
        Seq.equal d.CS.delta_raw_sent B.empty /\
        Seq.equal d.CS.delta_raw_received B.empty /\
        pread_ok a /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        record_schedule_coupling a.CS.cs_model /\
        record_app_epoch_coupling a.CS.cs_model /\
        app_slots_none_shape a.CS.cs_model /\
        WStep.server_reachable (CS.initial a.CS.cs_model.CS.model_config) a)
      (ensures pread_ok c')
  = if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then
    (
      lemma_pre_appdata_back a d c';
      lemma_server_reachable_raw_received_parses a.CS.cs_model.CS.model_config a;
      eliminate exists (msgs:list CW.wire_message).
        WF.parses_as CW.tls_record_wire_format
          a.CS.cs_wire_log.CL.raw_received msgs Seq.empty
      returns pread_ok c'
      with _pf.
      (
        WStep.lemma_raw_appdata_count_seq_equal d.CS.delta_raw_received B.empty;
        WStep.lemma_raw_appdata_count_empty ();
        WStep.lemma_raw_appdata_count_append
          a.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received msgs;
        WStep.lemma_raw_appdata_count_seq_equal
          c'.CS.cs_wire_log.CL.raw_received
          (B.append a.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received);
        (match d.CS.delta_event with
         | CS.ConnLocalEvent local' ->
           assert (CS.legal_local_event a.CS.cs_model local');
           assert (CS.step_local_event a.CS.cs_model local' == Some c'.CS.cs_model);
           lemma_discharge_server_read a local';
           lemma_server_local_record_seq_stable_read a.CS.cs_model local' c'.CS.cs_model;
           lemma_server_local_record_install_char a.CS.cs_model local' c'.CS.cs_model
         | CS.ConnProtectedHandshake _ -> ()
         | CS.ConnNetworkEvent dm ->
           lemma_network_empty_delta_record_unchanged a.CS.cs_model dm c'.CS.cs_model);
        lemma_pread_algebra a d c' msgs
      )
    )
    else ()
#pop-options


(** ─────────────────────────────────────────────────────────────────────────
    H_seq PAYOFF.

    The whole point of the counting invariants: given `pwrite_ok` on the sender
    and `pread_ok` on the receiver, both still in the pre-application-data region
    and both at the Handshake RECORD epoch, and the `byte_pairing` byte-equality
    (sender's sent log == receiver's received log), the two record `seq` counters
    are equal — i.e. `H_seq`, the seq-alignment HYPOTHESIS consumed by the
    protected-message decode lemmas and baked into
    `protected_handshake_event_projection_pair`.  H_seq is thus a COROLLARY of
    `byte_pairing` + the counting invariants, with no dependence on the event-log
    length or the strict-progress guards.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_hseq_from_counts (sender receiver:CS.connection_state)
  : Lemma
      (requires
        pwrite_ok sender /\
        pread_ok receiver /\
        PC.pre_appdata_control sender.CS.cs_model.CS.model_control /\
        PC.pre_appdata_control receiver.CS.cs_model.CS.model_control /\
        sender.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
        receiver.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
        Seq.equal
          sender.CS.cs_wire_log.CL.raw_sent
          receiver.CS.cs_wire_log.CL.raw_received)
      (ensures
        sender.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.cs_model.CS.model_record.CS.record_read.R.seq)
  = WStep.lemma_raw_appdata_count_seq_equal
      sender.CS.cs_wire_log.CL.raw_sent
      receiver.CS.cs_wire_log.CL.raw_received
#pop-options
