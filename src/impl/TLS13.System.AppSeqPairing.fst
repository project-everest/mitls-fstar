module TLS13.System.AppSeqPairing

(**
  STAGE (b) — application-epoch RECORD-SEQUENCE alignment.

  Goal: at an application-data DELIVERY the sender's `record_write.seq` equals the
  receiver's `record_read.seq`, so that (together with the STAGE (a) key/iv
  agreement) the faithful-decode bridge
  `CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer`
  applies at STAGE (c).

  WHY A NEW CHANNEL-RELATIVE SHAPE (not an extension of `SeqCountBase`).
  `SeqCountBase` founds the handshake-region `H_seq` on `raw_appdata_count` of the
  whole raw log, GATED on `PC.pre_appdata_control`.  That gate is a DELIBERATE
  scoping decision with a machine-checked counterexample (a mid-handshake
  Close_notify/fail freezes `record_write` at the Handshake epoch while forcing one
  protected ApplicationData record onto the sent log, so the ungated clause is
  FALSE at close/fail exits).  It cannot simply be extended to the app region:
  `R.install_keys` RESETS `seq` to 0 at the epoch boundary, whereas
  `raw_appdata_count` keeps counting the protected HANDSHAKE flight, so the
  handshake anchor `seq == raw_appdata_count(raw_sent)` is false past the boundary
  by an (unstored) offset.

  Instead we mirror `byte_pairing` one level up, on the record SEQ counters.  The
  key device is the EPOCH-COLLAPSING projection `app_wseq`/`app_rseq`, which reads
  a direction's seq only when that direction is at the `Application` epoch and is
  `0` otherwise.  Because a fresh application epoch starts at seq `0`
  (`R.install_keys` resets), the projection is CONTINUOUS across the epoch
  boundary: it stays `0` through the whole handshake (both endpoints not-yet-App
  give `0`), and it stays `0` at the instant either endpoint installs its app keys.
  This makes the pairing identity UNGUARDED — no epoch case-split, no
  transition-window clauses, and no cross-endpoint epoch coupling — exactly like
  `byte_pairing` on raw bytes, one level up.
**)

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
module SCB  = TLS13.System.SeqCountBase
module ORD  = TLS13.System.Ordering
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module HANR = TLS13.ConnectionState.HandshakeAgreementNonReady
module WFL  = TLS13.Spec.WireFormatLemmas
module SLM  = TLS13.System.SlotMono
module RKE  = TLS13.ConnectionState.RecordKeyEpoch
module CCShape = TLS13.ConnectionState.ClientCanonicalShape

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(** The write / read record-layer direction states of an endpoint. **)
let wr (st:CS.connection_state) : R.direction_state =
  st.CS.cs_model.CS.model_record.CS.record_write

let rd (st:CS.connection_state) : R.direction_state =
  st.CS.cs_model.CS.model_record.CS.record_read

(** The write direction state captured in an in-flight payload's sender snapshot. **)
let snap_wr (p:SY.tls_payload) : R.direction_state =
  p.SY.pl_snap.CS.model_record.CS.record_write

(** EPOCH-COLLAPSING seq projections: the record seq counted only while at the
    application epoch, and `0` otherwise.  Continuous across the epoch boundary
    (a fresh app epoch starts at seq `0`). **)
let app_wseq (st:CS.connection_state) : nat =
  if R.Application? (wr st).R.epoch then (wr st).R.seq else 0

let app_rseq (st:CS.connection_state) : nat =
  if R.Application? (rd st).R.epoch then (rd st).R.seq else 0

let snap_app_wseq (p:SY.tls_payload) : nat =
  if R.Application? (snap_wr p).R.epoch then (snap_wr p).R.seq else 0

(** How many records a SEND of message `m` advances `record_write` by — the
    `application_data_record_count` of an application-data payload, and one for
    every other (single-record) message.  This is exactly the advance applied by
    `CS.step_tls_message` at the app-data arm, and by `R.next_seq` elsewhere. **)

(** ─────────────────────────────────────────────────────────────────────────
    MODEL-LEVEL seq machinery and the SEND / RECEIVE record-seq DELTA lemmas.

    These are the engine behind the 6-family `app_seq_pairing` preservation: they
    say EXACTLY how a legal `step_tls_message` moves the epoch-collapsing write /
    read projections, so each family lemma reduces to "the acting endpoint stepped
    by this message".
    ───────────────────────────────────────────────────────────────────────── **)

let m_wr (m:CS.connection_model) : R.direction_state =
  m.CS.model_record.CS.record_write
let m_rd (m:CS.connection_model) : R.direction_state =
  m.CS.model_record.CS.record_read

(** The epoch-collapsing seq projections at the MODEL level.  Definitionally
    `app_wseq st == m_wseq st.cs_model`, `app_rseq st == m_rseq st.cs_model`, and
    `snap_app_wseq p == m_wseq p.pl_snap`. **)
let m_wseq (m:CS.connection_model) : nat =
  if R.Application? (m_wr m).R.epoch then (m_wr m).R.seq else 0
let m_rseq (m:CS.connection_model) : nat =
  if R.Application? (m_rd m).R.epoch then (m_rd m).R.seq else 0

(** The app-epoch WRITE advance a SENT message applies to `record_write.seq`,
    keyed on the SENDER'S CONTROL (which is what `step_tls_message` actually
    dispatches on).  Only two `Sent` arms advance the write seq while at the
    application region:

      * `TlsApplicationData b` at `ControlApplicationData`
          → `application_data_record_count b`  (the app-data arm);
      * `TlsAlert Close_notify` at `ControlApplicationData`
          → `1`  (`next_seq`, moving to `ControlClosing`).

    EVERYTHING ELSE is `0`: a non-close alert (or a close at any OTHER control,
    e.g. `ControlClosed`) hits the `fail_model` catch-all, which PRESERVES
    `model_record` (no seq advance); a `Close_notify` re-send at `ControlClosing`
    or `ControlFailed` is `None`.  Keying on control — not on the message alone —
    is load-bearing: a message-only count would wrongly credit a close that failed
    from `ControlClosed`. **)
let m_wadv (m:CS.connection_model) (msg:M.tls_message) : nat =
  match msg, m.CS.model_control with
  | M.TlsApplicationData b, CS.ControlApplicationData -> RF.application_data_record_count b
  | M.TlsAlert T.Close_notify, CS.ControlApplicationData -> 1
  | _, _ -> 0

(** The app-epoch READ advance a RECEIVED message applies to `record_read.seq`,
    keyed on the RECEIVER'S CONTROL.  Every deliverable protected payload bumps the
    read seq by exactly one (`step_tls_message` uses `next_seq`):

      * `TlsApplicationData`/`TlsIgnoredPostHandshake`/`Close_notify` at
        `ControlApplicationData` → `1`;
      * `Close_notify` at `ControlClosing` → `1`  (`next_seq`, moving to
        `ControlClosed`);
      * everything else → `0`  (`fail_model` catch-all preserves `model_record`,
        or the arm is `None`). **)
let m_radv (m:CS.connection_model) (msg:M.tls_message) : nat =
  match msg, m.CS.model_control with
  | M.TlsApplicationData _, CS.ControlApplicationData -> 1
  | M.TlsIgnoredPostHandshake _, CS.ControlApplicationData -> 1
  | M.TlsAlert T.Close_notify, CS.ControlApplicationData -> 1
  | M.TlsAlert T.Close_notify, CS.ControlClosing -> 1
  | _, _ -> 0

(** The application record delta an in-flight payload contributes — the
    control-aware write advance evaluated at the SENDER'S sealing SNAPSHOT
    (`pl_snap`), counted only when that snapshot was at the `Application` epoch (a
    protected handshake record snapshots at the `Handshake` epoch and contributes
    `0`). **)
let rin (p:SY.tls_payload) : nat =
  m_wadv p.SY.pl_snap p.SY.pl_sent

let rin_app (p:SY.tls_payload) : nat =
  if R.Application? (snap_wr p).R.epoch then rin p else 0

(** A no-key-update event log whose LAST event sends `msg` cannot send a
    `KeyUpdate` — the tail element must itself be non-`KeyUpdate`.  This is how
    `SY.tls_no_rekeying` on the POST-state excludes the `KeyUpdate` arms of
    `step_tls_message` from the SEND families. **)
let rec lemma_no_key_update_tail (log:list CS.conn_event) (ev:CS.conn_event)
  : Lemma
      (requires SMCorr.conn_events_no_key_update (log @ [ev]) == true)
      (ensures SMCorr.conn_event_is_key_update ev == false)
      (decreases log)
  = match log with
    | [] -> ()
    | _ :: rest -> lemma_no_key_update_tail rest ev

(** A client/server that sent `msg` last, in a no-key-update trace, did not send a
    `KeyUpdate`. **)
let lemma_sent_not_key_update (st:CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        SMCorr.connection_state_no_key_update_trace st /\
        (exists (prefix:list CS.conn_event).
          st.CS.cs_event_log == prefix @ [SMKM.sent_tls_event msg]))
      (ensures ~(M.TlsKeyUpdate? msg))
  = eliminate exists (prefix:list CS.conn_event).
       st.CS.cs_event_log == prefix @ [SMKM.sent_tls_event msg]
    with
      lemma_no_key_update_tail prefix (SMKM.sent_tls_event msg)

(** SEND DELTA.  A legal `Sent` model step advances the epoch-collapsing WRITE
    projection by `m_wadv m msg` (when the writer is at the `Application` epoch)
    and leaves the READ projection unchanged.

    The GUARD `((m_wr m).epoch =!= Application \/ ~TlsHandshake? msg)` excludes the
    single false case — a HANDSHAKE send while the write epoch is already
    `Application` — which is unreachable in the real system (client: the
    strengthened `HsServerFinishedVerified` shape gives write epoch `=!= Application`
    at every handshaking control; app-data control forbids handshake sends).  The
    `~TlsKeyUpdate? msg` hypothesis excludes the rekeying arms (which `install_keys`
    and would reset seq), supplied by `SY.tls_no_rekeying`. **)
(** `advance_direction_records` bumps `seq` by exactly `n` (and preserves the
    epoch, per the existing `CSL.lemma_advance_direction_records_preserves_epoch`).
    Needed for the app-data SEND arm, which advances the write by
    `application_data_record_count` records at once. **)
let rec lemma_advance_direction_records_seq (st:R.direction_state) (n:nat)
  : Lemma
      (ensures (CS.advance_direction_records st n).R.seq == st.R.seq + n)
      (decreases n)
  = if n = 0 then () else lemma_advance_direction_records_seq st (n - 1)

let rec lemma_advance_direction_records_epoch (st:R.direction_state) (n:nat)
  : Lemma
      (ensures (CS.advance_direction_records st n).R.epoch == st.R.epoch)
      (decreases n)
  = if n = 0 then () else lemma_advance_direction_records_epoch st (n - 1)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
(** The `Sent` handshake sub-case of the send delta.  With write epoch
    =!= Application, every arm keeps the epoch-collapsing write projection at 0
    (next_seq preserves the non-Application epoch; the client-Finished install
    lands Application at seq 0) and leaves the read projection unchanged. **)
let lemma_sent_handshake_wseq
  (m m':CS.connection_model) (hm:M.handshake_msg)
  : Lemma
      (requires
        CS.step_handshake_message m CL.Sent hm == Some m' /\
        (m_wr m).R.epoch =!= R.Application)
      (ensures m_wseq m' == m_wseq m /\ m_rseq m' == m_rseq m)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_sent_wseq_delta (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent msg == Some m' /\
        ~(M.TlsKeyUpdate? msg) /\
        ((m_wr m).R.epoch =!= R.Application \/ ~(M.TlsHandshake? msg)))
      (ensures
        m_wseq m' == m_wseq m + (if R.Application? (m_wr m).R.epoch then m_wadv m msg else 0) /\
        m_rseq m' == m_rseq m)
  = match msg with
    | M.TlsHandshake hm ->
        // guard forces (m_wr m).epoch =!= Application here.  Every `Sent`
        // handshake arm of `step_handshake_message` touches `record_write` only
        // through `R.next_seq` (epoch-preserving, so it stays =!= Application and
        // the projection stays 0) or through
        // `install_client_application_write_after_finished`, which installs the
        // Application epoch at seq 0 (projection 0).  `record_read` is untouched
        // on `Sent` arms (read installs are all `Received`).
        lemma_sent_handshake_wseq m m' hm
    | M.TlsApplicationData b ->
        // app-data SEND at ControlApplicationData advances the write by
        // `application_data_record_count b` records at once.
        lemma_advance_direction_records_seq (m_wr m) (RF.application_data_record_count b);
        lemma_advance_direction_records_epoch (m_wr m) (RF.application_data_record_count b)
    | _ -> ()
#pop-options

(** RECEIVE DELTA.  A legal `Received` model step advances the epoch-collapsing
    READ projection by `m_radv m msg` (when the reader is at the `Application`
    epoch) and leaves the WRITE projection unchanged.  Same guard rationale. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
(** The `Received` handshake sub-case of the receive delta. **)
let lemma_recv_handshake_rseq
  (m m':CS.connection_model) (hm:M.handshake_msg)
  : Lemma
      (requires
        CS.step_handshake_message m CL.Received hm == Some m' /\
        (m_rd m).R.epoch =!= R.Application)
      (ensures m_rseq m' == m_rseq m /\ m_wseq m' == m_wseq m)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_recv_rseq_delta (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Received msg == Some m' /\
        ~(M.TlsKeyUpdate? msg) /\
        ((m_rd m).R.epoch =!= R.Application \/ ~(M.TlsHandshake? msg)))
      (ensures
        m_rseq m' == m_rseq m + (if R.Application? (m_rd m).R.epoch then m_radv m msg else 0) /\
        m_wseq m' == m_wseq m)
  = match msg with
    | M.TlsHandshake hm -> lemma_recv_handshake_rseq m m' hm
    | _ -> ()
#pop-options

(** A RECEIVE off both `ControlApplicationData` and `ControlClosing` advances the
    read seq by ZERO: every nonzero arm of `m_radv` is at one of those two controls
    (`TlsApplicationData`/`TlsIgnoredPostHandshake`/`Close_notify @ App`, and
    `Close_notify @ Closing`).  Used at the delivery `~App (snap_wr)` branch, where
    the control-gated backward gives `~ControlApplicationData?` and `not_closing`
    gives `~ControlClosing?`. **)
let lemma_m_radv_zero_non_cad_closing (m:CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires ~(CS.ControlApplicationData? m.CS.model_control) /\
                ~(CS.ControlClosing? m.CS.model_control))
      (ensures m_radv m msg == 0)
  = ()

(** Discharges `lemma_recv_rseq_delta`'s Handshake-vs-App precondition for ANY legal
    receive from a consistent state, WITHOUT needing to know the receiver's read
    epoch.  Enumeration: a `TlsHandshake` receive that STEPS from a consistent state
    sits at one of the seven handshaking-nonfinal receive controls (none is
    `HsServerFinishedVerified` / `HsClientFinishedReceived` — those are LOCAL
    Finished-verify controls, not receive arms), and
    `lemma_handshaking_nonfinal_read_not_application` then forces `~App (rd)` there.
    A non-Handshake `msg` takes the right disjunct directly.  This is what lets the
    `~App (snap_wr)` delivery branch invoke the receive-seq delta lemma even when the
    receiver's read epoch is unknown. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_recv_precond (st st':CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        CS.step_tls_message st.CS.cs_model CL.Received msg == Some st'.CS.cs_model)
      (ensures (m_rd st.CS.cs_model).R.epoch =!= R.Application \/ ~(M.TlsHandshake? msg))
  = match msg with
    | M.TlsHandshake hm -> CSL.lemma_handshaking_nonfinal_read_not_application st
    | _ -> ()
#pop-options

(** The RECEIVER-side gate for the record-seq pairing.  TRUE on the "pre-closing"
    controls `{ControlNew, ControlHandshaking _, ControlApplicationData}`, FALSE on
    the "closing region" `{ControlClosing, ControlClosed, ControlFailed _}`.  This
    is the correct gate (see the long note below): it is TRUE through the whole
    handshake — so establishment at the `ControlHandshaking -> ControlApplicationData`
    seam still has the equality to read off — yet FALSE at exactly the closing
    controls where the mutual-close counter race desyncs the record seqs. **)
let not_closing (c:CS.connection_control_state) : bool =
  not (CS.ControlClosing? c || CS.ControlClosed? c || CS.ControlFailed? c)

(** ─────────────────────────────────────────────────────────────────────────
    GATED record-seq pairing.  The pairing is an EQUALITY between the sender's
    application write seq and the receiver's application read seq, GATED on the
    RECEIVER being OUTSIDE the closing region (`not_closing`).  There is NO global
    inequality: once a connection begins to close, no `app_wseq`/`app_rseq`
    inequality is true in EITHER direction (see the root cause below).

    WHY ONLY GATED, AND WHY THE GATE IS `not_closing` (receiver NOT in the closing
    region `{ControlClosing, ControlClosed, ControlFailed}`).

    `app_wseq`/`app_rseq` project `record_write.seq`/`record_read.seq` at the
    `Application` epoch.  These counters DESYNC across a close, because a
    `fail_model` alert SEND emits a wire record WITHOUT advancing
    `record_write.seq`, while the RECEIVER that processes that alert still advances
    `record_read.seq`.  Concretely (`M` = model step):

    THE FALSIFYING SCENARIO — a mutual-close race (single in-flight slot).
    Start: both at `ControlApplicationData`, aligned
    (`app_wseq client == app_rseq server == R_c`), channel `Quiet`.
      1. Server SENDS `Close_notify` (`ControlApplicationData`,
         `StateMachine.fst:929` Sent arm): server -> `ControlClosing`, write seq
         `next_seq`.  Channel `ToClient`.
      2. Deliver to client: client (`ControlApplicationData`) RECEIVES it ->
         `ControlClosed`, read seq `next_seq` (`StateMachine.fst:943`).  Channel
         `Quiet`.  Now client `ControlClosed`, server `ControlClosing`, still
         `app_wseq client == app_rseq server == R_c`.
      3. Client SENDS `Close_notify` FROM `ControlClosed`: matches the alert
         catch-all `| M.TlsAlert alert, _ -> Some (fail_model …)`
         (`StateMachine.fst:968`).  `fail_model` (`:303`) PRESERVES `model_record`,
         so `app_wseq client` STAYS `R_c` — yet the send still EMITS a protected
         record (the driver `ClientSendCloseNotify` has NO control gate,
         `Endpoint.Client.fst:79`; `legal_tls_message` for a Sent alert is
         `| M.TlsAlert _, _ -> True`, `StateMachine.fst:1430`; and at
         `ControlClosed` the client still holds `Application` write keys, so the
         seal succeeds).  Client -> `ControlFailed`.  Channel `ToServer p`,
         `snap_app_wseq p == R_c`.
      4. Deliver to server (`ControlClosing`) RECEIVES `Close_notify` ->
         `ControlClosed`, read seq `next_seq` (`StateMachine.fst:949` — the ONLY
         non-`ControlApplicationData` control whose Received arm still advances the
         read seq).  Channel `Quiet`, server now `ControlClosed`
         (so `~ControlFailed?` is TRUE), with `app_rseq server == R_c + 1` but
         `app_wseq client == R_c`.

    At step 4's post-state a receiver-not-failed EQUALITY demands `R_c == R_c + 1`
    and a global INEQUALITY `app_rseq server <= app_wseq client` demands
    `R_c + 1 <= R_c` — BOTH false.  The divergence is INVISIBLE to the end-to-end
    goal, a byte-stream PREFIX property: `Close_notify` carries zero application
    bytes (`app_bytes_delta`, `System.fst:397`), so `app_pairing` is untouched.

    THE GATE.  Gate the equality on the RECEIVER being OUTSIDE the closing region,
    i.e. `not_closing (ctrl receiver)` — TRUE on `{ControlNew, ControlHandshaking _,
    ControlApplicationData}`, FALSE on `{ControlClosing, ControlClosed,
    ControlFailed}`.  Every close/alert RECEIVE moves the receiver INTO the closing
    region (`:943` ApplicationData->`ControlClosed`, `:949` Closing->`ControlClosed`,
    the catch-all `:968`->`ControlFailed`), so the gate goes vacuous at exactly the
    step that would desync — the step-4 post-state above (`ControlClosed`) claims
    nothing.  No application data is ever delivered to a closing-region receiver
    (the app-data Received arm pins `ControlApplicationData`), and closing-region
    receivers only ever RECEIVE alerts/close, so gating them out loses no app-data
    alignment.  App-data deliveries keep the receiver AT `ControlApplicationData`
    and advance both sides by one, so the equality is inductive exactly where the
    faithful-decode bridge needs it.

    WHY `not_closing` AND NOT the narrower `ControlApplicationData?`.  The gate must
    also stay TRUE across the whole HANDSHAKE, because that is where the alignment
    is ESTABLISHED.  At the client's Finished send (`ControlHandshaking
    HsServerFinishedVerified -> ControlApplicationData`) the post-state's client is
    at `ControlApplicationData`, so `sc_seq_ok` on the post-state DEMANDS
    `app_wseq server == app_rseq client`.  With a `ControlApplicationData?` gate the
    PRE-state's `sc_seq_ok` is silent (the client is still handshaking), so nothing
    supplies `app_wseq server == 0` — establishment has NO source and the send
    family cannot close.  `not_closing` keeps the equality live through handshaking,
    where it reads `0 == 0` (`lemma_handshaking_{read,write}_app_seq_zero` give
    `app_rseq client == 0`; the carried equality then delivers `app_wseq server ==
    0`), so it transfers to the post-state seam for free.  `not_closing` is thus the
    MINIMAL gate: the old equality excused at exactly the absorbing closing region.

    The gate is sound BECAUSE the closing region is ABSORBING under `step_model`
    (`lemma_step_preserves_closing`, proven from the effect functions, NOT assumed):
    once a receiver enters `{Closing, Closed, Failed}` it never returns, so a send
    that could desync it (a `fail_model` alert emitted without advancing the write
    seq) can only ever reach a receiver that is ALREADY in the closing region — the
    gate is already vacuous there.

    NB — the one non-obvious soundness case.  For the gate to be inductive at a LIVE
    receiver, every message that advances the receiver's READ seq while LEAVING it
    live must be matched by a sender that advanced its WRITE seq by the same amount.
    Going through `m_radv`'s non-zero arms: app-data is symmetric (both sides +N),
    and both `Close_notify` arms move the receiver INTO the closing region (so the
    gate goes vacuous).  The ONE arm that advances the read seq AND keeps the
    receiver at `ControlApplicationData` is `M.TlsIgnoredPostHandshake` (`:858`).
    That does NOT break the gate because it can never be SENT and hence never be
    in flight: its `Sent` arm is `None` and `legal_tls_message` requires
    `dir == CL.Received` for it (`StateMachine.fst:1413`).  A future reader who
    spots the `:858` read-seq advance and fears a leak should stop here: no wire
    payload can carry a `TlsIgnoredPostHandshake`, so `cs_seq_ok`/`sc_seq_ok` never
    see it on the in-flight side.

    ✗ DO NOT re-gate on `~ControlFailed?` (a previous, committed attempt).  It is
    UNSOUND: it admits `ControlClosing`/`ControlClosed` receivers, and the
    mutual-close race above lands the receiver at `ControlClosed` (which is
    `~ControlFailed?`) with `app_rseq server == app_wseq client + 1`.
    ✗ DO NOT narrow to `ControlApplicationData?` either (also tried, and approved
    on paper): it is SOUND but breaks ESTABLISHMENT at the client-Finished seam, as
    spelled out above — the post-state claims the equality but the pre-state, being
    handshaking, supplies nothing.  Both were tried and RETRACTED; `not_closing` is
    the gate that is simultaneously sound (closing region absorbing) and
    establishable (live through the handshake).
    ───────────────────────────────────────────────────────────────────────── **)

(** ── C -> S direction (client writes, server reads). ── **)
let cs_seq_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      not_closing (SY.ctrl s.server) ==>
         snap_app_wseq p == app_rseq s.server
  | _ ->
      not_closing (SY.ctrl s.server) ==>
         app_wseq s.client == app_rseq s.server

(** ── S -> C direction (server writes, client reads). ── **)
let sc_seq_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToClient p ->
      not_closing (SY.ctrl s.client) ==>
         snap_app_wseq p == app_rseq s.client
  | _ ->
      not_closing (SY.ctrl s.client) ==>
         app_wseq s.server == app_rseq s.client

(** The application-epoch record-seq pairing invariant — the seq-level analogue
    of `SY.byte_pairing`, one level up. **)
let app_seq_pairing (s:SY.tls_system_state) : prop =
  cs_seq_ok s /\ sc_seq_ok s

(** ─────────────────────────────────────────────────────────────────────────
    STAGE (b) PAYOFF — delivery-time alignment (consumed by STAGE (c)).

    At an in-flight-to-server state whose in-flight payload was sealed at the
    application epoch and whose receiver (the server) is at the application read
    epoch, the sealing snapshot's write seq equals the server's read seq — exactly
    the `sender.record_write.seq == receiver.record_read.seq` hypothesis of the
    faithful-decode bridge.  Symmetric for the client.
    ───────────────────────────────────────────────────────────────────────── **)
let lemma_cs_delivery_alignment (s:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        app_seq_pairing s /\ s.channel == MP.ToServer p /\
        CS.ControlApplicationData? (SY.ctrl s.server) /\
        R.Application? (snap_wr p).R.epoch /\
        R.Application? (rd s.server).R.epoch)
      (ensures (snap_wr p).R.seq == (rd s.server).R.seq)
  = ()

let lemma_sc_delivery_alignment (s:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        app_seq_pairing s /\ s.channel == MP.ToClient p /\
        CS.ControlApplicationData? (SY.ctrl s.client) /\
        R.Application? (snap_wr p).R.epoch /\
        R.Application? (rd s.client).R.epoch)
      (ensures (snap_wr p).R.seq == (rd s.client).R.seq)
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    INITIAL STATE.  Both endpoints start at the `Initial` record epoch with the
    channel `Quiet`, so both projections are `0` and the identity holds.
    ───────────────────────────────────────────────────────────────────────── **)
let lemma_initial_app_seq_pairing (cfg_c cfg_s:CS.connection_config)
  : Lemma (app_seq_pairing (SY.initial_tls_system cfg_c cfg_s))
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    STAGE (c) ENGINE, PART 1 — DECODE DETERMINISM.

    `received_single_protected_message_decode model msg raw` is an existential over
    `outer_fragment`, `opened`, `plaintext`, but every stage of the pipeline
    (`W.parse_record_wire`, `R.open_record`, `W.parse_plaintext`,
    `W.parse_tls_message`) is a TOTAL function, so the witnesses are pinned
    uniquely by `raw` and the message it decodes to is determined.  Hence any two
    messages that a fixed model decodes a fixed `raw` to are equal.
    ───────────────────────────────────────────────────────────────────────── **)
let lemma_decode_functional
  (model:CS.connection_model) (msg1 msg2:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        SMCan.received_single_protected_message_decode model msg1 raw /\
        SMCan.received_single_protected_message_decode model msg2 raw)
      (ensures msg1 == msg2)
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    STAGE (c) ENGINE, PART 2 — MONOTONE APPLICATION-KEY AGREEMENT.

    Faithful decode at an application-data delivery needs key/iv agreement between
    the sender's sealing snapshot and the receiver's read direction.  The existing
    agreement tool `SY.lemma_ready_quiescent_agrees` is gated on
    `tls_application_ready` (BOTH endpoints at `ControlApplicationData`).  That is
    NOT available at every delivery: the receiver may legally have taken a
    `LocalFail` (`StateMachine.legal_local_event | LocalFail _, _ -> True`) and
    left `ControlApplicationData`.  Crucially `fail_model` preserves `model_record`
    AND `model_handshake`, so the receiver keeps its record keys/iv/epoch and key
    schedule — hence the agreement, once established, remains TRUE; it is only the
    control-gated *derivation* that stops applying.

    We therefore carry the agreement as a MONOTONE invariant conjunct, gated on the
    stable antecedent `cf_delivered` (client write epoch Application AND server read
    epoch Application), which:
      * becomes true exactly at the atomic client-Finished delivery to the server
        (`StateMachine.fst:774`), where the post-state has BOTH endpoints at
        `ControlApplicationData` and channel `Quiet` (the client is frozen at
        `ControlApplicationData` while its Finished is in flight, because sends and
        locals are gated on `is_quiet`), so `SY.lemma_ready_quiescent_agrees`
        applies THERE; and
      * PERSISTS thereafter: `R.install_keys` is the only writer of a record epoch,
        no step reverts an `Application` epoch except a `KeyUpdate` install, and
        `KeyUpdate` is excluded by the existing `SY.tls_no_rekeying` conjunct.  So
        both the antecedent and the (record/keyschedule-only) consequent survive
        any subsequent local failure or close of either endpoint.

    NOTE (load-bearing): the persistence argument depends on `SY.tls_no_rekeying`
    to exclude the `M.TlsKeyUpdate` arms of `step_tls_message`
    (`StateMachine.fst:868+`), which are the ONLY transitions that re-`install_keys`
    an already-`Application` record (resetting its seq and material).  Without that
    conjunct the consequent would not be stable. **)

(** The monotone antecedent: the client's write and the server's read record
    epochs have both reached `Application` (equivalently: the client sent its
    Finished and the server received it).  Stable under every non-rekeying step. **)
let cf_delivered (s:SY.tls_system_state) : prop =
  R.Application? (wr s.client).R.epoch /\ R.Application? (rd s.server).R.epoch

(** The gated application-record material agreement conjunct. **)
let app_material_agreement (s:SY.tls_system_state) : prop =
  cf_delivered s ==>
    SMKM.supported_profile_application_record_material_agrees s.client s.server


(** ─────────────────────────────────────────────────────────────────────────
    STAGE (c) — THE FAITHFUL-DECODE SEAL CONJUNCT.

    The in-flight protected payload's seal fact is NOT available from
    `SY.tls_system_inv` — `SY.channel_consistent` (System.fst:290) constrains only
    the two CLEARTEXT hellos and says nothing about a protected payload.  So a
    delivery cannot, from `tls_system_inv` alone, decode the wire back to the
    message the sender sealed.  We therefore CARRY, on the in-flight payload, exactly
    the inputs the faithful-decode bridge
    (`CSL.lemma_received_single_protected_message_decode_from_..._seal_peer`)
    consumes: key/iv material agreement between the sealing snapshot's write
    direction and the receiver's read direction, the single-record seal witness, and
    the message round-trip.  (The seq-alignment hypothesis of the bridge is derived
    at the delivery from `app_seq_pairing` via `lemma_cs_delivery_alignment`, so it
    is not carried here.) **)
let inflight_bridge_ready
  (snap receiver:CS.connection_model) (msg:M.tls_message) (raw:B.bytes) : prop =
  (match SMKM.record_direction_material snap.CS.model_record.CS.record_write,
         SMKM.record_direction_material receiver.CS.model_record.CS.record_read with
   | Some sw, Some rr -> SMKM.record_key_iv_material_agrees sw rr
   | _, _ -> False) /\
  SMCan.sent_single_protected_message_seal snap msg raw /\
  (let (ct, frag) = W.serialize_tls_message msg in
   W.parse_tls_message ct frag == Some msg)

(** The seal conjunct proper.  For an in-flight-to-server payload, THREE components,
    all keyed on READABLE fields (the snapshot write epoch and the receiver control):

      * FORWARD (ungated): if the sealing snapshot's write epoch is `Application`
        then the receiver's (server's) read epoch is `Application`.  This is the
        direction consumed at the delivery's NEITHER-APP arm (contrapositive) and by
        `inflight_sender_stepped`'s handshake-exclusion disjunct.

      * CONTROL-GATED BACKWARD: if the receiver's CONTROL is
        `ControlApplicationData` then the snapshot write epoch is `Application`.
        This replaces the old read-epoch biconditional, which was UNSOUND — see
        HISTORY below.  The gate is on the CONTROL because
        `ControlApplicationData` is STRICTLY STRONGER than the app read epoch: the
        epoch survives into `HsServerFinishedVerified` and the entire closure region
        (`fail_model` preserves `model_record`), whereas the control does NOT.  A
        reader must NOT "simplify" this gate back to `R.Application? (rd server)` —
        that reintroduces CE1/CE2 (an alert or Finished payload with the receiver on
        app read keys but the SNAPSHOT still on handshake write keys).

      * BRIDGE, gated on the snapshot write epoch: when `App (snap_wr)`, the bridge
        inputs (`inflight_bridge_ready`: key/iv agreement between the SNAPSHOT write
        material and the receiver read material, single-record seal witness, message
        round-trip) hold.  Snapshot-keyed so that in an alert-inflation window
        (`~App (snap_wr)`, receiver possibly on app read keys) the bridge is simply
        not asserted — protocol-faithful, since a handshake-keyed alert is
        undecryptable to a client on app keys.  The record-seq ALIGNMENT the bridge
        additionally needs is derived at the delivery from `cs_seq_ok`'s gated
        alignment conjunct via `lemma_cs_delivery_alignment`, so it is NOT restated
        here.

    Symmetric for an in-flight-to-client payload.  A `Quiet` channel carries no
    payload, so the conjunct is vacuous — hence trivial at the initial state.

    HISTORY — why the biconditional `App (rd receiver) <==> App (snap_wr)` was
    UNSOUND (do not re-add).  The `<==` (read-epoch backward) direction is false:
    a protected alert is `Application_data`-typed at the wire, a `Sent` alert is
    legal from any control, and epochs are field-keyed and preserved by
    `fail_model`.  So a server at `HsServerFinishedSent` (App read keys installed)
    with a client `Close_notify` sealed on HANDSHAKE write keys in flight has
    `App (rd server)` true and `App (snap_wr)` false — the biconditional's `<==`
    fails.  The fix keeps the FORWARD `App (snap_wr) ==> App (rd receiver)` (sound:
    an app-sealed snapshot forces the receiver onto app read keys via the delivery)
    and replaces the false `<==` with the control-gated backward above, which is the
    direction actually consumed and is closure-safe.  The two delivery consume sites
    branch on `App (snap_wr p)` (readable), NOT on the receiver read epoch.

    HISTORY (do not re-add): this conjunct USED to also carry
    `m_radv server pl_sent == m_wadv snap pl_sent` (a record-COUNT advance
    equality).  That is FALSE at a reachable `ToServer` state — a `Close_notify`
    sent from `ControlApplicationData` (`m_wadv == 1`) in flight to a server that
    took `LocalFail` and is now `ControlFailed` (`m_radv == 0`), the very scenario
    spelled out at `cs_seq_ok` — and it is also UNNECESSARY: the end-to-end goal is
    a byte-stream prefix property, and a `Close_notify` carries no application
    bytes, so the record-count divergence is invisible to it.  The bridge needs
    only key/iv agreement plus the seq alignment (supplied by `cs_seq_ok`), never
    the count equality.

    NOTE (why this is stable and where establishment lives): a `ToServer` channel is
    entered ONLY by `client_send`, and the ONLY family enabled from a non-`Quiet`
    channel is the matching delivery (every send/local gates on `is_quiet`), which
    exits to `Quiet`.  So the SERVER is frozen while `ToServer`, and the three
    components are established at the send and never perturbed until the delivery
    consumes them.  IMPORTANT: `pl_snap` is the PRE-send snapshot (System.fst:826 —
    the channel is `tls_to_server (emitted_raw out) a.client.CS.cs_model sent`, the
    model BEFORE the send mutates it), so a client's atomic app-write-at-Finished-
    send is NOT reflected in `snap_wr`: the client-Finished payload has
    `~App (snap_wr)` even though the post-send client is on app write keys.
    "Atomic at the send" reads as "already in the snapshot" but it is not. **)
let channel_seal_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      // forward (ungated, readable antecedent): a snapshot sealed on app write keys
      // is delivered to a server whose read epoch is Application.
      (R.Application? (snap_wr p).R.epoch ==> R.Application? (rd s.server).R.epoch) /\
      // control-gated backward: keyed on the CONTROL, not the read epoch.  See the
      // doc comment above for why the read-epoch gate (the old biconditional) is
      // UNSOUND (CE1/CE2) and why ControlApplicationData is the right, closure-safe
      // strengthening.
      (CS.ControlApplicationData? (SY.ctrl s.server) ==> R.Application? (snap_wr p).R.epoch) /\
      // bridge, gated on the readable snapshot write epoch.
      (R.Application? (snap_wr p).R.epoch ==>
        inflight_bridge_ready p.SY.pl_snap s.server.CS.cs_model p.SY.pl_sent p.SY.pl_raw)
  | MP.ToClient p ->
      (R.Application? (snap_wr p).R.epoch ==> R.Application? (rd s.client).R.epoch) /\
      (CS.ControlApplicationData? (SY.ctrl s.client) ==> R.Application? (snap_wr p).R.epoch) /\
      (R.Application? (snap_wr p).R.epoch ==>
        inflight_bridge_ready p.SY.pl_snap s.client.CS.cs_model p.SY.pl_sent p.SY.pl_raw)
  | MP.Quiet -> True

(** The full STAGE (b)+(c) extras bundle is defined further down, AFTER the two
    carried in-flight payload facts (`inflight_sender_stepped`,
    `inflight_single_record`) it now includes.  See `app_extras` below. **)

(** ─────────────────────────────────────────────────────────────────────────
    CLIENT-CONTROL RECOVERY HELPERS (client Finished send lands the client at
    `ControlApplicationData`).  Consumed by `lemma_ama_deliver_to_server`'s B2
    branch via `lemma_client_send_installs_app_write_pins` to recover the client
    control at the delivery.  (Formerly the establishment helpers for the retired
    `cf_inflight_client_appdata` conjunct — see git history; that conjunct was a
    Route-X leftover whose control-recovery job is now done by
    `read_write_coupling` + the write pin, so it was dropped.)
    ───────────────────────────────────────────────────────────────────────── **)

(** SPEC-level: a *client* Finished send lands the client at
    `ControlApplicationData`.  A `CL.Sent` Finished steps via
    `step_handshake_message`, whose only two `CL.Sent, M.Finished` arms are at
    `HsServerEncryptedFlightSent` (→ `HsServerFinishedSent`) and
    `HsServerFinishedVerified` (→ `ControlApplicationData`).  Legality at the
    former requires `config_role == ServerEndpoint`; with `ClientEndpoint` only the
    latter is legal, and it sets the control unconditionally. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 30"
let lemma_client_finished_send_lands_appdata
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        M.TlsHandshake? msg /\ M.Finished? (M.TlsHandshake?._0 msg) /\
        CS.legal_tls_message m CL.Sent msg /\
        CS.step_tls_message m CL.Sent msg == Some m')
      (ensures m'.CS.model_control == CS.ControlApplicationData)
  = ()
#pop-options

(** WIRE-level: a client `LocalEvent` send whose event-log delta records
    `SMKM.sent_tls_event sent` pins the model transition to that very message.
    `canonical_wire_step` (inside `client_step`) carries a `legal_connection_delta`
    for some `conn_ev`, which appends `conn_ev` to the event log; list-append
    injectivity against the recorded `sent_tls_event sent` forces
    `conn_ev == sent_tls_event sent`, and the delta then yields the model facts. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_client_send_pins_model
  (st0 c':CS.connection_state)
  (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (sent:M.tls_message)
  : Lemma
      (requires
        EC.client_step st0 (SM.LocalEvent local) c' out /\
        c'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent])
      (ensures
        CS.legal_event st0.CS.cs_model (SMKM.sent_tls_event sent) /\
        CS.step_model st0.CS.cs_model (SMKM.sent_tls_event sent) == Some c'.CS.cs_model)
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      EC.client_representation_matches st0 local conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 c' conn_ev raw_sent B.empty
    with
    (
      // `canonical_wire_step` gives `legal_connection_delta`, hence
      //   c'.cs_event_log == st0.cs_event_log @ [conn_ev].
      // Together with the hypothesis' `@ [sent_tls_event sent]`, append-injectivity
      // on the shared head pins the singleton tails equal.
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent)
    )
#pop-options

(** WIRE-level, SERVER mirror: a server `LocalEvent` send whose event-log delta
    records `SMKM.sent_tls_event sent` pins the model transition to that message.
    Same append-injectivity argument as the client, against the
    `canonical_wire_step` inside `ES.server_step`'s `LocalEvent` arm. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_send_pins_model
  (st0 s':CS.connection_state)
  (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (sent:M.tls_message)
  : Lemma
      (requires
        ES.server_step st0 (SM.LocalEvent local) s' out /\
        s'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent])
      (ensures
        CS.legal_event st0.CS.cs_model (SMKM.sent_tls_event sent) /\
        CS.step_model st0.CS.cs_model (SMKM.sent_tls_event sent) == Some s'.CS.cs_model)
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ES.server_representation_matches local conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty
    with
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent)
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE CLOSING REGION IS ABSORBING (the soundness AND establishment lynchpin of
    the `not_closing` gate).

    Once a connection's control enters `{ControlClosing, ControlClosed,
    ControlFailed}` it never leaves it under ANY legal `step_model`.  Proven from
    the EFFECT functions, not assumed:
      * `ControlFailed` is absorbing by `CSL.lemma_step_model_from_failed_results_failed`.
      * At `ControlClosing`/`ControlClosed`, every handshake/app-data/key-update arm
        of `step_tls_message` is gated on a NON-closing control (so it returns
        `None` there — `step_handshake_message` at `:831`, app-data at `:832`,
        key-update at `:869`), and every LOCAL arm of `step_local_event` is gated on
        `ControlNew`/`ControlHandshaking`/`ControlApplicationData` except
        `LocalFail _ , _` which yields `fail_model` (`ControlFailed`).  The only
        `Some` results are therefore the alert arms `:949` (`Closing`->`Closed`),
        `:961` (`Failed`->`Failed`), and the catch-all `:968` (->`ControlFailed`),
        plus `LocalFail` — all inside the closing region.

    Stated as the contrapositive `not_closing m' ==> not_closing m`, which is the
    form the send/local families consume: if the POST-state left the closing region
    then the PRE-state was already out of it.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_step_preserves_closing (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires CS.step_model m ce == Some m')
      (ensures not_closing m'.CS.model_control ==> not_closing m.CS.model_control)
  = if not_closing m.CS.model_control
    then ()
    else if CS.ControlFailed? m.CS.model_control
    then CSL.lemma_step_model_from_failed_results_failed m ce m'
    else ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE (b) PRESERVATION — the SEND families.

    A `client_send`/`server_send` enters `MP.ToServer`/`MP.ToClient` from a
    `Quiet` pre-state.  The acting endpoint steps by exactly the message it appends
    to its event log (`lemma_*_send_pins_model`), so the epoch-collapsing write
    projection advances by `rin_app` of the freshly-created payload and the read
    projection is unchanged (`lemma_sent_wseq_delta`).  The two send-delta GUARDS
    are discharged HERE:

      * `~M.TlsKeyUpdate? sent` from `SY.tls_no_rekeying b` on the post-state's
        acting endpoint (`lemma_sent_not_key_update`); and
      * `(m_wr …).epoch =!= Application \/ ~M.TlsHandshake? sent`: trivial for a
        non-handshake send, and for a handshake send exactly the new reachable-shape
        extraction lemma `CSL.lemma_{client,server}_handshake_send_write_epoch_not_application`
        (a client/server never sends a handshake once its write epoch is
        Application).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_asp_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b)
      (ensures app_seq_pairing b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    with
    (
      assert (SMCorr.connection_state_no_key_update_trace c');
      lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      // ~KeyUpdate from the post-state's no-rekeying trace.
      lemma_sent_not_key_update c' sent;
      // write-epoch guard: trivial for non-handshake, extraction lemma otherwise.
      (match sent with
       | M.TlsHandshake hm ->
           CSL.lemma_client_handshake_send_write_epoch_not_application a.client c' hm
       | _ -> ());
      lemma_sent_wseq_delta a.client.CS.cs_model c'.CS.cs_model sent;
      // sc-direction: the client is the RECEIVER; if the post-state client is out
      // of the closing region, so was the pre-state client, so `sc_seq_ok a`
      // supplies the pre-state equality that transfers (read seq unchanged).
      lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model
        (CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = sent }))
    )
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_asp_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b)
      (ensures app_seq_pairing b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    with
    (
      assert (SMCorr.connection_state_no_key_update_trace s');
      lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      lemma_sent_not_key_update s' sent;
      (match sent with
       | M.TlsHandshake hm ->
           CSL.lemma_server_handshake_send_write_epoch_not_application a.server s' hm
       | _ -> ());
      lemma_sent_wseq_delta a.server.CS.cs_model s'.CS.cs_model sent;
      // cs-direction: the server is the RECEIVER; closing-region absorption
      // transfers the pre-state equality from `cs_seq_ok a` (read seq unchanged).
      lemma_step_preserves_closing a.server.CS.cs_model s'.CS.cs_model
        (CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = sent }))
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE (b) PRESERVATION — the LOCAL families.

    A `client_local`/`server_local` step is a canonical endpoint step that emits
    NO wire record, so the channel stays `Quiet` and only the acting endpoint's
    model moves.  We must show the epoch-collapsing write/read projections of that
    endpoint are UNCHANGED.

    The step's `conn_ev` has an EMPTY byte-delta on both sides (no wire output ⟹
    `raw_sent` empty; a local step has `raw_received` empty).  Two cases:

      * `ConnLocalEvent lev` — a genuine local event.  Its ONLY writers of
        `model_record` are key installs (`install_record_keys[_for_role]`), legal
        ONLY at `ControlHandshaking`; `R.install_keys` UNCONDITIONALLY resets the
        installed direction's `seq` to 0 (an EFFECT of the install function, not a
        legality side-condition), so POST-install both projections are 0.  For
        preservation we also need the PRE-install projection to be 0 — supplied by
        the reachable handshaking-seq-zero facts
        `CSL.lemma_handshaking_{read,write}_app_seq_zero`.  At `ControlApplicationData`
        a local event is either `LocalDeliverApplicationData` (touches only
        `model_application.app_log`) or `LocalFail` (`fail_model` preserves
        `model_record`); both preserve the projections with no side fact.  This is
        `lemma_step_local_event_preserves_app_seq`.

      * `ConnNetworkEvent dm` with EMPTY byte-delta — IMPOSSIBLE for a protected
        message (`protected_record_count` is always ≥ 1, including a `Sent`
        `TlsApplicationData` whose count `application_data_record_count` is ≥ 1 for
        EVERY payload, empty included: an empty app-data send still emits one
        zero-length record and is therefore a SEND, not a local), so an empty raw
        parses to a nonzero record count and contradicts the empty parse; and for a
        cleartext message the step leaves `model_record` unchanged
        (`SCB.lemma_cleartext_step_record_unchanged`).  Either way the projections
        are unchanged.  This is `lemma_network_empty_delta_record_unchanged_ungated`.

    NOTE (dependence on `tls_no_rekeying`): the LOCAL families do NOT need
    `SY.tls_no_rekeying` — a `KeyUpdate` is a network SEND (protected handshake
    record, non-empty), never a local step, so the key-mutating arm is already
    excluded structurally by the empty byte-delta.  The `KeyUpdate` exclusion via
    `tls_no_rekeying` is only load-bearing for the SEND families.
    ───────────────────────────────────────────────────────────────────────── **)

(** MODEL-LEVEL: a legal local event preserves both epoch-collapsing seq
    projections, GIVEN the handshaking-seq-zero facts (needed only when the
    pre-state is at `ControlHandshaking`, where a key install can reset an
    already-advanced seq). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_step_local_event_preserves_app_seq
  (m m':CS.connection_model) (lev:CS.local_event)
  : Lemma
      (requires
        CS.step_local_event m lev == Some m' /\
        CS.legal_local_event m lev /\
        (CS.ControlHandshaking? m.CS.model_control ==>
           ((m_wr m).R.epoch =!= R.Application \/ (m_wr m).R.seq == 0) /\
           ((m_rd m).R.epoch =!= R.Application \/ (m_rd m).R.seq == 0)))
      (ensures m_wseq m' == m_wseq m /\ m_rseq m' == m_rseq m)
  = ()
#pop-options

(** MODEL-LEVEL: a legal NETWORK step whose byte-delta is empty on both sides
    leaves `model_record` UNCHANGED, at ANY control (no `pre_appdata` gate: an
    empty protected raw is refuted uniformly because `protected_record_count` is
    always ≥ 1). **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60"
let lemma_network_empty_delta_record_unchanged_ungated
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnNetworkEvent dm) /\
        CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
        CS.event_raw_delta_legal m (CS.ConnNetworkEvent dm) B.empty B.empty)
      (ensures m'.CS.model_record == m.CS.model_record)
  = if CS.network_message_is_cleartext dm.CL.message_direction dm.CL.message_value
    then SCB.lemma_cleartext_step_record_unchanged m dm m'
    else begin
      (match dm.CL.message_direction with
       | CL.Sent ->
         (match dm.CL.message_value with
          | M.TlsApplicationData bytes ->
            RF.lemma_application_data_record_count_len_positive (B.length bytes)
          | _ -> ());
         WStep.lemma_ws_raw_records_nonempty_parse_record
           B.empty T.Application_data
           (CS.protected_record_count CL.Sent dm.CL.message_value)
       | CL.Received ->
         WStep.lemma_ws_raw_records_nonempty_parse_record
           B.empty T.Application_data
           (CS.protected_record_count CL.Received dm.CL.message_value))
    end
#pop-options

(** MODEL-LEVEL dispatch: any legal EMPTY-byte-delta step preserves both
    projections.  `ConnLocalEvent` reduces to the local-event lemma; a network
    event with empty delta leaves `model_record` fixed. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_step_empty_delta_preserves_app_seq
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ce /\
        CS.step_model m ce == Some m' /\
        CS.event_raw_delta_legal m ce B.empty B.empty /\
        (CS.ControlHandshaking? m.CS.model_control ==>
           ((m_wr m).R.epoch =!= R.Application \/ (m_wr m).R.seq == 0) /\
           ((m_rd m).R.epoch =!= R.Application \/ (m_rd m).R.seq == 0)))
      (ensures m_wseq m' == m_wseq m /\ m_rseq m' == m_rseq m)
  = match ce with
    | CS.ConnLocalEvent lev ->
      lemma_step_local_event_preserves_app_seq m m' lev
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM (coalesced protected handshake).  Two sub-cases:
         - HEAD: `CS.event_raw_delta_legal` charges a head step
             `raw_records_exactly raw_received Application_data 1`,
           which `B.empty` cannot satisfy -- so this sub-case is refuted by the
           empty-byte-delta hypothesis, exactly as the protected `ConnNetworkEvent`
           sub-case is refuted in `lemma_network_empty_delta_record_unchanged_ungated`.
         - TAIL: charged ZERO bytes, so it really does occur here.  It routes
           through `CS.step_handshake_message m CL.Received msg`, which NEVER
           touches `record_write` on a `CL.Received` arm, so `m_wseq` is immediate.
           For `m_rseq`: on a non-`Finished` message `step_protected_handshake`
           RESTORES `record_read` from the pre-state, so `m_rseq` is unchanged; on
           `Finished` the read direction is `R.install_keys`-ed to the Application
           epoch at seq 0, so `m_rseq m' == 0`, and the pre-state is at
           `ControlHandshaking` (every `legal_handshake_message` arm is), so the
           handshaking-seq-zero hypothesis gives `m_rseq m == 0` too.  This is the
           same argument `lemma_step_local_event_preserves_app_seq` makes for a
           key-installing local event. *)
      if step.CS.protected_handshake_head
      then WStep.lemma_ws_raw_records_nonempty_parse_record B.empty T.Application_data 1
      else ()
    | CS.ConnNetworkEvent dm ->
      lemma_network_empty_delta_record_unchanged_ungated m dm m'
#pop-options

(** WIRE-level: a client `LocalEvent` step emitting NO wire output steps the model
    by SOME `conn_ev` whose byte-delta is empty on both sides.  `raw_sent` is empty
    because `client_wire_outputs_match` ties it to `serialize_all []`; the received
    delta is `B.empty` by construction of a local step. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_local_extract
  (st0 c':CS.connection_state) (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [])
      (ensures
        exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some c'.CS.cs_model /\
          CS.event_raw_delta_legal st0.CS.cs_model ce B.empty B.empty)
  = let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CTy.client_local_event_matches st0 local conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } c' /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    with
    (
      WStep.lemma_serialize_all_nil_wire ();
      Seq.lemma_eq_elim raw_sent B.empty;
      introduce exists (ce:CS.conn_event).
        CS.legal_event st0.CS.cs_model ce /\
        CS.step_model st0.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal st0.CS.cs_model ce B.empty B.empty
      with conn_ev and ()
    )
#pop-options

(** WIRE-level, SERVER mirror. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_local_extract
  (st0 s':CS.connection_state) (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [])
      (ensures
        exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some s'.CS.cs_model /\
          CS.event_raw_delta_legal st0.CS.cs_model ce B.empty B.empty)
  = let api = CTy.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CTy.server_local_event_matches local conn_ev /\
       ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } s' /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    with
    (
      WStep.lemma_serialize_all_nil_wire ();
      Seq.lemma_eq_elim raw_sent B.empty;
      introduce exists (ce:CS.conn_event).
        CS.legal_event st0.CS.cs_model ce /\
        CS.step_model st0.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal st0.CS.cs_model ce B.empty B.empty
      with conn_ev and ()
    )
#pop-options

(** LOCAL family — CLIENT.  Channel stays `Quiet`; the client's projections are
    unchanged; the server is untouched. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_asp_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_local a b)
      (ensures app_seq_pairing b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    with
    (
      lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      with
      (
        (if CS.ControlHandshaking? a.client.CS.cs_model.CS.model_control then begin
           CSL.lemma_handshaking_read_app_seq_zero a.client;
           CSL.lemma_handshaking_write_app_seq_zero a.client
         end);
        lemma_step_empty_delta_preserves_app_seq
          a.client.CS.cs_model c'.CS.cs_model ce;
        // sc-direction: the client is the RECEIVER; closing-region absorption
        // transfers the pre-state equality from `sc_seq_ok a` (read seq frozen).
        lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model ce
      )
    )
#pop-options

(** LOCAL family — SERVER (mirror). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_asp_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_local a b)
      (ensures app_seq_pairing b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    with
    (
      lemma_server_local_extract a.server s' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      with
      (
        (if CS.ControlHandshaking? a.server.CS.cs_model.CS.model_control then begin
           CSL.lemma_handshaking_read_app_seq_zero a.server;
           CSL.lemma_handshaking_write_app_seq_zero a.server
         end);
        lemma_step_empty_delta_preserves_app_seq
          a.server.CS.cs_model s'.CS.cs_model ce;
        // cs-direction: the server is the RECEIVER; closing-region absorption
        // transfers the pre-state equality from `cs_seq_ok a` (read seq frozen).
        lemma_step_preserves_closing a.server.CS.cs_model s'.CS.cs_model ce
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    STAGE (b) PRESERVATION — the DELIVERY family to the SERVER.

    An in-flight-to-server payload is delivered: the server receives the wire
    record, steps by the decoded message `msg`, and the channel returns to `Quiet`.
    We must re-establish `app_seq_pairing` on the post-state.

    NON-CIRCULARITY (the crux of why this is a preservation, not an assumption):
    the induction hypothesis is the STREAM BUNDLE on the PRE-state `a`
    (`app_seq_pairing a`, `channel_seal_ok a`, and the two carried in-flight facts).
    From the pre-state seal we drive the faithful-decode bridge to learn what the
    server just received; the CONCLUSION `app_seq_pairing b` lands on the POST-state.
    The bridge is fed by a pre-state fact and the equality is discharged on the
    post-state, so nothing is assumed about the state we are proving.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** A no-key-update trace whose LAST event RECEIVES `msg` cannot receive a
    `KeyUpdate` — the RECEIVE mirror of `lemma_sent_not_key_update`
    (`conn_event_is_key_update` flags a `TlsKeyUpdate` in EITHER direction). **)
let lemma_recv_not_key_update (st:CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        SMCorr.connection_state_no_key_update_trace st /\
        (exists (prefix:list CS.conn_event).
          st.CS.cs_event_log == prefix @ [SMKM.received_tls_event msg]))
      (ensures ~(M.TlsKeyUpdate? msg))
  = eliminate exists (prefix:list CS.conn_event).
       st.CS.cs_event_log == prefix @ [SMKM.received_tls_event msg]
    with
      lemma_no_key_update_tail prefix (SMKM.received_tls_event msg)

(** A reachable SERVER endpoint is at a server control (grounds the SH/HRR
    exclusion in the not-cleartext helper: those handshake messages are received
    only at CLIENT controls, which `server_ctrl_ok` excludes). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_server_reachable_ctrl_ok
  (cfg:CS.connection_config) (server:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial cfg) server /\
        cfg.CS.config_role == CS.ServerEndpoint)
      (ensures WStep.server_ctrl_ok server.CS.cs_model.CS.model_control)
  = let init : CS.connection_state = CS.initial cfg in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches (WStep.server_sm init) init trace server
    with
      WStep.lemma_server_trace_appdata_post_cf init init server trace
#pop-options

(** A RECEIVED message whose wire record has content type `Application_data` is
    NOT a cleartext record.  For a reachable server the only cleartext RECEIVES are
    a `ClientHello` or a `ChangeCipherSpec` (`WStep.lemma_cleartext_recv_not_appdata`
    shows both parse to a non-`Application_data` outer type — contradiction), and a
    `ServerHello`/`HelloRetryRequest` receive is impossible at any `server_ctrl_ok`
    control (its `step_tls_message` arm is at a client control, so the step is
    `None`). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_recv_msg_not_cleartext
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model) (raw:B.bytes)
  : Lemma
      (requires
        CS.step_tls_message m CL.Received msg == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        WStep.server_ctrl_ok m.CS.model_control /\
        CS.network_message_raw_delta_legal m
          ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw /\
        (match W.parse_record_wire raw with
         | Some (ct, _, _) -> ct == T.Application_data
         | None -> False))
      (ensures CS.network_message_is_cleartext CL.Received msg == false)
  = if CS.network_message_is_cleartext CL.Received msg then
      (match msg with
       | M.TlsHandshake (M.ClientHello _) ->
           WStep.lemma_cleartext_recv_not_appdata m msg raw
       | M.TlsChangeCipherSpec ->
           WStep.lemma_cleartext_recv_not_appdata m msg raw
       | _ -> ())   // ServerHello / HelloRetryRequest: step is None at a server control
    else ()
#pop-options

(** A RECEIVE leaves the epoch-collapsing WRITE projection unchanged: no `Received`
    arm of `step_tls_message` writes `record_write` (message-step key installs are
    all on `record_read`; write installs are LOCAL / on `Sent` arms). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_recv_preserves_write
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m CL.Received msg == Some m')
      (ensures m_wseq m' == m_wseq m)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE TWO CARRIED IN-FLIGHT PAYLOAD FACTS (delivery-time obligations).

    Both are ESTABLISHED at the send (`client_send`/`server_send`) and vacuous on a
    `Quiet` channel; here they are taken as EXPLICIT hypotheses of the delivery
    lemma and wired into the stream bundle as a separate mechanical step.
    ───────────────────────────────────────────────────────────────────────── **)

(** (1) FROZEN SENDER — the in-flight payload's sender snapshot stepped BY exactly
    the sealed message to the (frozen) acting endpoint's current model.  Carrying
    the full `step_tls_message` relation (not the two narrower seq/shape facts)
    mirrors `step_tls_message`'s own dispatch as faithfully as possible.  The two
    send-delta GUARDS (`~KeyUpdate`, and the handshake-write-epoch guard) are folded
    in: both are discharged at the send from `SY.tls_no_rekeying` and the
    reachable-shape `lemma_{client,server}_handshake_send_write_epoch_not_application`. **)
let inflight_sender_stepped (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      CS.step_tls_message p.SY.pl_snap CL.Sent p.SY.pl_sent == Some s.client.CS.cs_model /\
      ~(M.TlsKeyUpdate? p.SY.pl_sent) /\
      ((snap_wr p).R.epoch =!= R.Application \/ ~(M.TlsHandshake? p.SY.pl_sent))
  | MP.ToClient p ->
      CS.step_tls_message p.SY.pl_snap CL.Sent p.SY.pl_sent == Some s.server.CS.cs_model /\
      ~(M.TlsKeyUpdate? p.SY.pl_sent) /\
      ((snap_wr p).R.epoch =!= R.Application \/ ~(M.TlsHandshake? p.SY.pl_sent))
  | MP.Quiet -> True

(** (2) SINGLE RECORD — the sealed payload is exactly one protected record.  For an
    application-data payload this is `application_data_record_count bytes == 1`
    (`protected_record_count CL.Sent`), i.e. `|bytes| <= 16384`.

    WHY IT IS A DELIVERY-TIME OBLIGATION (not baked into `m_wadv`): `m_wadv` mirrors
    the model, and the model's app-data SEND arm (`StateMachine.fst:841`) really does
    advance `record_write` by `application_data_record_count bytes` (possibly >= 2),
    while the RECEIVE arm advances by exactly one `next_seq` (`:851`).  The seal fact
    `sent_single_protected_message_seal` (`Canonical.fst:64`) does NOT bound the
    plaintext length, so it cannot force the count to 1.  It is the SYSTEM-level
    emission interface that rules out a multi-record send: `SY.tls_emit`
    (`System.fst:730`) requires `so_wire_outputs == [w]` (one wire record) and
    `Impl.Client.Types.fst:2087` requires `protected_record_count == 1`.  So this
    fact is established at the send from the emission interface and carried to the
    delivery. **)
let inflight_single_record (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p -> CS.protected_record_count CL.Sent p.SY.pl_sent == 1
  | MP.ToClient p -> CS.protected_record_count CL.Sent p.SY.pl_sent == 1
  | MP.Quiet -> True

(** (3) IN-FLIGHT RAW DELTA LEGALITY — the in-flight wire bytes `pl_raw` are a
    LEGAL ENCODING of the sent message `pl_sent` under the sealing snapshot
    `pl_snap`, i.e. the canonical send-side relation
    `network_message_raw_delta_legal pl_snap {Sent; pl_sent} pl_raw`.  This is the
    RELATION the spec already defines (StateMachine.fst:1493-1507), TOTAL over both
    record classes (cleartext and protected) — NOT a projection of one branch (an
    earlier `~cleartext`-gated `raw_records_exactly` projection was silently vacuous
    on the cleartext branch, which is exactly the load-bearing CCS case).  A
    genuinely DIFFERENT object from `inflight_single_record`, which is about the
    abstract message `pl_sent`, not the wire bytes `pl_raw`.

    This is EXACTLY the send-time fact — it is a conjunct of the send's
    `legal_connection_delta` — so it is definitional at the send and vacuous on
    `Quiet`; carried because nothing in `tls_system_inv` transports the in-flight
    `raw`'s record shape to the delivery (`channel_consistent` is cleartext-hellos
    only).

    WHAT IT GIVES AT A DELIVERY (both branches of `network_message_raw_delta_legal`,
    StateMachine.fst:1493-1507):
      * NON-cleartext `pl_sent`: the else-branch is `raw_records_exactly pl_raw
        Application_data (protected_record_count Sent pl_sent)`, so `pl_raw` parses
        as an `Application_data` record — this is the CCS EXCLUSION for a protected
        handshake payload (`lemma_recv_msg_not_cleartext` needs ONLY this outer type,
        no key/iv material, no seal, no faithful decode; then the option-0 gate
        closes the `+1` enumeration over {EE,Cert,CV}, see `HSP.lemma_hs_recv_plus_one`).
      * cleartext `pl_sent` (e.g. a `ChangeCipherSpec` in flight at a Handshake
        write epoch — model-legal at any `ControlHandshaking`, StateMachine.fst:1432):
        the cleartext branch pins `pl_raw` to the `Change_cipher_spec`-typed record,
        which at the delivery forces the received message to be CCS too (a `+0`
        step), so the send `+0` and receive `+0` MATCH.  Without this branch a
        `~cleartext`-decoded receive of a cleartext-sent record could not be
        excluded.  (Upgraded from a `~cleartext`-gated `raw_records_exactly` to the
        full delta-legal for exactly this cleartext-CCS case.)

    WHY CARRIED (replaces the deleted `HSP.hs_channel_seal_ok` seal): the outer type
    is a SEND-time fact; at a delivery it is otherwise recoverable only by the full
    segmented-replay decomposition of the sender's `raw_sent` log. **)
let inflight_raw_delta_legal (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      CS.network_message_raw_delta_legal p.SY.pl_snap
        ({ CL.message_direction = CL.Sent; CL.message_value = p.SY.pl_sent }) p.SY.pl_raw
  | MP.ToClient p ->
      CS.network_message_raw_delta_legal p.SY.pl_snap
        ({ CL.message_direction = CL.Sent; CL.message_value = p.SY.pl_sent }) p.SY.pl_raw
  | MP.Quiet -> True

(** The full STAGE (b)+(c) extras carried on top of the stream bundle.  Defined
    here (rather than next to the STAGE-(b) send families) because it now folds in
    the two carried in-flight payload facts above. **)
(** ─────────────────────────────────────────────────────────────────────────
    READ/WRITE COUPLING — the cross-endpoint progress conjunct (Route Y).

    The `hello_coupling`-analogue framing (System.fst:330) at the record-epoch
    level: it cannot use `hello_coupling`'s monotone-`Some?` register because the
    fact it carries — a sender snapshot's write epoch — is not a stored-message
    flag but a record-layer position.  For a payload in flight TO THE SERVER, IF
    the server is still in its handshake RECEIVE region (`server_recv_region_ctrl`,
    WireStep.fst:4801 — the controls strictly before the client-Finished delivery,
    INCLUDING `HsServerFinishedSent`), THEN the sealing snapshot's write epoch is
    NOT yet `Application`.

    WHY IT IS TRUE / WHERE IT IS PROVEN: this is an HONEST record-COUNT argument,
    NOT a decode/authenticity fact — a client that has installed its application
    write keys has SENT >= 1 protected record (its Finished), whereas a server still
    in its receive region has RECEIVED 0; byte-pairing right-cancellation then gives
    the contradiction.  It is discharged by
    `ORD.lemma_inflight_sender_write_epoch_not_application_server`
    (Ordering.fst:285), whose author explicitly anticipated THIS conjunct as the
    `inflight_snap_reachable` carrier of its hypotheses.  The full reachable
    snapshot `connection_state` the count lemma needs is available only AT THE
    SEND (the pre-send client), so we invoke the lemma there and carry only its
    EPOCH CONCLUSION — the payload keeps only `pl_snap : connection_model`
    (System.fst:87), which has no `raw_sent`, so the ingredients cannot be carried.

    NON-CIRCULAR: the antecedent reads only `s.server`'s control, never
    `p.pl_sent`, so it is decidable at the delivery without the decode.

    STABILITY: a `ToServer` channel is entered ONLY by `client_send` (establishment)
    and the ONLY family enabled from it is `deliver_to_server`, which exits to
    `Quiet` (Common.SystemProduct.fst:54-60); so the conjunct is non-vacuous only
    in the frozen window and is established once, at the send. **)
let read_write_coupling (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      WStep.server_recv_region_ctrl (SY.ctrl s.server) ==>
        (snap_wr p).R.epoch =!= R.Application
  | _ -> True

(** THE MISSING `server_clean` MIRROR (cross-endpoint appdata-epoch coupling).

    `SY.tls_system_inv` carries `client_clean` (System.fst:589), coupling the
    CLIENT's readiness to the server — but NO `server_clean`.  This conjunct is
    that mirror: each endpoint AT `ControlApplicationData` forces its PEER's
    application WRITE epoch to be installed.

    THE TWO HALVES ARE GATED DIFFERENTLY — read the definition, not the name.
    Conjunct 1 (server @ CAD ==> client's app WRITE installed) is UNGATED: it holds
    at EVERY channel, in flight as well as at `Quiet`.  Conjunct 2 (the mirror) is
    gated on `MP.Quiet?` AND on `~(ControlFailed? (ctrl s.server))`.  The predicate
    was originally named `quiet_appdata_write_coupling` and gated WHOLESALE on
    `MP.Quiet?`; that gate was DROPPED from conjunct 1 (a STRENGTHENING — the
    conjunct now asserts strictly more) and the name changed accordingly, because
    the `Quiet` gate made conjunct 1 UNESTABLISHABLE: both delivery families have a
    NON-`Quiet` pre-state, where a `Quiet`-gated conjunct is vacuous and so carries
    nothing forward into the post-state.

    HOW CONJUNCT 1 IS ESTABLISHED AT THE `deliver_to_server` THAT ENTERS CAD (the
    one non-forwarding case; the "get the fact from the STEP, not the invariant"
    law).  `StateMachine.fst:774` is the unique receive arm producing server-CAD, so
    the delivered message is a `Finished`.  `inflight_sender_stepped` then carries
    `step_tls_message p.pl_snap CL.Sent p.pl_sent == Some s.client.cs_model`, and
    there are exactly TWO `CL.Sent, Finished` step arms: `:676` (-> the SERVER-only
    stage `HsServerFinishedSent`) and `:809` (-> `ControlApplicationData`).
    `SY.client_stage_ok` (a conjunct of `tls_system_inv`, `| _ -> False` on
    server-only stages) kills the first, so the CLIENT'S CONTROL is
    `ControlApplicationData` — derived from the step, needing NO legality and NO
    counting — and `connection_state_consistent` then lifts that to the RECORD-level
    `Application` write epoch.  All five other families merely forward: the sends by
    write-epoch monotonicity, `deliver_to_client` by
    `AMF.lemma_recv_preserves_write_epoch`, `server_local` by CAD-backward,
    `client_local` by `lemma_client_local_preserves_app_write`.

    STATED AT THE EPOCH LEVEL DELIBERATELY (control antecedent, EPOCH consequent).
    A control-level mirror (`peer @ ControlApplicationData`) would COLLAPSE in the
    closure region: `fail_model`/close move the peer OFF `ControlApplicationData`
    to `ControlFailed`/`ControlClosing`, so a control consequent would become
    false there.  The application WRITE epoch, by contrast, PERSISTS: `fail_model`
    (StateMachine.fst:303) preserves `model_record`, and — given
    `SY.tls_no_rekeying` (which excludes the `M.TlsKeyUpdate` re-`install_keys`
    arms) — no step ever un-installs an `Application` epoch.  So the consequent is
    MONOTONE and survives the closure region, which is exactly what lets the two
    LOCAL families preserve it for free and lets the closure-region sends discharge
    it (they leave `ControlApplicationData`, weakening the antecedent).

    WHY CONJUNCT 2 KEEPS BOTH ITS GATES.  Conjunct 2 is
    (I believe) TRUE at a failed server — it is UNDERIVABLE, not false, and the
    distinction matters.  The truth argument: if the client is at
    `ControlApplicationData` and the channel is `Quiet`, the client's Finished was
    SUCCESSFULLY DELIVERED, which required the server to step on it at
    `HsServerFinishedSent` — landing it at `ControlApplicationData` with its
    application WRITE epoch installed (RECORD level).  Only AFTERWARDS can it fail,
    and `fail_model` (StateMachine.fst:303) preserves `model_record` wholesale.  So
    the `Application` write epoch was already installed before the failure and
    survives it.  What is missing is a HISTORY fact — "the server passed through
    `ControlApplicationData`" — which no conjunct of the invariant currently
    carries; `model_record_keys_consistent_for_role` is `| ControlFailed _ -> True`
    (vacuous), so consistency alone gives nothing at a failed server.  Hence the
    gate, which is LEGAL by the gate-monotonicity law because `ControlFailed` alone
    is absorbing (`HSP.lemma_step_control_failed_absorbing`); the finer
    `ControlFailed`-only gate is used in preference to `not terminal_control`
    precisely so the `Closing`/`Closed` branches — which ARE derivable, via
    `CSL.lemma_connection_closing_closed_record_epochs_installed` — are kept.
    The obvious candidate counterexample (deliver the client Finished to an
    ALREADY-`ControlFailed` server) does NOT exist: that delivery hits
    `| _, _ -> None` (StateMachine.fst:970 pre-fix numbering), so the step cannot
    occur and the channel never returns to `Quiet`.  A future strengthening that
    carries the history fact could remove the `ControlFailed` gate.  The `Quiet`
    gate on conjunct 2 is NOT known to be droppable the way conjunct 1's was: the
    `client_clean` route it rests on (System.fst:589) is itself `Quiet`-gated. **)
let appdata_write_coupling (s:SY.tls_system_state) : prop =
  ( (CS.ControlApplicationData? (SY.ctrl s.server) ==>
       R.Application? (wr s.client).R.epoch) /\
    (MP.Quiet? s.channel /\
     CS.ControlApplicationData? (SY.ctrl s.client) /\
     ~(CS.ControlFailed? (SY.ctrl s.server)) ==>
       R.Application? (wr s.server).R.epoch) )

(** GATE 2a conjunct 1 — both-slots gate: the missing `server_clean` mirror of
    the client-side readiness.  Once the CLIENT has verified the server Finished
    and BOTH endpoints hold their `ks_client_handshake_traffic` slot, the two
    slots carry byte-identical record material.  The consume-side spec support is
    the server's protected-Finished open at StateMachine.fst:1375-1377. **)
let hs_material_agreement (s:SY.tls_system_state) : prop =
  ( s.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
    Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
    Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ) ==>
      SMKM.key_schedule_traffic_record_material_agrees
        (SMKI.traffic_id CS.TrafficHandshake CS.ClientTraffic) s.client s.server

(** GATE 2a conjunct 2 — client record<->slot link, gated on the client's
    Handshake WRITE epoch, per-endpoint.  Survives ControlFailed as a carried
    fact (fail_model preserves model_record + hs_keys). **)
let client_hs_write_record_slot_link (s:SY.tls_system_state) : prop =
  R.Handshake? (wr s.client).R.epoch ==>
    SMKM.record_direction_material_matches_key_schedule_for_role
      CS.ClientEndpoint CS.TrafficWrite
      (SMKI.traffic_id CS.TrafficHandshake CS.ClientTraffic) s.client.CS.cs_model

(** GATE conjunct 10 — the FINISHED-DELIVERED application-read coupling: the
    server->client mirror that `channel_seal_ok`'s ToClient FORWARD arm needs, and
    the client->server direction the ToServer forward arm needs.  At a `Quiet`
    channel, if an endpoint has PRODUCED its Finished (a monotone `option`-witness
    on `model_handshake`) then its PEER holds the application READ epoch.

    ANTECEDENT = "peer sent its Finished", NOT "peer holds the App WRITE epoch".
    The App-write gate (the earlier `appwrite_delivered_coupling` shape) is VACUOUS
    exactly at the flip where establishment must happen — the peer's App-write
    installs strictly later (server: the lagging local install at
    `HsServerFinishedSent`, StateMachine.fst:1181; client: atomic at the CF send,
    :809-818) than its Finished-send, so an App-write gate cannot be established at
    the delivery flip.  The `Some? hs_{server,client}_finished` witness IS true at
    the flip and is STRICTLY STRONGER: `App (wr server) ==> Some? hs_server_finished`
    (server installs App-write only at `HsServerFinishedSent`, reached by the SF
    send at StateMachine.fst:685 which sets `hs_server_finished = Some fin`), and
    `App (wr client) ==> Some? hs_client_finished` (atomic — the CF send arm at
    :809-818 sets `hs_client_finished` and installs App-write in ONE transition).
    So this conjunct implies the App-write-gated `channel_seal` forward arms.

    WHY IT HOLDS (the load-bearing step a future reader will challenge).  Consider
    the first half at its establishment, the `deliver_to_client` flip (server SF ->
    client):
      * Finished arm (StateMachine.fst:738): installs `App (rd client)` directly.
      * ALERT arm (:968, the third vector): the ONLY route to a `Quiet` post-state
        with the client NOT on app-read while the server's SF is out.  Excluded by
        FAITHFUL DECODE: the CF ServerTraffic material agreement
        (`HANR.lemma_handshake_server_traffic_key_schedule_material_agrees_nonready_cf`)
        forces the client handshake-READ material == server handshake-WRITE
        material, so the sealed SF opens (open-after-seal, same key) to a Finished,
        never an alert.  This is the sharpened law: the state machine blocks a
        Finished into a failed peer, but only key agreement stops a peer mis-
        decoding an in-flight Finished as an alert.
      * SF into a `ControlFailed` client (failed for other reasons first): the CF
        agreement STILL holds (it is control-free), so the wire still decodes to a
        Finished, and a Finished into `ControlFailed` BLOCKS (:822 fallthrough) ->
        delivery incomplete -> channel stays `ToClient` -> not `Quiet` -> vacuous.
      * `ks_master_secret == None`: the Finished arm blocks (:738 install-or-block)
        -> not `Quiet` -> vacuous.
      * After establishment: App-read epochs are MONOTONE under `tls_no_rekeying`;
        `fail_model` preserves `model_record` (epochs) and `model_handshake`
        (witnesses).  So no reachable `Quiet` state violates it.

    ROLE RESTRICTIONS ARE LOAD-BEARING for the two LOCAL families.  The witness
    `s.server.hs_server_finished` is set only by the server SEND (:685); the local-
    verify route (:556, `LocalVerifyFinished`) that also sets `hs_server_finished`
    is CLIENT-ROLE-ONLY (`config_role == ClientEndpoint`, StateMachine.fst:1272), so
    a `server_local` cannot flip it and a `client_local` touches only client fields.
    Symmetrically `s.client.hs_client_finished` is set only by the client SEND
    (:818); the local-verify route (:567, `LocalVerifyClientFinished`) is SERVER-
    ROLE-ONLY (:1279), so a `client_local` cannot flip it.  (The non-atomic verify
    routes at `HsServerFinishedReceived`/`HsClientFinishedReceived` reach the flip
    stage WITHOUT installing app-read, but those stages have NO transition into them
    and are dead; we do not rely on that reachability grep — the role restriction
    kills the arm outright.)

    PER-HALF IN-FLIGHT GATING (not a plain `Quiet ==>`).  Each half is gated to
    exclude ONLY the channel direction that carries ITS OWN sender's in-flight
    Finished: the first half (server SF -> client) is gated `~ToClient`, the second
    (client CF -> server) `~ToServer`.  A plain `Quiet` gate makes the WHOLE
    conjunct vacuous at every in-flight state, so at a `deliver_to_client`
    (`ToClient -> Quiet`) the PASSIVE second half could not be carried from the
    pre-state.  With per-half gating, at a delivery the passive half is ACTIVE in
    the pre-state (a `ToClient` pre-state satisfies `~ToServer`, keeping the second
    half live) and is preserved verbatim, while the delivery's OWN half is
    established fresh by faithful decode.  This is strictly STRONGER than the
    `Quiet`-gated form and COINCIDES with it at `Quiet` (where both `~ToClient` and
    `~ToServer` hold), so every consumer — which reads the conjunct only at `Quiet`
    send pre-states — is unaffected.  Each half genuinely holds in its active region:
    it fails only while its sender's Finished is in flight, which is exactly the
    excluded direction. **)
let finished_delivered_appread_coupling (s:SY.tls_system_state) : prop =
  ( ~(MP.ToClient? s.channel) ==>
      (Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==>
         R.Application? (rd s.client).R.epoch) ) /\
  ( ~(MP.ToServer? s.channel) ==>
      (Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
         R.Application? (rd s.server).R.epoch) )

(** (12) IN-FLIGHT SNAPSHOT HANDSHAKE-WRITE EPOCH — for a PROTECTED (non-cleartext)
    handshake message in flight TO THE CLIENT, the sealing snapshot's write record is
    at the `Handshake` epoch.

    WHY IT IS A CARRIED FACT (establish-then-consume, like `inflight_raw_delta_legal`
    and the seq-alignment arm): `Handshake?(snap_wr)` is PROVABLE AT THE SEND but
    UNDERIVABLE AT THE DELIVERY.  At the send the pre-send server `= pl_snap` sits at
    `HsServerHelloSent` (EE) / `HsServerEncryptedFlightSent` (Cert/CV/SF) — inside the
    `lemma_server_handshake_write_record_has_keys` region — so has-keys (=> `Some?
    write.key`) + `lemma_server_handshake_send_write_epoch_not_application` (=> `~App`)
    + `RKE.lemma_connection_consistent_write_key_present_not_initial` (=> `~Initial`)
    give `Handshake?`.  At the DELIVERY the snapshot's `connection_state` is
    unreconstructable — the payload carries only `pl_snap : connection_model`, no
    `raw_sent` (System.fst:87; see the `read_write_coupling` doc comment) — and the
    model-level facts permit a `~Handshake(snap_wr)` "garbage-raw" reading (the
    protected branch of `network_message_raw_delta_legal` is only `raw_records_exactly
    raw Application_data count`, tying `raw` to no seal), so the fact MUST be carried,
    not re-derived.

    NON-CIRCULAR: established at the send with NO appeal to decode; consumed at the
    delivery to DISCHARGE the `Handshake?(snap_wr)` half of `hs_channel_seal_ok`'s
    bridge gate (the receiver-read half comes from `RKE` off the delivery's own
    protected-decode).  Guard is `TlsHandshake?` AND `~cleartext`: a
    ClientHello/ServerHello send is cleartext (Initial write, excluded); an
    app-data/KeyUpdate send is not `TlsHandshake?` (its App/Application write is
    excluded) — leaving exactly the EE/Cert/CV/Finished flight, all at Handshake write.

    TOSERVER ARM (symmetric).  The client's ONLY protected handshake send is its
    Finished, from `ControlHandshaking HsServerFinishedVerified` (ClientHello and
    CCS are cleartext, hence excluded by the `~cleartext` guard; every other client
    `Sent` handshake message has no legal arm).  Establishment at that send is the
    exact mirror of the server side, and rests on the RECORD-LEVEL conjunct
    `Some? model_record.record_write.R.key` that the `Sent/Finished/
    HsServerFinishedVerified` arm of `legal_tls_message` now demands (see the
    "Stream-integrity fix (RECORD level, not slot level)" comment there).  That
    conjunct is LOAD-BEARING here and cannot be replaced by the arm's SLOT-level
    `Some? ks_client_handshake_traffic`: the client's handshake-WRITE record
    install is an OPTIONAL local, so slot presence does not imply record-key
    presence (the SLOT vs RECORD law).  With it,
    `lemma_client_finished_verified_write_epoch_handshake` (which needs exactly
    `Some? record_write.key`) plus
    `RKE.lemma_connection_consistent_write_key_present_not_initial` give
    `Handshake?` on the snapshot write.  Consumed at the delivery to discharge the
    snapshot half of `hs_channel_seal_ok`'s ToServer bridge gate. **)
let inflight_snap_handshake_write (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToClient p ->
      (M.TlsHandshake? p.SY.pl_sent /\
       ~(CS.network_message_is_cleartext CL.Sent p.SY.pl_sent)) ==>
        R.Handshake? (snap_wr p).R.epoch
  | MP.ToServer p ->
      (M.TlsHandshake? p.SY.pl_sent /\
       ~(CS.network_message_is_cleartext CL.Sent p.SY.pl_sent)) ==>
        R.Handshake? (snap_wr p).R.epoch
  | _ -> True

let app_extras (s:SY.tls_system_state) : prop =
  app_seq_pairing s /\
  app_material_agreement s /\ channel_seal_ok s /\
  inflight_sender_stepped s /\ inflight_single_record s /\
  inflight_raw_delta_legal s /\
  inflight_snap_handshake_write s /\
  read_write_coupling s /\
  appdata_write_coupling s /\
  hs_material_agreement s /\
  client_hs_write_record_slot_link s /\
  finished_delivered_appread_coupling s

(** Initial state: both record epochs are `Initial`, so `cf_delivered` is false
    and the agreement is vacuous; `app_seq_pairing` was shown initial above; and
    the initial channel is `Quiet`, so the two in-flight facts are vacuous. **)
let lemma_initial_app_extras (cfg_c cfg_s:CS.connection_config)
  : Lemma (app_extras (SY.initial_tls_system cfg_c cfg_s))
  = ()

(** A `Quiet` channel carries no in-flight payload, so both carried facts hold
    vacuously.  This is what the LOCAL and DELIVERY families discharge (their
    post-states are `Quiet`). **)
let lemma_quiet_inflight_vacuous (s:SY.tls_system_state)
  : Lemma (requires MP.Quiet? s.channel)
          (ensures inflight_sender_stepped s /\ inflight_single_record s /\
                   inflight_raw_delta_legal s)
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT of `inflight_single_record` at the send.

    `protected_record_count CL.Sent` is `1` for every message EXCEPT a
    `Sent, TlsApplicationData bytes`, where it is `application_data_record_count
    bytes` (possibly >= 2) — the model's app-data SEND arm really does allow a
    multi-record send.  The count-1 obligation is therefore a genuine SYSTEM-level
    fact recovered from the emission interface: the send emits exactly ONE wire
    record `w`, and a legal Sent-app-data delta is `raw_records_exactly raw
    Application_data count`.  Since `w` is one FULL wire record
    (`w.wm_parse_ok`), the nonempty first parse of `raw` consumes all of it, so
    `raw_records_exactly raw Application_data 1` also holds — and
    `raw_records_exactly` pins `length (parse_record_prefix raw).values` to BOTH
    counts, forcing `count == 1`.  (This is NOT baked into `m_wadv`, which mirrors
    the model and must stay faithful to the multi-record send arm.) **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80"
let lemma_send_single_record_count
  (m:CS.connection_model) (sent:M.tls_message) (w:CW.wire_message) (raw:B.bytes)
  : Lemma
      (requires
        Seq.equal raw (CW.wire_serialize w) /\
        CS.network_message_raw_delta_legal m
          ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw)
      (ensures CS.protected_record_count CL.Sent sent == 1)
  = match sent with
    | M.TlsApplicationData bytes ->
        let count = RF.application_data_record_count bytes in
        RF.lemma_application_data_record_count_len_positive (B.length bytes);
        // App-data is NOT cleartext, so the legal delta is exactly
        //   raw_records_exactly raw Application_data count.
        assert (CS.raw_records_exactly raw T.Application_data count);
        // `raw` is one full wire record (`w.wm_parse_ok`).
        Seq.lemma_eq_elim raw (CW.wire_serialize w);
        let _pk = w.CW.wm_parse_ok in
        assert (W.parse_record_wire raw ==
                  Some (w.CW.wm_content_type, w.CW.wm_fragment, B.length raw));
        WStep.lemma_ws_raw_records_nonempty_parse_record raw T.Application_data count;
        eliminate exists (fragment:M.sealed_record) (consumed:nat).
          W.parse_record raw == Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\ consumed <= B.length raw
        with
        (
          // parse_record -> parse_record_wire agreement: the third component
          // (consumed) must equal `B.length raw` by injectivity of `Some`.
          W.lemma_parse_record_implies_parse_record_wire raw;
          assert (consumed == B.length raw);
          CSL.lemma_parse_record_full_raw_records_exactly raw T.Application_data fragment;
          assert (CS.raw_records_exactly raw T.Application_data 1)
        )
    | _ -> ()
#pop-options

(** ESTABLISHMENT of `inflight_raw_delta_legal`'s outer-type fact.  For a NON-cleartext
    send, `network_message_raw_delta_legal m {Sent; sent} raw` IS (by the else-branch,
    StateMachine.fst:1503-1507) `raw_records_exactly raw Application_data
    (protected_record_count Sent sent)`, so the guarded conclusion is definitional. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_send_record_shape
  (m:CS.connection_model) (sent:M.tls_message) (w:CW.wire_message) (raw:B.bytes)
  : Lemma
      (requires
        Seq.equal raw (CW.wire_serialize w) /\
        CS.network_message_raw_delta_legal m
          ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw)
      (ensures
        ~(CS.network_message_is_cleartext CL.Sent sent) ==>
          CS.raw_records_exactly raw T.Application_data
            (CS.protected_record_count CL.Sent sent))
  = ()
#pop-options

(** Extract the count-1 fact from a CLIENT send: `client_step`'s
    `canonical_wire_step` carries a `legal_connection_delta` whose Sent-arm gives
    `network_message_raw_delta_legal` on the emitted `raw_sent`, which equals the
    single wire record `w`'s bytes. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 60"
let lemma_client_send_count
  (st0 c':CS.connection_state)
  (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        EC.client_step st0 (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        c'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent])
      (ensures CS.protected_record_count CL.Sent sent == 1 /\
               (~(CS.network_message_is_cleartext CL.Sent sent) ==>
                  CS.raw_records_exactly (SY.emitted_raw out) T.Application_data
                    (CS.protected_record_count CL.Sent sent)) /\
               CS.network_message_raw_delta_legal st0.CS.cs_model
                 ({ CL.message_direction = CL.Sent; CL.message_value = sent })
                 (SY.emitted_raw out))
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      EC.client_representation_matches st0 local conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 c' conn_ev raw_sent B.empty
    with
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      SY.lemma_serialize_all_single w;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
      lemma_send_single_record_count st0.CS.cs_model sent w raw_sent;
      lemma_send_record_shape st0.CS.cs_model sent w raw_sent
    )
#pop-options

(** Server mirror of `lemma_client_send_count`. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 60"
let lemma_server_send_count
  (st0 s':CS.connection_state)
  (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        ES.server_step st0 (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        s'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent])
      (ensures CS.protected_record_count CL.Sent sent == 1 /\
               (~(CS.network_message_is_cleartext CL.Sent sent) ==>
                  CS.raw_records_exactly (SY.emitted_raw out) T.Application_data
                    (CS.protected_record_count CL.Sent sent)) /\
               CS.network_message_raw_delta_legal st0.CS.cs_model
                 ({ CL.message_direction = CL.Sent; CL.message_value = sent })
                 (SY.emitted_raw out))
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ES.server_representation_matches local conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty
    with
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      SY.lemma_serialize_all_single w;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
      lemma_send_single_record_count st0.CS.cs_model sent w raw_sent;
      lemma_send_record_shape st0.CS.cs_model sent w raw_sent
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT of BOTH in-flight facts at the SEND families.  Same eliminate
    shape as `lemma_asp_client_send`/`lemma_asp_server_send`: the send enters
    `MP.ToServer`/`MP.ToClient` from `Quiet`.  `inflight_sender_stepped` is the
    same three facts those families already discharge (frozen step + the two
    send-delta guards); `inflight_single_record` is `lemma_{client,server}_send_count`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_asp_client_send_inflight (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b)
      (ensures inflight_sender_stepped b /\ inflight_single_record b /\
               inflight_raw_delta_legal b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    with
    (
      assert (SMCorr.connection_state_no_key_update_trace c');
      lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      lemma_sent_not_key_update c' sent;
      (match sent with
       | M.TlsHandshake hm ->
           CSL.lemma_client_handshake_send_write_epoch_not_application a.client c' hm
       | _ -> ());
      lemma_client_send_count a.client c' local out w sent
    )
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_asp_server_send_inflight (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b)
      (ensures inflight_sender_stepped b /\ inflight_single_record b /\
               inflight_raw_delta_legal b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    with
    (
      assert (SMCorr.connection_state_no_key_update_trace s');
      lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      lemma_sent_not_key_update s' sent;
      (match sent with
       | M.TlsHandshake hm ->
           CSL.lemma_server_handshake_send_write_epoch_not_application a.server s' hm
       | _ -> ());
      lemma_server_send_count a.server s' local out w sent
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT of `inflight_snap_handshake_write` at the CLIENT send (ToServer
    arm).  Mirror of the server lemma below.  The client's only NON-cleartext
    handshake send is its Finished: `ClientHello` is cleartext (guard false),
    `ServerHello` is cleartext too, `EncryptedExtensions`/`Certificate`/
    `CertificateVerify` have only `ServerEndpoint` `Sent` arms, and `Sent`
    `HelloRetryRequest` has no arm at all (the step would be `None`, contradicting
    `Some c'`).  So the pre-send client sits at `ControlHandshaking
    HsServerFinishedVerified`, where the RECORD-LEVEL legality conjunct hands us
    `Some? record_write.R.key` directly; `lemma_client_finished_verified_write_
    epoch_handshake` then gives `Handshake?`.  (`RKE` and the not-application
    lemma are cited for symmetry with the server route and to keep the proof
    robust to the exact shape of the client-Finished epoch lemma.)
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 60"
let lemma_asp_client_send_snap_handshake_write (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b)
      (ensures inflight_snap_handshake_write b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    with
    (
      lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      (match sent with
       | M.TlsHandshake hm ->
           (match hm with
            | M.Finished _ ->
                CSL.lemma_client_handshake_send_write_epoch_not_application a.client c' hm;
                assert (a.client.CS.cs_model.CS.model_control ==
                          CS.ControlHandshaking CS.HsServerFinishedVerified);
                // RECORD level (not slot level): supplied by the strengthened
                // `Sent/Finished/HsServerFinishedVerified` arm of `legal_tls_message`.
                assert (Some? a.client.CS.cs_model.CS.model_record.CS.record_write.R.key);
                RKE.lemma_connection_consistent_write_key_present_not_initial a.client;
                CSL.lemma_client_finished_verified_write_epoch_handshake a.client
            | _ -> ())
       | _ -> ())
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT of `inflight_snap_handshake_write` at the SERVER send (ToClient
    arm).  Same eliminate shape as `lemma_asp_server_send_inflight`.  For a
    non-cleartext handshake message (EE/Cert/CV/Finished) the pre-send server sits
    at `HsServerHelloSent` (EE) or `HsServerEncryptedFlightSent` (Cert/CV/SF) — both
    in the `has_keys` region — so has-keys + not-application + `RKE` give the
    `Handshake?` write epoch.  ServerHello is cleartext (guard false); no Sent HRR
    arm exists (the step would be `None`, contradicting `Some s'`).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 60"
let lemma_asp_server_send_snap_handshake_write (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b)
      (ensures inflight_snap_handshake_write b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    with
    (
      lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      (match sent with
       | M.TlsHandshake hm ->
           (match hm with
            | M.EncryptedExtensions _
            | M.Certificate _
            | M.CertificateVerify _
            | M.Finished _ ->
                CSL.lemma_server_handshake_send_write_epoch_not_application a.server s' hm;
                assert (a.server.CS.cs_model.CS.model_control ==
                          CS.ControlHandshaking CS.HsServerHelloSent \/
                        a.server.CS.cs_model.CS.model_control ==
                          CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
                assert (Some? a.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
                CSL.lemma_server_handshake_write_record_has_keys a.server;
                assert (Some? a.server.CS.cs_model.CS.model_record.CS.record_write.R.key);
                RKE.lemma_connection_consistent_write_key_present_not_initial a.server
            | _ -> ())
       | _ -> ())
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_asp_deliver_to_server
  (a:SY.tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        app_extras a /\
        a.channel == SY.tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
        SY.tls_no_rekeying ({ a with server = s'; channel = MP.Quiet }))
      (ensures app_seq_pairing ({ a with server = s'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with server = s'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
    // Unfold the extras bundle to recover the four facts this body consumes.
    assert (app_seq_pairing a /\ channel_seal_ok a /\
            inflight_sender_stepped a /\ inflight_single_record a);
    assert (a.channel == MP.ToServer p);
    // Reachable server -> server_ctrl_ok (grounds the SH/HRR exclusion in the
    // not-cleartext helper).
    lemma_server_reachable_ctrl_ok a.server.CS.cs_model.CS.model_config a.server;
    eliminate exists (msg:M.tls_message).
      (let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
       CS.legal_connection_delta a.server
         { CS.delta_event = conn_ev;
           CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire } s' /\
       SMCan.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    with
    (
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
      // The model step the server just took: step_tls_message ... Received msg.
      assert (CS.step_tls_message a.server.CS.cs_model CL.Received msg == Some s'.CS.cs_model);
      // ~KeyUpdate(msg) from the post-state's no-rekeying trace (its event log ends
      // with `received_tls_event msg`).
      lemma_recv_not_key_update s' msg;
      // sc-direction (server writes, client reads): a RECEIVE freezes the server's
      // WRITE projection, and the client is untouched, so `sc_seq_ok a` transfers.
      lemma_recv_preserves_write a.server.CS.cs_model s'.CS.cs_model msg;
      // cs-direction (client writes, server reads): the gated alignment.  When the
      // POST-state server is live, the PRE-state server was live too (closing region
      // is absorbing), so `cs_seq_ok a` supplies the pre-state seq equality.
      introduce not_closing (SY.ctrl s') ==> app_wseq a.client == app_rseq s'
      with
      (
        lemma_step_preserves_closing a.server.CS.cs_model s'.CS.cs_model conn_ev;
        // EQ_pre : snap_app_wseq p == app_rseq a.server   (cs_seq_ok a, ToServer p, live)
        // send delta : app_wseq a.client == snap_app_wseq p + rin_app p
        lemma_sent_wseq_delta snap a.client.CS.cs_model sent;
        if R.Application? (snap_wr p).R.epoch then
        (
          // App(snap_wr) BRANCH (was BOTH-APP).  channel_seal_ok a's FORWARD gives
          // App(rd a.server); its snapshot-keyed bridge fires; EQ_pre (both App)
          // gives the seq alignment.  The faithful-decode bridge (fed by the
          // PRE-state seal — non-circular) pins what the server received.
          assert (R.Application? (rd a.server).R.epoch);   // forward, from App(snap_wr)
          CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
            snap a.server.CS.cs_model sent raw;
          // FINDING-1 HINGE: the bridge is invoked only here, where the server's read
          // epoch is Application, hence the server is not handshaking on a cleartext
          // record; the received wire record is Application_data-typed, so the
          // received message is not cleartext and the projection yields its decode.
          lemma_recv_msg_not_cleartext a.server.CS.cs_model msg s'.CS.cs_model raw;
          lemma_decode_functional a.server.CS.cs_model msg sent raw;
          // msg == sent; the receive delta needs ~Handshake(msg) (from msg == sent an
          // app-data payload) and ~KeyUpdate(msg) (already have).
          lemma_recv_rseq_delta a.server.CS.cs_model s'.CS.cs_model msg;
          // COUNT-MATCH : m_wadv snap sent == m_radv a.server msg.
          (match sent with
           | M.TlsApplicationData bts ->
               // both steps force ControlApplicationData; single-record: the send
               // advance is `application_data_record_count bts == 1`.
               ()
           | M.TlsAlert T.Close_notify ->
               // a received Close_notify lands the server in the closing region,
               // contradicting the live branch — vacuous.
               ()
           | _ -> ())
        )
        else
        (
          // ~App(snap_wr) BRANCH (was NEITHER-APP).  LHS `app_wseq a.client == 0`
          // (snap_app_wseq p == 0 and rin_app p == 0, both by ~App(snap_wr)).  For
          // the RHS: the control-gated backward (channel_seal_ok a, ToServer p)
          // CONTRAPOSITIVE gives ~ControlApplicationData?(ctrl a.server), and
          // `_live` + `lemma_step_preserves_closing` gives not_closing(ctrl
          // a.server) hence ~ControlClosing?.  Off both controls a receive advances
          // the read seq by 0 (`lemma_m_radv_zero_non_cad_closing`), and the delta
          // lemma's Handshake precondition is discharged by `lemma_recv_precond`
          // (single-endpoint enumeration, needs no read-epoch knowledge).  With
          // `m_rseq a.server == 0` from EQ_pre + ~App(snap_wr), `app_rseq s' == 0`.
          //
          // The residue this closes: a HANDSHAKE payload with ~App(snap_wr) whose
          // receive moves the read projection.  The read projection can move only two
          // ways, and both self-discharge: either the receiver was ALREADY on app
          // read keys (Case A: impossible — every handshake-receive control is
          // handshaking-nonfinal, so `lemma_handshaking_nonfinal_read_not_application`
          // inside `lemma_recv_precond` forces ~App(rd), and here `m_radv == 0`
          // anyway off {CAD,Closing}); or the receive INSTALLS app read keys (Case B:
          // `install_keys` (TLS13.Record.Spec.fst:31) zeroes the seq, so the read
          // projection posts 0).  There is no third way for `app_rseq` to exceed 0
          // after a handshake delivery, which is why no cross-endpoint content is
          // needed here.
          assert (~(CS.ControlApplicationData? (SY.ctrl a.server)));  // control-gated backward
          lemma_recv_precond a.server s' msg;
          lemma_recv_rseq_delta a.server.CS.cs_model s'.CS.cs_model msg;
          lemma_m_radv_zero_non_cad_closing a.server.CS.cs_model msg
        )
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE CLIENT NOT-CLEARTEXT HELPER (bridge-first, client mirror of
    `lemma_recv_msg_not_cleartext`).

    A RECEIVED message whose wire record has content type `Application_data` is NOT
    a cleartext record, for a reachable CLIENT whose READ epoch is `Application`.

    The client is NOT symmetric to the server here, and that is the whole reason a
    separate helper (and the new spec lemma) exists.  On the server side, the four
    cleartext receives were excluded either by a raw-type contradiction
    (`ClientHello`/`ChangeCipherSpec`) or by `server_ctrl_ok`
    (`ServerHello`/`HelloRetryRequest` are received only at CLIENT controls, so the
    step is `None`).  A client, by contrast, LEGITIMATELY receives
    `ServerHello`/`HelloRetryRequest`, so `server_ctrl_ok` has no mirror.  But those
    two are received ONLY at `HsClientHelloSent` (`step_tls_message` has no other
    `Received` arm for them), a NON-FINAL handshaking control that
    `CSL.lemma_handshaking_nonfinal_read_not_application` places OFF the
    `Application` read epoch — contradicting the both-application hypothesis under
    which this helper is invoked.  So they are discharged by read-epoch placement,
    with NO wire-length bound (which the serialize/parse roundtrip of a
    `ServerHello` would otherwise demand).  `ClientHello`/`ChangeCipherSpec` are
    excluded by the same raw-type contradiction as on the server. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_client_recv_msg_not_cleartext
  (client:CS.connection_state) (msg:M.tls_message) (m':CS.connection_model) (raw:B.bytes)
  : Lemma
      (requires
        CS.step_tls_message client.CS.cs_model CL.Received msg == Some m' /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        SMR.connection_state_consistent client /\
        R.Application? (rd client).R.epoch /\
        CS.network_message_raw_delta_legal client.CS.cs_model
          ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw /\
        (match W.parse_record_wire raw with
         | Some (ct, _, _) -> ct == T.Application_data
         | None -> False))
      (ensures CS.network_message_is_cleartext CL.Received msg == false)
  = if CS.network_message_is_cleartext CL.Received msg then
      (match msg with
       | M.TlsHandshake (M.ClientHello _) ->
           WStep.lemma_cleartext_recv_not_appdata client.CS.cs_model msg raw
       | M.TlsChangeCipherSpec ->
           WStep.lemma_cleartext_recv_not_appdata client.CS.cs_model msg raw
       | _ ->
           // ServerHello / HelloRetryRequest: the ONLY `Received` arm of
           // `step_tls_message` for either is at `HsClientHelloSent`, so step-success
           // pins the control there — a non-final handshaking control, off the
           // Application read epoch by the new spec lemma, contradicting the App-read
           // hypothesis of the both-application branch.  No length bound needed.
           assert (client.CS.cs_model.CS.model_control ==
                     CS.ControlHandshaking CS.HsClientHelloSent);
           CSL.lemma_handshaking_nonfinal_read_not_application client)
    else ()
#pop-options

(** MODEL-LEVEL: the seq effect of a legal `ConnProtectedHandshake` step (the
    coalesced-protected-flight event agentic added to `CS.conn_event`).

    `CS.step_protected_handshake` routes through
    `CS.step_handshake_message m CL.Received msg`, and NO `CL.Received` arm of
    `step_handshake_message` touches `record_write` -- hence `m_wseq` is frozen,
    exactly as for a received network message (`lemma_recv_preserves_write`).

    For the READ side: the four supported messages are
    `EncryptedExtensions | Certificate | CertificateVerify | Finished`.  The first
    three advance `record_read` by `R.next_seq`, which PRESERVES the epoch, so a
    non-Application read epoch stays non-Application and the projection stays 0.
    `Finished` is the atomic install arm: `record_read` becomes
    `R.install_keys ... R.Application ...`, i.e. the Application epoch at seq 0,
    so the projection is again 0.  (On a TAIL step the non-`Finished` cases
    additionally RESTORE `record_read` from the pre-state, which only makes the
    conclusion easier.) **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 100"
let lemma_protected_step_seq
  (m m':CS.connection_model) (step:CS.protected_handshake_step)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnProtectedHandshake step) /\
        CS.step_model m (CS.ConnProtectedHandshake step) == Some m' /\
        (m_rd m).R.epoch =!= R.Application)
      (ensures m_wseq m' == m_wseq m /\ m_rseq m' == 0 /\ m_rseq m == 0)
  = ()
#pop-options

(** The control of a client taking a legal protected-handshake step is one of the
    four `legal_handshake_message` RECEIVE controls, none of which is
    `HsServerFinishedVerified` or `HsClientFinishedReceived` -- so
    `CSL.lemma_handshaking_nonfinal_read_not_application` applies and the client's
    READ epoch is NOT `Application`. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 100"
let lemma_protected_step_read_not_application
  (st:CS.connection_state) (step:CS.protected_handshake_step)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        CS.legal_event st.CS.cs_model (CS.ConnProtectedHandshake step))
      (ensures (rd st).R.epoch =!= R.Application)
  = if step.CS.protected_handshake_buffering
    then
      (* A BUFFERING step carries no message -- it sets a record's plaintext
         aside so a handshake message spanning several records can be
         reassembled -- so [legal_handshake_message] says nothing about it and
         its [protected_handshake_message] field is inert.  Legality instead
         pins the control to one of the four [protected_handshake_buffering_stage]
         stages (HsServerHelloReceived, HsEncryptedExtensionsReceived,
         HsCertificateValidated, HsCertificateVerifyVerified).  None of those
         is HsServerFinishedVerified or HsClientFinishedReceived, so the same
         placement argument still gives a non-Application read epoch. *)
      begin
        assert (CS.ControlHandshaking? st.CS.cs_model.CS.model_control);
        assert (st.CS.cs_model.CS.model_control
                  =!= CS.ControlHandshaking CS.HsServerFinishedVerified);
        assert (st.CS.cs_model.CS.model_control
                  =!= CS.ControlHandshaking CS.HsClientFinishedReceived);
        CSL.lemma_handshaking_nonfinal_read_not_application st
      end
    else
      begin
        assert (CS.legal_handshake_message st.CS.cs_model CL.Received
                  step.CS.protected_handshake_message);
        assert (CS.ControlHandshaking? st.CS.cs_model.CS.model_control);
        assert (st.CS.cs_model.CS.model_control
                  =!= CS.ControlHandshaking CS.HsServerFinishedVerified);
        assert (st.CS.cs_model.CS.model_control
                  =!= CS.ControlHandshaking CS.HsClientFinishedReceived);
        CSL.lemma_handshaking_nonfinal_read_not_application st
      end
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    STAGE (b) PRESERVATION — DELIVERY TO CLIENT (mirror of `lemma_asp_deliver_to_server`).

    A `deliver_to_client` consumes an in-flight `MP.ToClient` payload (sealed by the
    SERVER) and steps the CLIENT by the message it decodes to.  As on the server
    side the proof is NON-CIRCULAR: the faithful-decode bridge is fed by the
    PRE-state seal (`channel_seal_ok a`, `sc_seq_ok a`, and the two carried in-flight
    facts), and the CONCLUSION `app_seq_pairing b` lands on the POST-state.

    The mirror is NOT a syntactic dual: the gated direction is now `sc_seq_ok`
    (server writes -> client reads), and the not-cleartext hinge cannot reuse the
    server's `lemma_recv_msg_not_cleartext` (which grounds the SH/HRR exclusion in
    `server_ctrl_ok`, absent for a client that legitimately receives them).  It uses
    the client helper above instead, which excludes SH/HRR by read-epoch placement.
    ═══════════════════════════════════════════════════════════════════════════ **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_asp_deliver_to_client
  (a:SY.tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        app_extras a /\
        a.channel == SY.tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
        SY.tls_no_rekeying ({ a with client = c'; channel = MP.Quiet }))
      (ensures app_seq_pairing ({ a with client = c'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with client = c'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
    // Unfold the extras bundle to recover the four facts this body consumes.
    assert (app_seq_pairing a /\ channel_seal_ok a /\
            inflight_sender_stepped a /\ inflight_single_record a);
    assert (a.channel == MP.ToClient p);
    EC.lemma_client_wire_step_inversion #CTy.client_local_event a.client c' wire out;
    eliminate exists (conn_ev0:CS.conn_event).
      (EC.client_wire_received_event a.client wire conn_ev0 /\
       SMCan.canonical_wire_step a.client c' conn_ev0
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
         (CW.wire_serialize wire) /\
       EC.client_local_outputs_match conn_ev0 out.SM.so_local_outputs)
    with
    (
      match conn_ev0 with
      | CS.ConnLocalEvent _ ->
        // `EC.client_wire_received_event` is `False` on a local event.
        ()
      | CS.ConnProtectedHandshake step ->
        (* NEW ARM (coalesced protected handshake).  `origin/agentic` extended the
           client's WIRE receive path so that a wire record may be consumed by a
           HEAD `ConnProtectedHandshake` step instead of a `ConnNetworkEvent`.

           BOTH pairing directions close WITHOUT any record->message bridge:

           * `cs_seq_ok b` (client writes / server reads).  The step routes through
             `CS.step_handshake_message _ CL.Received _`, which never touches
             `record_write`, so `app_wseq c' == app_wseq a.client`; the server is
             untouched.  `cs_seq_ok a` transfers.

           * `sc_seq_ok b` (server writes / client reads).  Split on the seal:
             - `App? (snap_wr p)`: the FORWARD conjunct of `channel_seal_ok a`
               gives `App? (rd a.client)`.  But a client taking a legal protected
               handshake step sits at one of the four `legal_handshake_message`
               RECEIVE controls, where `CSL.lemma_handshaking_nonfinal_read_not_application`
               forces the read epoch OFF `Application`.  VACUOUS.
             - `~App? (snap_wr p)`: then `snap_app_wseq p == 0` and `rin_app p == 0`,
               so `lemma_sent_wseq_delta` gives `app_wseq a.server == 0`; and
               `lemma_protected_step_seq` gives `app_rseq c' == 0` (next_seq is
               epoch-preserving off Application; the `Finished` install lands at
               Application seq 0).  0 == 0. *)
        lemma_protected_step_read_not_application a.client step;
        lemma_protected_step_seq a.client.CS.cs_model c'.CS.cs_model step;
        introduce not_closing (SY.ctrl c') ==> app_wseq a.server == app_rseq c'
        with
        (
          lemma_sent_wseq_delta snap a.server.CS.cs_model sent;
          assert (~(R.Application? (snap_wr p).R.epoch))
        )
      | CS.ConnNetworkEvent tm ->
      let msg : M.tls_message = tm.CL.message_value in
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      assert (conn_ev0 == conn_ev);
      Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
      // The model step the client just took: step_tls_message ... Received msg.
      assert (CS.step_tls_message a.client.CS.cs_model CL.Received msg == Some c'.CS.cs_model);
      // ~KeyUpdate(msg) from the post-state's no-rekeying trace (its event log ends
      // with `received_tls_event msg`).
      lemma_recv_not_key_update c' msg;
      // cs-direction (client writes, server reads): a RECEIVE freezes the client's
      // WRITE projection, and the server is untouched, so `cs_seq_ok a` transfers.
      lemma_recv_preserves_write a.client.CS.cs_model c'.CS.cs_model msg;
      // sc-direction (server writes, client reads): the gated alignment.  When the
      // POST-state client is live, the PRE-state client was live too (closing region
      // is absorbing), so `sc_seq_ok a` supplies the pre-state seq equality.
      introduce not_closing (SY.ctrl c') ==> app_wseq a.server == app_rseq c'
      with
      (
        lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model conn_ev;
        // EQ_pre : snap_app_wseq p == app_rseq a.client   (sc_seq_ok a, ToClient p, live)
        // send delta : app_wseq a.server == snap_app_wseq p + rin_app p
        lemma_sent_wseq_delta snap a.server.CS.cs_model sent;
        if R.Application? (snap_wr p).R.epoch then
        (
          // App(snap_wr) BRANCH (was BOTH-APP).  channel_seal_ok a's FORWARD gives
          // App(rd a.client); its snapshot-keyed bridge fires; EQ_pre (both App)
          // gives the seq alignment.  The faithful-decode bridge (fed by the
          // PRE-state seal — non-circular) pins what the client received.
          assert (R.Application? (rd a.client).R.epoch);   // forward, from App(snap_wr)
          CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
            snap a.client.CS.cs_model sent raw;
          // FINDING-1 HINGE: the bridge is invoked only here, where the client's read
          // epoch is Application; the received wire record is Application_data-typed,
          // so by the client not-cleartext helper the received message is not
          // cleartext and the projection yields its decode.  (Unlike the server, the
          // client's App read epoch does NOT imply `ControlApplicationData` — the
          // `HsServerFinishedVerified` window — so the helper excludes SH/HRR by
          // read-epoch placement, not by control.)
          lemma_client_recv_msg_not_cleartext a.client msg c'.CS.cs_model raw;
          lemma_decode_functional a.client.CS.cs_model msg sent raw;
          // msg == sent; the receive delta needs ~Handshake(msg) (from msg == sent an
          // app-data payload) and ~KeyUpdate(msg) (already have).
          lemma_recv_rseq_delta a.client.CS.cs_model c'.CS.cs_model msg;
          // COUNT-MATCH : m_wadv snap sent == m_radv a.client msg.
          (match sent with
           | M.TlsApplicationData bts ->
               // both steps force ControlApplicationData; single-record: the send
               // advance is `application_data_record_count bts == 1`.
               ()
           | M.TlsAlert T.Close_notify ->
               // a received Close_notify lands the client in the closing region
               // (`:943` ApplicationData->ControlClosed, `:949` Closing->ControlClosed),
               // contradicting the live branch — vacuous.
               ()
           | _ -> ())
        )
        else
        (
          // ~App(snap_wr) BRANCH (was NEITHER-APP).  LHS `app_wseq a.server == 0`
          // (snap_app_wseq p == 0 and rin_app p == 0, both by ~App(snap_wr)).  For
          // the RHS: the control-gated backward (channel_seal_ok a, ToClient p)
          // CONTRAPOSITIVE gives ~ControlApplicationData?(ctrl a.client), and `_live`
          // + `lemma_step_preserves_closing` gives not_closing(ctrl a.client) hence
          // ~ControlClosing?.  This branch is REQUIRED to use the control route (not
          // ~App(rd a.client)): CE1 puts a client at `HsServerFinishedVerified` here,
          // which is App-READ yet ~App(snap_wr) — so the read epoch is unusable, but
          // the control is not `ControlApplicationData` and `m_radv == 0` off
          // {CAD,Closing}.  The delta lemma's Handshake precondition is discharged by
          // `lemma_recv_precond`.  With `m_rseq a.client == 0` from EQ_pre +
          // ~App(snap_wr), `app_rseq c' == 0`.  Same two-way read-projection
          // enumeration as the server site (Case A vacuous, Case B `install_keys`
          // zeroes the seq).
          assert (~(CS.ControlApplicationData? (SY.ctrl a.client)));  // control-gated backward
          lemma_recv_precond a.client c' msg;
          lemma_recv_rseq_delta a.client.CS.cs_model c'.CS.cs_model msg;
          lemma_m_radv_zero_non_cad_closing a.client.CS.cs_model msg
        )
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT + PRESERVATION of `read_write_coupling`.

    The conjunct is non-vacuous only for a `ToServer` channel, which is entered
    ONLY by `client_send` and exited ONLY by `deliver_to_server` (to `Quiet`);
    `server_serve` is disabled and every other family keeps the channel `Quiet`
    or turns it `ToClient`.  So preservation is: ESTABLISH at the client send,
    and VACUOUS everywhere else.
    ───────────────────────────────────────────────────────────────────────── **)

(** VACUITY: any state whose channel is not `ToServer` satisfies the coupling. **)
let lemma_rwc_not_to_server (s:SY.tls_system_state)
  : Lemma (requires ~(MP.ToServer? s.channel))
          (ensures read_write_coupling s)
  = ()

(** ESTABLISHMENT at the client send.  The pre-send client (= the payload's
    frozen snapshot `p.pl_snap`) is byte-reachable and consistent (from
    `tls_system_inv a`), and at the pre-state `Quiet` channel `byte_pairing a`
    gives `a.client.raw_sent == a.server.raw_received`.  When the (frozen) server
    is in its receive region, the count lemma
    `ORD.lemma_inflight_sender_write_epoch_not_application_server` then yields
    `(snap_wr p).epoch =!= Application` directly — no snapshot state is carried;
    the full `connection_state` witness is used only here, at the send.

    Note (asymmetry with the committed sibling `lemma_asp_client_send_inflight`,
    which carries `SY.tls_no_rekeying b`): that hypothesis is used there via
    `lemma_sent_not_key_update`/`inflight_sender_stepped`'s `~KeyUpdate` conjunct;
    the count argument here needs no such exclusion, so `tls_no_rekeying` is
    genuinely absent from this establishment. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_rwc_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b)
      (ensures read_write_coupling b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c';
                    channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    with
    (
      let p : SY.tls_payload =
        { SY.pl_raw = SY.emitted_raw out;
          SY.pl_snap = a.client.CS.cs_model;
          SY.pl_sent = sent } in
      assert (b.channel == MP.ToServer p);
      assert (b.server == a.server);
      introduce WStep.server_recv_region_ctrl (SY.ctrl b.server) ==>
                (snap_wr p).R.epoch =!= R.Application
      with
      (
        // byte_pairing a @ Quiet: a.client.raw_sent == a.server.raw_received.
        assert (SY.byte_pairing a);
        assert (Seq.equal a.client.CS.cs_wire_log.CL.raw_sent
                          a.server.CS.cs_wire_log.CL.raw_received);
        Seq.lemma_eq_elim a.client.CS.cs_wire_log.CL.raw_sent
                          a.server.CS.cs_wire_log.CL.raw_received;
        // supply the Ordering lemma's remaining inputs from `tls_system_inv a`.
        assert (WStep.client_reachable
                  (CS.initial a.client.CS.cs_model.CS.model_config) a.client);
        assert (WStep.server_reachable
                  (CS.initial a.server.CS.cs_model.CS.model_config) a.server);
        assert (SMR.connection_state_consistent a.client);
        assert (a.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert (a.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert (WStep.server_recv_region_ctrl a.server.CS.cs_model.CS.model_control);
        ORD.lemma_inflight_sender_write_epoch_not_application_server
          a.server a.client (SY.emitted_raw out)
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    STAGE — APPLICATION RECORD-MATERIAL AGREEMENT ESTABLISHMENT at the
    client-Finished DELIVERY TO SERVER (the unique step turning `cf_delivered`
    true).  Three pure-model/state pins feed the system-level producer.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** B2 RECEIVE PIN: a SERVER taking a LEGAL receive that installs the application
    READ epoch (`record_read.epoch` non-`Application` -> `Application`, ~KeyUpdate)
    is at `HsServerFinishedSent` taking the client-Finished receive — the UNIQUE
    server-legal install arm — landing at `ControlApplicationData`.  The sibling
    install arm (client Finished-receive at `HsCertificateVerifyVerified`,
    StateMachine.fst:738) is excluded by LEGALITY: `legal_tls_message` requires
    `config_role == ClientEndpoint` for it (StateMachine.fst:1371), contradicting
    role Server.  (Note: the KeyUpdate-receive install is excluded by ~KeyUpdate.)
    Legality is available at the delivery from `legal_connection_delta`, so this is
    cheaper than pinning the control to the receive region and enumerating it. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80"
let lemma_server_recv_installs_app_read_pins
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_tls_message m CL.Received msg /\
        CS.step_tls_message m CL.Received msg == Some m' /\
        ~(M.TlsKeyUpdate? msg) /\
        ~(R.Application? m.CS.model_record.CS.record_read.R.epoch) /\
        R.Application? m'.CS.model_record.CS.record_read.R.epoch)
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        m'.CS.model_control == CS.ControlApplicationData)
  = ()
#pop-options

(** B1 MATERIAL CONGRUENCE: at a CONSISTENT endpoint whose read epoch is ALREADY
    `Application`, a receive (~KeyUpdate) touches neither `record_write` (receives
    never write) nor the read epoch/key/iv (only `record_read.seq` advances;
    `fail_model` preserves `model_record` entirely).  The two Finished-receive
    arms — the only read re-installs — sit at handshaking controls
    `HsCertificateVerifyVerified` (client) / `HsServerFinishedSent` (server); at
    either, `CSL.lemma_handshaking_nonfinal_read_not_application` forces the read
    epoch OFF `Application`, contradicting the hypothesis, so they are vacuously
    excluded.  `peer_record_material_agrees` reads ONLY key/iv/epoch (never seq),
    so this is exactly the stability the congruence transfer needs — which is why
    a server receive (advancing only `rd.seq`) and `fail_model` (preserving
    `model_record`) are both harmless to agreement. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80"
let lemma_recv_app_preserves_record_material
  (st st':CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        CS.step_tls_message st.CS.cs_model CL.Received msg == Some st'.CS.cs_model /\
        ~(M.TlsKeyUpdate? msg) /\
        R.Application? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
      (ensures
        st'.CS.cs_model.CS.model_record.CS.record_write == st.CS.cs_model.CS.model_record.CS.record_write /\
        st'.CS.cs_model.CS.model_record.CS.record_read.R.epoch == st.CS.cs_model.CS.model_record.CS.record_read.R.epoch /\
        st'.CS.cs_model.CS.model_record.CS.record_read.R.key == st.CS.cs_model.CS.model_record.CS.record_read.R.key /\
        st'.CS.cs_model.CS.model_record.CS.record_read.R.static_iv == st.CS.cs_model.CS.model_record.CS.record_read.R.static_iv)
  = match st.CS.cs_model.CS.model_control with
    | CS.ControlHandshaking CS.HsCertificateVerifyVerified
    | CS.ControlHandshaking CS.HsServerFinishedSent ->
        CSL.lemma_handshaking_nonfinal_read_not_application st
    | _ -> ()
#pop-options

(** B2 CLIENT-CONTROL PIN (write mirror of the receive pin): a send that installs
    the application WRITE epoch (`record_write.epoch` non-`Application` ->
    `Application`, ~KeyUpdate) lands the sender at `ControlApplicationData`.  The
    UNIQUE `step_tls_message` `Sent` arm that installs app write from a non-app
    snapshot is the client Finished-send (StateMachine.fst:809, at
    `HsServerFinishedVerified`), whose control update to `ControlApplicationData` is
    UNCONDITIONAL (it fires even on the `install_client_application_write_after_finished`
    `None`-arm hole, where the write epoch would stay `Handshake` — but then the
    hypothesis `Application? client'.write` is false and the lemma is vacuous); the
    sibling KeyUpdate-send installer is excluded by ~KeyUpdate, and every other
    `Sent` arm leaves the write epoch unchanged.  Role- and consistency-free: no
    competing arm exists (unlike the receive side's two Finished arms). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 80"
let lemma_client_send_installs_app_write_pins
  (snap client':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message snap CL.Sent sent == Some client' /\
        ~(M.TlsKeyUpdate? sent) /\
        ~(R.Application? snap.CS.model_record.CS.record_write.R.epoch) /\
        R.Application? client'.CS.model_record.CS.record_write.R.epoch)
      (ensures client'.CS.model_control == CS.ControlApplicationData)
  = ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    SYSTEM-LEVEL PRODUCER: `app_material_agreement b` at a `deliver_to_server`.

    Split on the PRE-state server read epoch:
      * B1 (already `Application`): the receive is monotone — `cf_delivered a`
        holds, `app_material_agreement a` (from `app_extras a`) gives agreement at
        `a`, and the receive preserves the material `peer_record_material_agrees`
        reads (key/iv/epoch, never seq), so agreement transfers to `s'`.
      * B2 (not yet `Application`, becomes `Application` at `s'` by `cf_delivered b`):
        the receive INSTALLS app read — the receive pin lands `a.server` at
        `HsServerFinishedSent` (in the recv region, so `read_write_coupling a` fires
        and gives `snap_wr p =!= Application`) and `s'` at `ControlApplicationData`;
        with `inflight_sender_stepped a` and `cf_delivered b`'s `Application?
        (wr a.client)`, the write pin lands `a.client` at `ControlApplicationData`.
        Both endpoints ready, `lemma_ready_quiescent_agrees b` closes it.

    NOTE on the B1/B2 division of labour: the `ControlApplicationData` arm of the
    server reachable shape is USELESS for monotone preservation (it drops
    keys-installed at the closure controls) but SUFFICIENT for the B2 readiness
    establishment via `CSL.lemma_connection_appdata_keys_installed_for_role`
    (through `SY.lemma_appdata_implies_{client,server}_ready`). **)
#restart-solver
#push-options "--fuel 2 --ifuel 4 --z3rlimit 2400"
let lemma_ama_deliver_to_server
  (a:SY.tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        app_extras a /\
        a.channel == SY.tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
        SY.tls_system_inv ({ a with server = s'; channel = MP.Quiet }) /\
        SY.server_config_valid_e2e s' /\
        (* CROSS-RECORD REASSEMBLY GATE, threaded from the caller: the readiness
           agreement tool `SY.lemma_ready_quiescent_agrees` is gated on the client
           taking no BUFFERING protected-handshake step.  We cannot prove that here
           (the cross-endpoint record seal is not in scope at this layer); it is
           discharged one layer up in `TLS13.System.AppExtrasInv` (a conjunct of
           `stream2_extras`), which supplies it at this call.  This step does not
           touch the client (`b.client == a.client`), so the fact is stated on `a`. *)
        CCShape.no_buffering_steps a.client.CS.cs_event_log)
      (ensures app_material_agreement ({ a with server = s'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with server = s'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
    assert (app_seq_pairing a /\
            app_material_agreement a /\ channel_seal_ok a /\
            inflight_sender_stepped a /\ inflight_single_record a /\
            read_write_coupling a);
    assert (a.channel == MP.ToServer p);
    introduce cf_delivered b ==>
                SMKM.supported_profile_application_record_material_agrees b.client b.server
    with
    (
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent
            { CL.message_direction = CL.Received; CL.message_value = msg } in
         CS.legal_connection_delta a.server
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire } s' /\
         SMCan.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      with
      (
        let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        assert (CS.legal_tls_message a.server.CS.cs_model CL.Received msg);
        assert (CS.step_tls_message a.server.CS.cs_model CL.Received msg == Some s'.CS.cs_model);
        lemma_recv_not_key_update s' msg;
        if R.Application? (rd a.server).R.epoch then
        (
          // B1 MONOTONE: agreement at `a` transfers to `s'` (write + read
          // key/iv/epoch preserved; agreement reads no seq).
          lemma_recv_app_preserves_record_material a.server s' msg
        )
        else
        (
          // B2 ESTABLISHMENT: the receive installs app read.
          lemma_server_recv_installs_app_read_pins a.server.CS.cs_model s'.CS.cs_model msg;
          // `a.server @ HsServerFinishedSent` is in the recv region, so
          // `read_write_coupling a` gives `snap_wr p =!= Application`, and the write
          // pin then lands `a.client @ ControlApplicationData`.
          lemma_client_send_installs_app_write_pins snap a.client.CS.cs_model sent;
          SY.lemma_appdata_implies_client_ready b;
          SY.lemma_appdata_implies_server_ready b;
          SY.lemma_ready_quiescent_agrees b
        )
      )
    )
#pop-options
