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
module SM   = Common.StateMachine
module CW   = TLS13.Spec.Endpoint.Wire
module CTy  = TLS13.Impl.CanonicalTypes
module EC   = TLS13.Spec.Endpoint.Client
module ES   = TLS13.Spec.Endpoint.Server
module EAPI = TLS13.Spec.Endpoint.API
module L    = FStar.List.Tot

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

(** The app-epoch WRITE advance a SENT message applies (when the writer is at the
    `Application` epoch): `application_data_record_count` for app data, one for a
    protected `Close_notify`, zero otherwise. **)
let msg_wcount (msg:M.tls_message) : nat =
  match msg with
  | M.TlsApplicationData b -> RF.application_data_record_count b
  | M.TlsAlert T.Close_notify -> 1
  | _ -> 0

(** The app-epoch READ advance a RECEIVED message applies (when the reader is at
    the `Application` epoch): a single record for every deliverable protected
    payload (`step_tls_message` bumps `record_read` by exactly one via `next_seq`),
    zero otherwise.  Note this differs from `msg_wcount` on multi-record app data —
    but such a send is UNDELIVERABLE (`tls_carries` forces a single wire record),
    so at any real delivery `msg_wcount == msg_rcount == 1`. **)
let msg_rcount (msg:M.tls_message) : nat =
  match msg with
  | M.TlsApplicationData _ -> 1
  | M.TlsAlert T.Close_notify -> 1
  | M.TlsIgnoredPostHandshake _ -> 1
  | _ -> 0

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
    returns ~(M.TlsKeyUpdate? msg)
    with _pf.
      lemma_no_key_update_tail prefix (SMKM.sent_tls_event msg)

(** SEND DELTA.  A legal `Sent` model step advances the epoch-collapsing WRITE
    projection by `msg_wcount msg` (when the writer is at the `Application` epoch)
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
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

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"
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
    READ projection by `msg_rcount msg` (when the reader is at the `Application`
    epoch) and leaves the WRITE projection unchanged.  Same guard rationale. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
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

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"
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

(** ── C -> S direction (client writes, server reads). ── **)
let cs_seq_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      app_wseq s.client == app_rseq s.server + rin_app p /\
      snap_app_wseq p == app_rseq s.server
  | _ ->
      app_wseq s.client == app_rseq s.server

(** ── S -> C direction (server writes, client reads). ── **)
let sc_seq_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToClient p ->
      app_wseq s.server == app_rseq s.client + rin_app p /\
      snap_app_wseq p == app_rseq s.client
  | _ ->
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
        R.Application? (snap_wr p).R.epoch /\
        R.Application? (rd s.server).R.epoch)
      (ensures (snap_wr p).R.seq == (rd s.server).R.seq)
  = ()

let lemma_sc_delivery_alignment (s:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        app_seq_pairing s /\ s.channel == MP.ToClient p /\
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
    OPTION-4 FROZEN-CLIENT COUPLING — the establishment seam for agreement.

    Agreement is ESTABLISHED at the atomic client-Finished delivery to the server
    (the unique step that turns `cf_delivered` true), by invoking
    `SY.lemma_ready_quiescent_agrees` on the post-state.  That tool needs BOTH
    endpoints at `ControlApplicationData`.  The server lands there atomically; the
    CLIENT's control must be recovered from the pre-state, where the client is
    FROZEN with its Finished in flight.

    We capture "the client is frozen at application data while its Finished is in
    flight" as an invariant KEYED ON THE IN-FLIGHT MESSAGE (`pl_sent` is a
    Finished), NOT on the client's key-epoch state.  The message key is what makes
    it cheap:

      * ESTABLISHMENT (at `client_send`): a client (`config_role == ClientEndpoint`,
        a `tls_system_inv` conjunct) Finished send is legal only from
        `HsServerFinishedVerified` — the sibling `HsServerEncryptedFlightSent`
        Finished arm requires `ServerEndpoint` — and that arm sets
        `model_control := ControlApplicationData` unconditionally
        (`StateMachine.fst:809`).  So any client Finished send lands the client at
        application data, BY CONSTRUCTION.  No cross-endpoint progress coupling and
        no `close_notify` case-analysis is needed: a `close_notify` is not a
        `Finished`, so the antecedent is simply false for it (this is exactly the
        `ControlClosing` wart that a key-epoch-keyed antecedent would have hit).

      * PRESERVATION: a `MP.ToServer` channel is entered only by `client_send`
        (the establishment case).  From a `ToServer` state the ONLY enabled family
        is `deliver_to_server` (every send/local gates on `is_quiet`,
        `deliver_to_client` needs `ToClient`, and `server_serve` is disabled in
        this instance), and it yields `Quiet`, making the antecedent vacuous.
        Every OTHER family starts from `Quiet`, so `MP.ToServer? s.channel` is
        false in its pre-state and there is nothing to preserve.
    ───────────────────────────────────────────────────────────────────────── **)
let cf_inflight_client_appdata (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      (M.TlsHandshake? p.SY.pl_sent /\ M.Finished? (M.TlsHandshake?._0 p.SY.pl_sent)) ==>
        SY.ctrl s.client == CS.ControlApplicationData
  | _ -> True

(** The full STAGE (b)+(c) extras carried on top of the stream bundle. **)
let app_extras (s:SY.tls_system_state) : prop =
  app_seq_pairing s /\ cf_inflight_client_appdata s /\ app_material_agreement s

(** Initial state: both record epochs are `Initial`, so `cf_delivered` is false
    and the agreement is vacuous; `app_seq_pairing` was shown initial above. **)
let lemma_initial_app_extras (cfg_c cfg_s:CS.connection_config)
  : Lemma (app_extras (SY.initial_tls_system cfg_c cfg_s))
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT HELPERS for `cf_inflight_client_appdata`.
    ───────────────────────────────────────────────────────────────────────── **)

(** SPEC-level: a *client* Finished send lands the client at
    `ControlApplicationData`.  A `CL.Sent` Finished steps via
    `step_handshake_message`, whose only two `CL.Sent, M.Finished` arms are at
    `HsServerEncryptedFlightSent` (→ `HsServerFinishedSent`) and
    `HsServerFinishedVerified` (→ `ControlApplicationData`).  Legality at the
    former requires `config_role == ServerEndpoint`; with `ClientEndpoint` only the
    latter is legal, and it sets the control unconditionally. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 30 --split_queries always"
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
    returns
      CS.legal_event st0.CS.cs_model (SMKM.sent_tls_event sent) /\
      CS.step_model st0.CS.cs_model (SMKM.sent_tls_event sent) == Some c'.CS.cs_model
    with _pf.
    (
      // `canonical_wire_step` gives `legal_connection_delta`, hence
      //   c'.cs_event_log == st0.cs_event_log @ [conn_ev].
      // Together with the hypothesis' `@ [sent_tls_event sent]`, append-injectivity
      // on the shared head pins the singleton tails equal.
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent)
    )
#pop-options
