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
let rin (p:SY.tls_payload) : nat =
  match p.SY.pl_sent with
  | M.TlsApplicationData b -> RF.application_data_record_count b
  | _ -> 1

(** The application record delta an in-flight payload contributes — `rin` when the
    sender sealed it at the application epoch, and `0` for a protected handshake
    record (whose sender snapshot is at the `Handshake` epoch). **)
let rin_app (p:SY.tls_payload) : nat =
  if R.Application? (snap_wr p).R.epoch then rin p else 0

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
