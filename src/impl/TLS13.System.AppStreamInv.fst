module TLS13.System.AppStreamInv

(** ─────────────────────────────────────────────────────────────────────────
    THE APPLICATION BYTE-STREAM INVARIANT.

    This is the last layer of the stream-integrity stack: it lifts the RECORD-seq
    pairing (`ASP.app_seq_pairing`) and the faithful-decode bridge to the
    APPLICATION BYTE STREAMS accumulated in `CS.app_log`, and yields
    `SY.stream_integrity_holds` (each endpoint's received application byte stream
    is a prefix of its peer's sent stream) at every reachable, non-rekeyed state.

    ── WHY NOT `SY.app_pairing` ──────────────────────────────────────────────

    `SY.app_pairing` (System.fst:436) states the byte relation as an EXACT
    EQUALITY (`cs == sr ++ in-flight`) with NO gate.  That statement is not
    provable as an invariant from the stream-2 bundle, and the obstruction is
    real rather than an artefact of proof effort:

      * The delivery case needs BYTE FAITHFULNESS —
        `SY.app_bytes_delta msg == SY.app_bytes_delta sent`, where `sent` is the
        message the sender sealed and `msg` is the message the receiver decoded.
      * Byte faithfulness comes from the faithful-decode bridge
        (`CSL.lemma_received_single_protected_message_decode_..._seal_peer`), which
        needs RECORD-SEQ ALIGNMENT `(snap_wr p).seq == (rd receiver).seq`.
      * Alignment is supplied by `ASP.cs_seq_ok` ONLY under `ASP.not_closing
        (SY.ctrl receiver)`.  That gate is not decoration: it is excused exactly
        over the absorbing closing region, because a `Close_notify` RECEIVED at
        `ControlFailed` goes through the alert arm (`StateMachine.fst:961`) whose
        effect is `fail_model`, which does NOT advance the read seq, while the
        SENDER's `Close_notify` send at `ControlApplicationData` (`:929`) DOES
        advance the write seq.  So a closing-region receiver genuinely desynchronises.
      * Hence at a delivery to a closing-region receiver with an application-data
        payload in flight there is no alignment, the decode is unpinned, and if it
        were unfaithful the application bytes would be DROPPED — falsifying an
        exact equality on the post-state.

    PRECISION (this is a claim about DERIVABILITY, not about truth): that scenario
    is very likely UNREACHABLE — a raw record sealed under the sender's application
    write key, delivered to a receiver holding the matching key at the matching
    seq, decodes to the application-data message that was sealed, so the receive
    step is `None` at a closing-region control and the delivery is simply BLOCKED.
    But the only tool that pins the decode is the bridge, and the bridge needs the
    alignment that the closing region withholds.  So `SY.app_pairing` is
    `true-but-underivable` here, exactly like `appdata_write_coupling`'s conjunct 2
    at a failed server.  It is NOT known to be false.

    ── WHAT IS PROVED INSTEAD ────────────────────────────────────────────────

    `app_stream_pairing` splits `SY.app_pairing` into the part that is needed and
    the part that is derivable:

      * an UNGATED PREFIX clause `is_byte_prefix sr cs`, which is literally one
        half of `SY.stream_integrity_holds` — the end goal; and
      * a GATED EXACT clause `not_closing (ctrl receiver) ==> cs == sr ++ flight`,
        which is what makes the prefix clause inductive.

    The gate is `ASP.not_closing` on the RECEIVER, the SAME gate `ASP.cs_seq_ok`
    already carries, and it is legal by the SAME argument: the closing region is
    absorbing (`ASP.lemma_step_preserves_closing`), so `G_post ==> G_pre` — the
    gate-monotonicity obligation — holds.  That is the hinge of the whole design:
    at a delivery, `G_post` hands back `G_pre`, and `G_pre` is exactly the
    hypothesis `ASP.cs_seq_ok` needs to supply the alignment the bridge needs.  And
    when `G_post` is FALSE only the prefix clause must be re-established, which is
    free because a receiver outside `ControlApplicationData` cannot append
    application bytes at all (the `M.TlsApplicationData` receive arm pins
    `ControlApplicationData`, and `ControlApplicationData` is `not_closing`).

    `SY.lemma_app_pairing_implies_stream_integrity` is therefore NOT used: the
    prefix clause IS `SY.stream_integrity_holds`, so the reduction is `()` here.
    That frozen lemma remains correct and remains the documentation of why the
    equality form would suffice; it is simply a stronger hypothesis than the goal
    requires.
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
module W    = TLS13.Wire.Spec
module T    = TLS13.Types
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
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
module WFL  = TLS13.Spec.WireFormatLemmas
module SCB  = TLS13.System.SeqCountBase
module ASP  = TLS13.System.AppSeqPairing
module HSP  = TLS13.System.HsSeqPairing
module AEI  = TLS13.System.AppExtrasInv
module RTC  = FStar.ReflexiveTransitiveClosure

(** ═══════════════════════════════════════════════════════════════════════════
    PART 1 — MODEL-LEVEL BYTE-STREAM DELTAS.

    Purely local facts about how a single model step moves `app_log`.  Nothing
    cross-endpoint appears until Part 2.
    ═══════════════════════════════════════════════════════════════════════════ **)

let m_sent (m:CS.connection_model) : GTot B.bytes =
  CL.concat_bytes m.CS.model_application.CS.app_log.CL.app_sent

let m_recv (m:CS.connection_model) : GTot B.bytes =
  CL.concat_bytes m.CS.model_application.CS.app_log.CL.app_received

(** CHUNK-LIST level: the ONLY writer of `app_log` inside `step_tls_message` is the
    `M.TlsApplicationData` arm at `ControlApplicationData` (`StateMachine.fst:846`
    for `CL.Sent`, `:856` for `CL.Received`), which appends the payload to the
    matching side and leaves the other side alone.  Every other arm rebuilds
    `model_application` without touching `app_log` (or does not touch
    `model_application` at all). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_step_tls_app_log
  (m m':CS.connection_model) (dir:CS.direction) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m dir msg == Some m')
      (ensures
        (let l  = m.CS.model_application.CS.app_log in
         let l' = m'.CS.model_application.CS.app_log in
         match dir, msg with
         | CL.Sent, M.TlsApplicationData bts ->
             l'.CL.app_sent == l.CL.app_sent @ [bts] /\
             l'.CL.app_received == l.CL.app_received
         | CL.Received, M.TlsApplicationData bts ->
             l'.CL.app_received == l.CL.app_received @ [bts] /\
             l'.CL.app_sent == l.CL.app_sent
         | _, _ ->
             l'.CL.app_sent == l.CL.app_sent /\
             l'.CL.app_received == l.CL.app_received))
  = ()
#pop-options

(** BYTE level: the concatenation moves by exactly `SY.app_bytes_delta msg` on the
    direction of the step, and not at all on the other direction. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_step_tls_streams
  (m m':CS.connection_model) (dir:CS.direction) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m dir msg == Some m')
      (ensures
        (match dir with
         | CL.Sent ->
             Seq.equal (m_sent m') (B.append (m_sent m) (SY.app_bytes_delta msg)) /\
             Seq.equal (m_recv m') (m_recv m)
         | CL.Received ->
             Seq.equal (m_recv m') (B.append (m_recv m) (SY.app_bytes_delta msg)) /\
             Seq.equal (m_sent m') (m_sent m)))
  = lemma_step_tls_app_log m m' dir msg;
    let l  = m.CS.model_application.CS.app_log in
    match dir, msg with
    | CL.Sent, M.TlsApplicationData bts ->
        CL.lemma_concat_bytes_snoc_equal l.CL.app_sent bts (m_sent m)
    | CL.Received, M.TlsApplicationData bts ->
        CL.lemma_concat_bytes_snoc_equal l.CL.app_received bts (m_recv m)
    | _, _ ->
        Seq.append_empty_r (m_sent m);
        Seq.append_empty_r (m_recv m)
#pop-options

(** A legal LOCAL event leaves BOTH byte streams unchanged.  The only local arm
    that touches `app_log` is `LocalDeliverApplicationData bytes` at
    `ControlApplicationData` (`:570`), and its legality guard (`:1315`) is
    `exists pending. app_pending_plaintext == bytes ++ pending`.  With
    `app_pending_plaintext` empty — `SY.app_pending_empty`, conjunct 26 of
    `SY.tls_system_inv` — that forces `bytes` empty, so the appended chunk
    contributes nothing to the concatenation.  (This is the unimplemented
    TLS-to-host delivery hop; see the note at `SY.app_pending_empty`.) **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 200"
let lemma_step_local_streams
  (m m':CS.connection_model) (lev:CS.local_event)
  : Lemma
      (requires
        CS.step_local_event m lev == Some m' /\
        CS.legal_local_event m lev /\
        Seq.equal m.CS.model_application.CS.app_pending_plaintext B.empty)
      (ensures Seq.equal (m_sent m') (m_sent m) /\ Seq.equal (m_recv m') (m_recv m))
  = let l = m.CS.model_application.CS.app_log in
    match lev with
    | CS.LocalDeliverApplicationData bytes ->
        if CS.ControlApplicationData? m.CS.model_control
        then begin
          eliminate exists (pending:B.bytes).
            Seq.equal m.CS.model_application.CS.app_pending_plaintext (B.append bytes pending)
          with
          (
            // |bytes| + |pending| == |empty| == 0, so `bytes` is empty and the
            // appended chunk is invisible to the concatenation.
            Seq.lemma_eq_elim m.CS.model_application.CS.app_pending_plaintext B.empty;
            Seq.lemma_eq_elim m.CS.model_application.CS.app_pending_plaintext
              (B.append bytes pending);
            Seq.lemma_len_append bytes pending;
            assert (Seq.length (B.append bytes pending) ==
                    Seq.length bytes + Seq.length pending);
            assert (Seq.length B.empty == 0);
            assert (Seq.length bytes == 0);
            Seq.lemma_eq_elim bytes B.empty;
            CL.lemma_concat_bytes_snoc_equal l.CL.app_received bytes (m_recv m);
            Seq.append_empty_r (m_recv m)
          )
        end
    | _ -> ()
#pop-options

(** A legal NETWORK event with an EMPTY byte delta on both sides cannot be an
    application-data message: application data is never cleartext, and the
    protected branch of `network_message_raw_delta_legal` forces at least one wire
    record (`protected_record_count >= 1`), which an empty raw cannot carry.  This
    is the byte-stream analogue of
    `ASP.lemma_network_empty_delta_record_unchanged_ungated` and it is proved the
    same way. **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60"
let lemma_network_empty_delta_not_appdata
  (m:CS.connection_model) (dm:CL.directed_message M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnNetworkEvent dm) /\
        CS.step_model m (CS.ConnNetworkEvent dm) == Some m' /\
        CS.event_raw_delta_legal m (CS.ConnNetworkEvent dm) B.empty B.empty)
      (ensures ~(M.TlsApplicationData? dm.CL.message_value))
  = if CS.network_message_is_cleartext dm.CL.message_direction dm.CL.message_value
    then ()
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

(** A `CS.ConnProtectedHandshake` step leaves BOTH application streams unchanged,
    at ANY byte delta (this is the non-empty-delta companion of
    `lemma_step_empty_delta_streams`'s new arm): `CS.step_protected_handshake`
    routes through `CS.step_handshake_message _ CL.Received _`, which never touches
    `model_application.app_log`, and then rewrites only `model_record` and the
    `hb_*` handshake buffers. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_protected_step_streams
  (m m':CS.connection_model) (step:CS.protected_handshake_step)
  : Lemma
      (requires
        CS.legal_event m (CS.ConnProtectedHandshake step) /\
        CS.step_model m (CS.ConnProtectedHandshake step) == Some m')
      (ensures Seq.equal (m_sent m') (m_sent m) /\ Seq.equal (m_recv m') (m_recv m))
  = ()
#pop-options

(** DISPATCH: any legal empty-byte-delta step leaves both streams unchanged.  This
    is what the four LOCAL families consume (a local step emits no wire output, so
    `ASP.lemma_{client,server}_local_extract` hands back exactly this shape). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_step_empty_delta_streams
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ce /\
        CS.step_model m ce == Some m' /\
        CS.event_raw_delta_legal m ce B.empty B.empty /\
        Seq.equal m.CS.model_application.CS.app_pending_plaintext B.empty)
      (ensures Seq.equal (m_sent m') (m_sent m) /\ Seq.equal (m_recv m') (m_recv m))
  = match ce with
    | CS.ConnLocalEvent lev ->
      lemma_step_local_streams m m' lev
    | CS.ConnNetworkEvent dm ->
      lemma_network_empty_delta_not_appdata m dm m';
      lemma_step_tls_streams m m' dm.CL.message_direction dm.CL.message_value;
      Seq.append_empty_r (m_sent m);
      Seq.append_empty_r (m_recv m)
    (* A cleartext buffering step changes only the pending cleartext buffer. *)
    | CS.ConnCleartextHandshake step ->
      assert_norm (CS.step_model m (CS.ConnCleartextHandshake step) ==
                   CS.step_cleartext_handshake m step);
      CS.lemma_step_cleartext_handshake_inert m step
    | CS.ConnProtectedHandshake step ->
      (* NEW ARM.  `CS.step_protected_handshake` routes through
         `CS.step_handshake_message _ CL.Received _` -- a HANDSHAKE step, which never
         touches `model_application.app_log` -- and then rewrites only
         `model_record` and the `hb_*` handshake buffers via
         `CS.set_pending_protected_handshake`.  Both application streams are
         therefore literally unchanged. *)
      ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    PART 2 — THE INVARIANT.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** The application bytes in flight TOWARDS the server (resp. the client).  Zero
    unless the channel carries a payload in that direction. **)
let cs_flight (s:SY.tls_system_state) : GTot B.bytes =
  match s.channel with
  | MP.ToServer p -> SY.app_bytes_of p
  | _ -> B.empty

let sc_flight (s:SY.tls_system_state) : GTot B.bytes =
  match s.channel with
  | MP.ToClient p -> SY.app_bytes_of p
  | _ -> B.empty

(** ── C -> S direction (client sends, server receives). ── **)
let cs_stream_ok (s:SY.tls_system_state) : prop =
  SY.is_byte_prefix (SY.app_stream_received s.server) (SY.app_stream_sent s.client) /\
  (ASP.not_closing (SY.ctrl s.server) ==>
     Seq.equal (SY.app_stream_sent s.client)
               (B.append (SY.app_stream_received s.server) (cs_flight s)))

(** ── S -> C direction (server sends, client receives). ── **)
let sc_stream_ok (s:SY.tls_system_state) : prop =
  SY.is_byte_prefix (SY.app_stream_received s.client) (SY.app_stream_sent s.server) /\
  (ASP.not_closing (SY.ctrl s.client) ==>
     Seq.equal (SY.app_stream_sent s.server)
               (B.append (SY.app_stream_received s.client) (sc_flight s)))

let app_stream_pairing (s:SY.tls_system_state) : prop =
  cs_stream_ok s /\ sc_stream_ok s

(** THE PAYOFF, definitionally: the two ungated prefix clauses ARE
    `SY.stream_integrity_holds`. **)
let lemma_app_stream_pairing_implies_stream_integrity (s:SY.tls_system_state)
  : Lemma (requires app_stream_pairing s)
          (ensures SY.stream_integrity_holds s)
  = ()

(** INITIAL STATE: both logs are empty and the channel is `MP.Quiet`, so both
    prefix clauses are witnessed by `B.empty` and both equalities read
    `empty == empty ++ empty`. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_initial_app_stream_pairing (cfg_c cfg_s:CS.connection_config)
  : Lemma (app_stream_pairing (SY.initial_tls_system cfg_c cfg_s))
  = let s = SY.initial_tls_system cfg_c cfg_s in
    Seq.append_empty_r (SY.app_stream_received s.server);
    Seq.append_empty_r (SY.app_stream_received s.client);
    assert (Seq.equal (SY.app_stream_sent s.client)
                      (B.append (SY.app_stream_received s.server) B.empty));
    assert (Seq.equal (SY.app_stream_sent s.server)
                      (B.append (SY.app_stream_received s.client) B.empty));
    assert (SY.is_byte_prefix (SY.app_stream_received s.server)
                              (SY.app_stream_sent s.client));
    assert (SY.is_byte_prefix (SY.app_stream_received s.client)
                              (SY.app_stream_sent s.server))
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    PART 3 — PREFIX ALGEBRA AND THE DELIVERY BYTE-FAITHFULNESS BRIDGE.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** An exact decomposition is a prefix. **)
let lemma_prefix_of_split (pre delta full:B.bytes)
  : Lemma (requires Seq.equal full (B.append pre delta))
          (ensures SY.is_byte_prefix pre full)
  = introduce exists (rest:B.bytes). Seq.equal full (B.append pre rest)
    with delta and ()

(** Appending on the RIGHT of the longer string preserves the prefix relation. **)
let lemma_prefix_append_r (pre full delta:B.bytes)
  : Lemma (requires SY.is_byte_prefix pre full)
          (ensures SY.is_byte_prefix pre (B.append full delta))
  = eliminate exists (rest:B.bytes). Seq.equal full (B.append pre rest)
    with
    (
      Seq.append_assoc pre rest delta;
      introduce exists (r:B.bytes). Seq.equal (B.append full delta) (B.append pre r)
      with (B.append rest delta) and ()
    )

(** The prefix relation only sees the byte content. **)
let lemma_prefix_ext (pre pre' full full':B.bytes)
  : Lemma (requires SY.is_byte_prefix pre full /\ Seq.equal pre pre' /\ Seq.equal full full')
          (ensures SY.is_byte_prefix pre' full')
  = Seq.lemma_eq_elim pre pre';
    Seq.lemma_eq_elim full full'

(** ALIGNMENT under the LIVE-RECEIVER gate.  This is `ASP.lemma_cs_delivery_alignment`
    with its `ControlApplicationData?` hypothesis relaxed to the `ASP.not_closing`
    gate that `ASP.cs_seq_ok` actually carries — `ControlApplicationData` was only
    ever used there to establish `not_closing`.  Relaxing it is what lets the
    delivery family fire at a live receiver that is still handshaking. **)
let lemma_cs_align_live (s:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        ASP.app_seq_pairing s /\ s.channel == MP.ToServer p /\
        ASP.not_closing (SY.ctrl s.server) /\
        R.Application? (ASP.snap_wr p).R.epoch /\
        R.Application? (ASP.rd s.server).R.epoch)
      (ensures (ASP.snap_wr p).R.seq == (ASP.rd s.server).R.seq)
  = ()

let lemma_sc_align_live (s:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        ASP.app_seq_pairing s /\ s.channel == MP.ToClient p /\
        ASP.not_closing (SY.ctrl s.client) /\
        R.Application? (ASP.snap_wr p).R.epoch /\
        R.Application? (ASP.rd s.client).R.epoch)
      (ensures (ASP.snap_wr p).R.seq == (ASP.rd s.client).R.seq)
  = ()

(** A SENT application-data record leaves the write EPOCH where it was and pins the
    control to `ControlApplicationData` on BOTH sides of the step.  (The arm
    advances `record_write` by `RF.application_data_record_count`, and
    `advance_direction_records` is epoch-preserving.) **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_appdata_send_shape (m m':CS.connection_model) (bts:B.bytes)
  : Lemma
      (requires CS.step_tls_message m CL.Sent (M.TlsApplicationData bts) == Some m')
      (ensures
        m'.CS.model_record.CS.record_write.R.epoch ==
          m.CS.model_record.CS.record_write.R.epoch /\
        m.CS.model_control == CS.ControlApplicationData /\
        m'.CS.model_control == CS.ControlApplicationData)
  = ASP.lemma_advance_direction_records_epoch
      m.CS.model_record.CS.record_write
      (RF.application_data_record_count bts)
#pop-options

(** THE NON-APP SNAPSHOT LEMMA (client side).  If the in-flight-to-server payload
    was NOT sealed at the application write epoch, then it is not application data,
    so it carries NO application bytes.

    RECORD level throughout.  Route: `inflight_sender_stepped` hands back the
    sender's own step; if the message were application data, `lemma_appdata_send_shape`
    puts the POST-send client at `ControlApplicationData` with an UNCHANGED write
    epoch; the post-send client is a consistent `ClientEndpoint`, so
    `CSL.lemma_connection_appdata_keys_installed_for_role` +
    `CSL.lemma_connection_application_ready_record_epochs_installed` place its write
    epoch at `Application` — which, being unchanged by the send, is the snapshot's
    write epoch.  Contradiction.

    This is a genuine slot-to-record derivation and NOT an inference from slot-level
    presence: both CSL lemmas conclude at the RECORD epoch level. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_cs_nonapp_snapshot_no_bytes (a:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.inflight_sender_stepped a /\
        a.channel == MP.ToServer p /\
        ~(R.Application? (ASP.snap_wr p).R.epoch))
      (ensures Seq.equal (SY.app_bytes_of p) B.empty)
  = match p.SY.pl_sent with
    | M.TlsApplicationData bts ->
        lemma_appdata_send_shape p.SY.pl_snap a.client.CS.cs_model bts;
        CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint a.client;
        CSL.lemma_connection_application_ready_record_epochs_installed
          CS.ClientEndpoint a.client
    | _ -> ()
#pop-options

(** SERVER-side mirror. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_sc_nonapp_snapshot_no_bytes (a:SY.tls_system_state) (p:SY.tls_payload)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.inflight_sender_stepped a /\
        a.channel == MP.ToClient p /\
        ~(R.Application? (ASP.snap_wr p).R.epoch))
      (ensures Seq.equal (SY.app_bytes_of p) B.empty)
  = match p.SY.pl_sent with
    | M.TlsApplicationData bts ->
        lemma_appdata_send_shape p.SY.pl_snap a.server.CS.cs_model bts;
        CSL.lemma_connection_appdata_keys_installed_for_role CS.ServerEndpoint a.server;
        CSL.lemma_connection_application_ready_record_epochs_installed
          CS.ServerEndpoint a.server
    | _ -> ()
#pop-options

(** A RECEIVED message that is application data pins the receiver's PRE-state
    control to `ControlApplicationData` — the only `M.TlsApplicationData` receive
    arm (`StateMachine.fst:832`).  Consumed contrapositively: a receiver outside
    `ControlApplicationData` cannot append application bytes. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_recv_appdata_pins_cad (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Received msg == Some m' /\
        M.TlsApplicationData? msg)
      (ensures
        m.CS.model_control == CS.ControlApplicationData /\
        m'.CS.model_control == CS.ControlApplicationData)
  = ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    PART 4 — THE FOUR `Quiet`-PRE-STATE FAMILIES.

    On all four the RECEIVER of each direction is either frozen or steps without
    touching its received stream, so the only work is (i) moving the sender's own
    stream by the delta of the message it just emitted, and (ii) discharging
    gate monotonicity for whichever endpoint's control moved
    (`ASP.lemma_step_preserves_closing`, the SAME absorbing-region argument that
    licenses `ASP.cs_seq_ok`'s gate).
    ═══════════════════════════════════════════════════════════════════════════ **)

(** CLIENT SEND.  Post channel `MP.ToServer p`, `p.pl_snap == a.client.cs_model`,
    `b.server == a.server`.

      * c->s: the client's sent stream grows by `app_bytes_delta sent`, which is
        EXACTLY the new `cs_flight b`, so the gated equality moves from
        `cs == sr` (pre, `cs_flight a == B.empty` at `Quiet`) to
        `cs ++ delta == sr ++ delta`.  The server is frozen, so the gate is
        literally unchanged — no monotonicity obligation on this side.
      * s->c: nothing moves except possibly the CLIENT's control (a `Close_notify`
        send leaves `ControlApplicationData` for `ControlClosing`), so the gate can
        only turn OFF; `ASP.lemma_step_preserves_closing` discharges the direction
        that matters. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_asi_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_stream_pairing a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_send a b)
      (ensures app_stream_pairing b)
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
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      lemma_step_tls_streams a.client.CS.cs_model c'.CS.cs_model CL.Sent sent;
      ASP.lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model
        (SMKM.sent_tls_event sent);
      let cs  = SY.app_stream_sent a.client in
      let cs' = SY.app_stream_sent b.client in
      let sr  = SY.app_stream_received a.server in
      let d   = SY.app_bytes_delta sent in
      // c->s exact (gate unchanged: the server is frozen).
      assert (Seq.equal (cs_flight b) d);
      Seq.append_empty_r cs;
      introduce ASP.not_closing (SY.ctrl b.server) ==>
                Seq.equal cs' (B.append sr (cs_flight b))
      with
      (
        assert (Seq.equal cs (B.append sr (cs_flight a)));
        Seq.append_empty_r sr;
        Seq.lemma_eq_elim cs sr
      );
      // c->s prefix.
      lemma_prefix_append_r sr cs d;
      lemma_prefix_ext sr sr (B.append cs d) cs';
      // s->c: both streams frozen; the flight is empty on both sides.
      Seq.append_empty_r (SY.app_stream_received a.client)
    )
#pop-options

(** SERVER SEND — mirror. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_asi_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_stream_pairing a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_send a b)
      (ensures app_stream_pairing b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s';
                    channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    with
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      lemma_step_tls_streams a.server.CS.cs_model s'.CS.cs_model CL.Sent sent;
      ASP.lemma_step_preserves_closing a.server.CS.cs_model s'.CS.cs_model
        (SMKM.sent_tls_event sent);
      let ss  = SY.app_stream_sent a.server in
      let ss' = SY.app_stream_sent b.server in
      let cr  = SY.app_stream_received a.client in
      let d   = SY.app_bytes_delta sent in
      assert (Seq.equal (sc_flight b) d);
      Seq.append_empty_r ss;
      introduce ASP.not_closing (SY.ctrl b.client) ==>
                Seq.equal ss' (B.append cr (sc_flight b))
      with
      (
        assert (Seq.equal ss (B.append cr (sc_flight a)));
        Seq.append_empty_r cr;
        Seq.lemma_eq_elim ss cr
      );
      lemma_prefix_append_r cr ss d;
      lemma_prefix_ext cr cr (B.append ss d) ss';
      Seq.append_empty_r (SY.app_stream_received a.server)
    )
#pop-options

(** CLIENT LOCAL.  The channel stays `Quiet`, the server is frozen, and the
    client's step has an EMPTY byte delta on both sides, so BOTH of the client's
    streams are pointwise unchanged (`lemma_step_empty_delta_streams`, which
    consumes `SY.app_pending_empty` — conjunct 26 of `SY.tls_system_inv` — to kill
    the `LocalDeliverApplicationData` hop).  Only the client's control can move,
    and only deeper into the closing region. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_asi_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_stream_pairing a /\
        MP.Quiet? a.channel /\ SY.tls_step_client_local a b)
      (ensures app_stream_pairing b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    with
    (
      ASP.lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      with
      (
        lemma_step_empty_delta_streams a.client.CS.cs_model c'.CS.cs_model ce;
        ASP.lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model ce;
        lemma_prefix_ext
          (SY.app_stream_received a.server) (SY.app_stream_received a.server)
          (SY.app_stream_sent a.client) (SY.app_stream_sent b.client);
        lemma_prefix_ext
          (SY.app_stream_received a.client) (SY.app_stream_received b.client)
          (SY.app_stream_sent a.server) (SY.app_stream_sent a.server)
      )
    )
#pop-options

(** SERVER LOCAL — mirror. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60"
let lemma_asi_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ app_stream_pairing a /\
        MP.Quiet? a.channel /\ SY.tls_step_server_local a b)
      (ensures app_stream_pairing b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    with
    (
      ASP.lemma_server_local_extract a.server s' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      with
      (
        lemma_step_empty_delta_streams a.server.CS.cs_model s'.CS.cs_model ce;
        ASP.lemma_step_preserves_closing a.server.CS.cs_model s'.CS.cs_model ce;
        lemma_prefix_ext
          (SY.app_stream_received a.client) (SY.app_stream_received a.client)
          (SY.app_stream_sent a.server) (SY.app_stream_sent b.server);
        lemma_prefix_ext
          (SY.app_stream_received a.server) (SY.app_stream_received b.server)
          (SY.app_stream_sent a.client) (SY.app_stream_sent a.client)
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    PART 5 — THE DELIVERY FAMILIES (the only place byte faithfulness is needed).

    Shape of the argument for `deliver_to_server` (the client mirror is identical
    with the roles swapped):

      * The SENDER (client) is frozen and the s->c direction carries no flight, so
        `sc_stream_ok` transfers verbatim.
      * For `cs_stream_ok` everything turns on `G_post = not_closing (ctrl s')`:

        - `G_post` TRUE.  `ASP.lemma_step_preserves_closing` hands back
          `G_pre = not_closing (ctrl a.server)` — the gate-monotonicity obligation,
          discharged by the absorbing closing region.  `G_pre` is EXACTLY the
          hypothesis `ASP.cs_seq_ok` needs, so the alignment
          `(snap_wr p).seq == (rd a.server).seq` becomes available
          (`lemma_cs_align_live`), and with `channel_seal_ok`'s FORWARD arm and
          BRIDGE arm the faithful-decode bridge fires and pins `msg == sent`.  The
          received stream therefore grows by exactly the in-flight bytes and the
          gated equality re-establishes itself with an empty flight.
          When the snapshot was NOT sealed at the application epoch,
          `channel_seal_ok`'s CONTROL-GATED BACKWARD arm (contrapositive) puts the
          server outside `ControlApplicationData`, so it cannot append application
          bytes, and `lemma_cs_nonapp_snapshot_no_bytes` says there were none to
          append: both sides of the equation move by `B.empty`.

        - `G_post` FALSE.  Only the PREFIX clause must be re-established, and that
          is free: a receiver that appends application bytes is pinned at
          `ControlApplicationData` BEFORE and AFTER the step
          (`lemma_recv_appdata_pins_cad`), and `ControlApplicationData` is
          `not_closing` — contradicting `~G_post`.  So the received stream does not
          move at all and the pre-state prefix transfers.

    NON-CIRCULARITY: every fact consumed is read off the PRE-state `a` (or off the
    step itself); the conclusion lands on `b`.
    ═══════════════════════════════════════════════════════════════════════════ **)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 120"
let lemma_asi_deliver_to_server_raw
  (a:SY.tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ app_stream_pairing a /\
        a.channel == SY.tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out)
      (ensures app_stream_pairing ({ a with server = s'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with server = s'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
    assert (a.channel == MP.ToServer p);
    // TWO-RUN (by line index): DECORATIVE at the current fuel/ifuel.  DO NOT DELETE
    // AS DEAD WEIGHT: it is the producer of `WStep.server_ctrl_ok a.server`, the
    // hypothesis `ASP.lemma_recv_msg_not_cleartext` (LOAD-BEARING below) needs; if
    // ifuel ever drops, the inline re-derivation goes away and this becomes the fix.
    ASP.lemma_server_reachable_ctrl_ok a.server.CS.cs_model.CS.model_config a.server;
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
      assert (CS.step_tls_message a.server.CS.cs_model CL.Received msg == Some s'.CS.cs_model);
      // TWO-RUN: LOAD-BEARING (Error 19 when neutralised).  This is what says the
      // receiver's stream grows by exactly `app_bytes_delta msg` and the sender's
      // does not move at all.
      lemma_step_tls_streams a.server.CS.cs_model s'.CS.cs_model CL.Received msg;
      // TWO-RUN: DECORATIVE at ifuel 4.  DO NOT DELETE AS DEAD WEIGHT: this call is
      // the machine-checked discharge of the GATE-MONOTONICITY obligation
      // `G_post ==> G_pre` that makes the `not_closing` gate on `cs_stream_ok`
      // legal at all.  Without it the gate rests on an unproven absorption claim.
      ASP.lemma_step_preserves_closing a.server.CS.cs_model s'.CS.cs_model conn_ev;
      let cs = SY.app_stream_sent a.client in
      let sr = SY.app_stream_received a.server in
      let sr' = SY.app_stream_received b.server in
      let dm = SY.app_bytes_delta msg in
      // (i) OFF the gate the receiver cannot have appended anything.
      introduce ~(ASP.not_closing (SY.ctrl s')) ==> Seq.equal dm B.empty
      with
      (
        if M.TlsApplicationData? msg
        then lemma_recv_appdata_pins_cad a.server.CS.cs_model s'.CS.cs_model msg
        else ()
      );
      // (ii) ON the gate the delivery is byte-faithful.
      introduce ASP.not_closing (SY.ctrl s') ==> Seq.equal dm (SY.app_bytes_of p)
      with
      (
        assert (ASP.not_closing (SY.ctrl a.server));
        if R.Application? (ASP.snap_wr p).R.epoch
        then
        (
          // FORWARD arm of `channel_seal_ok a` -> the receiver is on app read keys.
          assert (R.Application? (ASP.rd a.server).R.epoch);
          // TWO-RUN: DECORATIVE (the lemma is itself `= ()`, so Z3 re-derives the
          // alignment inline from `ASP.app_seq_pairing a`).  DO NOT DELETE AS DEAD
          // WEIGHT: the seq alignment it names is the PRECONDITION of the bridge on
          // the next line, and is the sole reason the `not_closing` gate had to be
          // put on this clause in the first place.
          lemma_cs_align_live a p;
          // TWO-RUN: LOAD-BEARING.  The faithful-decode bridge.
          CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
            snap a.server.CS.cs_model sent raw;
          // TWO-RUN: LOAD-BEARING.  Converts the received-event projection for `msg`.
          ASP.lemma_recv_msg_not_cleartext a.server.CS.cs_model msg s'.CS.cs_model raw;
          // TWO-RUN: DECORATIVE.  DO NOT DELETE AS DEAD WEIGHT: it names the step
          // (decode functionality) that pins `msg == sent`, the whole point of the arm.
          ASP.lemma_decode_functional a.server.CS.cs_model msg sent raw
        )
        else
        (
          // BACKWARD arm (contrapositive): the receiver is off `ControlApplicationData`,
          // so it cannot append; and the snapshot carried no application bytes.
          assert (~(CS.ControlApplicationData? (SY.ctrl a.server)));
          if M.TlsApplicationData? msg
          then lemma_recv_appdata_pins_cad a.server.CS.cs_model s'.CS.cs_model msg
          else ();
          // TWO-RUN: LOAD-BEARING.  A non-application-epoch snapshot carries no
          // application bytes -- this is the RECORD-level fact (reached via
          // `CSL.lemma_connection_appdata_keys_installed_for_role`), never inferred
          // from slot-level key presence.
          lemma_cs_nonapp_snapshot_no_bytes a p
        )
      );
      // (iii) assemble the c->s clause.
      assert (Seq.equal sr' (B.append sr dm));
      Seq.append_empty_r sr;
      introduce ASP.not_closing (SY.ctrl b.server) ==>
                Seq.equal cs (B.append sr' (cs_flight b))
      with
      (
        assert (Seq.equal cs (B.append sr (SY.app_bytes_of p)));
        Seq.append_empty_r sr'
      );
      if ASP.not_closing (SY.ctrl b.server)
      then lemma_prefix_of_split sr' (cs_flight b) cs
      else lemma_prefix_ext sr sr' cs cs;
      // (iv) the s->c clause: both endpoints' streams in that direction are frozen
      // and the flight is empty before and after.
      Seq.append_empty_r (SY.app_stream_received a.client)
    )
#pop-options

(** The mirror.  Same three-part argument as above with the roles swapped; the one
    asymmetry is the not-cleartext hinge, which must use the CLIENT helper
    (`ASP.lemma_client_recv_msg_not_cleartext`, which excludes SH/HRR by read-epoch
    placement) rather than the server one (which grounds the exclusion in
    `server_ctrl_ok`, a fact a client does not have). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 120"
let lemma_asi_deliver_to_client_raw
  (a:SY.tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ app_stream_pairing a /\
        a.channel == SY.tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out)
      (ensures app_stream_pairing ({ a with client = c'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with client = c'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
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
        (* `EC.client_wire_received_event` is `False` on a local event. *)
        ()
      (* [client_wire_received_event] is False on a cleartext buffering step. *)
      | CS.ConnCleartextHandshake _ -> ()
      | CS.ConnProtectedHandshake step ->
        (* NEW ARM (coalesced protected handshake).  The delivered record is consumed
           by a HEAD protected-handshake step, which moves NO application bytes
           (`lemma_protected_step_streams`), so the client's received stream is
           frozen.  What must still be shown is that the IN-FLIGHT payload carried no
           application bytes either -- otherwise the `sc` equality would lose them
           when the channel returns to `MP.Quiet`.  That is settled WITHOUT any
           record->message bridge: a client taking a legal protected-handshake step
           sits at one of the four `legal_handshake_message` RECEIVE controls, where
           `CSL.lemma_handshaking_nonfinal_read_not_application` forces its read
           epoch OFF `R.Application` (`ASP.lemma_protected_step_read_not_application`);
           the FORWARD conjunct of `ASP.channel_seal_ok a` therefore rules out
           `App? (snap_wr p)`, and `lemma_sc_nonapp_snapshot_no_bytes` gives
           `SY.app_bytes_of p == B.empty`. *)
        Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
        lemma_protected_step_streams a.client.CS.cs_model c'.CS.cs_model step;
        ASP.lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model conn_ev0;
        ASP.lemma_protected_step_read_not_application a.client step;
        assert (~(R.Application? (ASP.snap_wr p).R.epoch));
        lemma_sc_nonapp_snapshot_no_bytes a p;
        let cr = SY.app_stream_received a.client in
        Seq.append_empty_r cr;
        Seq.append_empty_r (SY.app_stream_received b.client);
        Seq.append_empty_r (SY.app_stream_received a.server);
        assert (Seq.equal (SY.app_stream_received b.client) cr)
      | CS.ConnNetworkEvent tm ->
      let msg : M.tls_message = tm.CL.message_value in
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      assert (conn_ev0 == conn_ev);
      Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Received msg == Some c'.CS.cs_model);
      lemma_step_tls_streams a.client.CS.cs_model c'.CS.cs_model CL.Received msg;
      ASP.lemma_step_preserves_closing a.client.CS.cs_model c'.CS.cs_model conn_ev;
      let ss = SY.app_stream_sent a.server in
      let cr = SY.app_stream_received a.client in
      let cr' = SY.app_stream_received b.client in
      let dm = SY.app_bytes_delta msg in
      introduce ~(ASP.not_closing (SY.ctrl c')) ==> Seq.equal dm B.empty
      with
      (
        if M.TlsApplicationData? msg
        then lemma_recv_appdata_pins_cad a.client.CS.cs_model c'.CS.cs_model msg
        else ()
      );
      introduce ASP.not_closing (SY.ctrl c') ==> Seq.equal dm (SY.app_bytes_of p)
      with
      (
        assert (ASP.not_closing (SY.ctrl a.client));
        if R.Application? (ASP.snap_wr p).R.epoch
        then
        (
          assert (R.Application? (ASP.rd a.client).R.epoch);
          lemma_sc_align_live a p;
          CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
            snap a.client.CS.cs_model sent raw;
          ASP.lemma_client_recv_msg_not_cleartext a.client msg c'.CS.cs_model raw;
          ASP.lemma_decode_functional a.client.CS.cs_model msg sent raw
        )
        else
        (
          assert (~(CS.ControlApplicationData? (SY.ctrl a.client)));
          if M.TlsApplicationData? msg
          then lemma_recv_appdata_pins_cad a.client.CS.cs_model c'.CS.cs_model msg
          else ();
          lemma_sc_nonapp_snapshot_no_bytes a p
        )
      );
      assert (Seq.equal cr' (B.append cr dm));
      Seq.append_empty_r cr;
      introduce ASP.not_closing (SY.ctrl b.client) ==>
                Seq.equal ss (B.append cr' (sc_flight b))
      with
      (
        assert (Seq.equal ss (B.append cr (SY.app_bytes_of p)));
        Seq.append_empty_r cr'
      );
      if ASP.not_closing (SY.ctrl b.client)
      then lemma_prefix_of_split cr' (sc_flight b) ss
      else lemma_prefix_ext cr cr' ss ss;
      Seq.append_empty_r (SY.app_stream_received a.server)
    )
#pop-options

(** ── The two delivery families, in the bundled `(a b)` shape the roll-up wants. ── **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_asi_deliver_to_server (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ app_stream_pairing a /\
        SY.tls_step_deliver_to_server a b)
      (ensures app_stream_pairing b)
  = SY.lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    with lemma_asi_deliver_to_server_raw a wire s' out raw snap sent

let lemma_asi_deliver_to_client (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ app_stream_pairing a /\
        SY.tls_step_deliver_to_client a b)
      (ensures app_stream_pairing b)
  = SY.lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == SY.tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    with lemma_asi_deliver_to_client_raw a wire c' out raw snap sent
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    PART 6 — THE ROLL-UP AND THE REACHABILITY PAYOFF.

    `app_stream_pairing` sits on TOP of `AEI.stream2_extras`: the four `Quiet`
    families need nothing but the byte invariant itself, and the two deliveries
    consume `ASP.app_extras` (for `channel_seal_ok`, `app_seq_pairing`,
    `inflight_sender_stepped`).  Layering rather than merging keeps the six
    families here small and leaves the stream-2 layer untouched.
    ═══════════════════════════════════════════════════════════════════════════ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_app_stream_pairing_preserved (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ app_stream_pairing a /\
        SY.tls_sys_step a b)
      (ensures app_stream_pairing b)
  = MP.lemma_step_channel_cases SY.tls_machine_iface a b;
    FStar.Classical.move_requires_2 lemma_asi_client_send a b;
    FStar.Classical.move_requires_2 lemma_asi_server_send a b;
    FStar.Classical.move_requires_2 lemma_asi_deliver_to_client a b;
    FStar.Classical.move_requires_2 lemma_asi_deliver_to_server a b;
    FStar.Classical.move_requires_2 lemma_asi_client_local a b;
    FStar.Classical.move_requires_2 lemma_asi_server_local a b
#pop-options

(** The stream-3 combined predicate.  Same gate shape as `AEI.stream2_combined_inv`
    and `SY.stream_combined_inv`: the byte-level bundle is gated on
    `SY.tls_no_rekeying`, recovered BACKWARDS along a step by
    `SY.lemma_no_key_update_backward`. **)
let stream3_combined_inv (s:SY.tls_system_state) : prop =
  AEI.stream2_combined_inv s /\
  (SY.tls_no_rekeying s ==> app_stream_pairing s)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_stream3_combined_inv_preserved (x y:SY.tls_system_state)
  : Lemma (requires stream3_combined_inv x /\ SY.tls_sys_step x y)
          (ensures stream3_combined_inv y)
  = AEI.lemma_stream2_combined_inv_preserved x y;
    introduce SY.tls_no_rekeying y ==> app_stream_pairing y
    with
    (
      SY.lemma_no_key_update_backward x y;
      assert (SY.tls_system_inv x);
      assert (AEI.stream2_extras x);
      assert (ASP.app_extras x);
      assert (app_stream_pairing x);
      lemma_app_stream_pairing_preserved x y
    )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_initial_stream3_combined_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c /\
        SY.server_config_valid_e2e (CS.initial cfg_s))
      (ensures stream3_combined_inv (SY.initial_tls_system cfg_c cfg_s))
  = AEI.lemma_initial_stream2_combined_inv cfg_c cfg_s;
    lemma_initial_app_stream_pairing cfg_c cfg_s
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE BYTE-LEVEL REACHABILITY PAYOFF.

    Every reachable, non-rekeyed state with a valid server config satisfies the
    byte-stream pairing bundle — whose UNGATED clauses are literally
    `SY.stream_integrity_holds`.

    Entry hypotheses are IDENTICAL to `AEI.lemma_reachable_stream2_inv` (and hence
    to `SY.lemma_reachable_stream_inv` plus `server_config_valid_e2e`); nothing is
    added and nothing is traded away.
    ───────────────────────────────────────────────────────────────────────── **)
val lemma_reachable_app_stream_inv (cfg_c cfg_s:CS.connection_config) (s:SY.tls_system_state)
  : Lemma (requires cfg_c.CS.config_role == CS.ClientEndpoint /\
                    cfg_s.CS.config_role == CS.ServerEndpoint /\
                    WFL.supported_client_config_wire_profile cfg_c /\
                    SY.server_config_valid_e2e (CS.initial cfg_s) /\
                    SY.tls_no_rekeying s /\
                    RTC.closure SY.tls_sys_step (SY.initial_tls_system cfg_c cfg_s) s)
          (ensures SY.tls_stream_inv s /\ AEI.stream2_extras s /\ app_stream_pairing s)
let lemma_reachable_app_stream_inv cfg_c cfg_s s =
  AEI.lemma_reachable_stream2_inv cfg_c cfg_s s;
  lemma_initial_stream3_combined_inv cfg_c cfg_s;
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 lemma_stream3_combined_inv_preserved);
  RTC.stable_on_closure SY.tls_sys_step stream3_combined_inv ()
