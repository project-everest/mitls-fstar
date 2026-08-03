module TLS13.System.HsSeqPairing

(**
  HANDSHAKE-epoch RECORD-SEQUENCE alignment — the seq-level analogue of
  `AppSeqPairing.app_seq_pairing`, one epoch earlier.

  GOAL.  At a PROTECTED-HANDSHAKE delivery (EE / Cert / CV / SF to the client, CF
  to the server) the sender's `record_write.seq` equals the receiver's
  `record_read.seq`, so that — together with the readiness-FREE key/iv agreement
  from `HandshakeAgreementNonReady` — the faithful-decode bridge
  `CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer`
  applies BEFORE either endpoint is application-ready.  This is the seq-alignment
  half of THE ALIGNMENT LAW: faithful decode = key/iv agreement (control-free,
  survives `ControlFailed`) + cross-endpoint seq alignment (a COUNTING fact that
  must be inductively maintained, and is NOT readiness-free).  Per-endpoint
  replay-consistency furnishes only same-endpoint facts; this conjunct supplies the
  cross-endpoint half.

  WHY IT IS EPOCH-GATED (unlike the app analogue, which is UNguarded).
  `app_seq_pairing` needs no epoch gate because the application epoch is TERMINAL:
  the collapsing projection is `0` through the whole handshake and stays `0` at the
  instant either endpoint installs its app keys (fresh app seq `0`), so the
  identity is continuous.  The HANDSHAKE epoch is NOT terminal — it has an
  ASYMMETRIC EXIT:

    * the SERVER leaves handshake-WRITE via a SEPARATE local (app-write installs at
      `HsServerFinishedSent`, AFTER the SF send has already bumped handshake-write
      to seq 4 — StateMachine.fst:676-687 does `record_write = next_seq` and does
      NOT install app keys);
    * the CLIENT leaves handshake-READ INSIDE the SF receive (:738 installs
      app-read directly, collapsing to app seq `0`).

  So immediately after the SF delivery there is a `Quiet` state where the server
  still sits at handshake-write seq 4 while the client has collapsed to app-read 0.
  An UNGATED collapsing identity `hs_wseq server == hs_rseq client` would read
  `4 == 0` there — FALSE.  The fix (and the shape approved for this build) is to
  gate each Quiet half on BOTH endpoints' relevant epoch being `R.Handshake`; the
  exit window is then vacuous on whichever side has already collapsed, on either
  order of the asymmetric exit.  The in-flight half is gated on the SEALING
  SNAPSHOT (`snap_wr p`) per the standing discipline — the record in flight was
  sealed under the snapshot, and reading the live sender epoch would be reading a
  post-send quantity.

  NON-CIRCULARITY.  The pre-state coupling supplies THIS record's alignment; the
  post-state is never read to justify the step.  Coupling-pre + readiness-free key
  agreement => open succeeds => the decoded record IS the sent one => the receive
  either advances handshake-read by `+1` (coupling-post holds) or the record is
  wrong-control and blocks at StateMachine.fst:822 (no successor, trivially
  preserved).  "seq alignment proves decode which proves seq alignment" is what a
  reader will suspect; the resolution is that alignment-PRE proves decode proves
  alignment-POST, an ordinary induction.

  ESTABLISHMENT IS FREE.  Both endpoints reset seq to `0` on handshake-epoch
  install and the collapsing projection reads `0` before install (Initial epoch)
  and `0` at install (fresh handshake seq `0`), so the identity is continuous at
  the entry boundary.  No dedicated establishment family: the ordinary
  send/local/deliver families carry it through, and the CLEARTEXT window
  (ServerHello in flight before the client installs its read key) is excluded by
  CHANNEL DISCIPLINE — sends require `Quiet` (MP.lemma_step_channel_cases), so the
  server cannot send EE while SH is still in flight, and the first both-`Handshake`
  `Quiet` state (right after SH delivery) has both seqs freshly `0`.
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
module ASP  = TLS13.System.AppSeqPairing
module SMCan = TLS13.Spec.StateMachine.Canonical
module CSL  = TLS13.ConnectionState.Lemmas
module W    = TLS13.Wire.Spec
module T    = TLS13.Types
module SM   = Common.StateMachine
module CW   = TLS13.Spec.Endpoint.Wire
module CTy  = TLS13.Impl.CanonicalTypes
module EC   = TLS13.Spec.Endpoint.Client
module ES   = TLS13.Spec.Endpoint.Server
module EAPI = TLS13.Spec.Endpoint.API
module L    = FStar.List.Tot
module WStep = TLS13.System.WireStep
module WF   = Common.WireFormat
module HANR = TLS13.ConnectionState.HandshakeAgreementNonReady
module PWRA = TLS13.ConnectionState.ProtectedWireRecordAlignment

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(** EPOCH-COLLAPSING handshake-seq projections: the record seq counted only while
    at the HANDSHAKE epoch, and `0` otherwise.  Continuous across the ENTRY
    boundary (a fresh handshake epoch starts at seq `0`); the EXIT boundary is
    handled by the both-epoch gate on the conjunct, not by the projection. **)
let hs_wseq (st:CS.connection_state) : nat =
  if R.Handshake? (ASP.wr st).R.epoch then (ASP.wr st).R.seq else 0

let hs_rseq (st:CS.connection_state) : nat =
  if R.Handshake? (ASP.rd st).R.epoch then (ASP.rd st).R.seq else 0

(** The handshake-write seq captured in an in-flight payload's SENDER SNAPSHOT —
    the sealing snapshot `pl_snap`, per the standing in-flight discipline. **)
let snap_hs_wseq (p:SY.tls_payload) : nat =
  if R.Handshake? (ASP.snap_wr p).R.epoch then (ASP.snap_wr p).R.seq else 0

(** TERMINAL controls — the "done" states reached via `fail_model`
    (`ControlFailed`) or the close sequence (`ControlClosing`/`ControlClosed`).

    ROOT CAUSE (one sentence): `fail_model` (StateMachine.fst:303) is the UNIQUE
    step that decouples the read-seq from the received-byte count — it preserves
    `model_record` (so the read seq is NOT advanced) while the delivery still
    appends the record bytes — and it lands EXCLUSIVELY in the terminal set; so the
    terminal set is exactly the states where the cross-endpoint seq coupling can
    fail, and `not (terminal_control receiver)` gates precisely those out (the
    delivery-to-a-failed-receiver window that would otherwise falsify the pairing).

    THE GATE-MONOTONICITY LAW (why `not terminal`, NOT `ControlHandshaking?`).
    A gate `G` on an invariant conjunct `G ==> P` is NOT free.  Under preservation
    `inv a /\ step a b ==> inv b` you ASSUME `G_a ==> P_a` and must PROVE
    `G_b ==> P_b`: given `G_b` you must first re-establish `G_a` to use the
    hypothesis, so you owe `G_b ==> G_a` — the gate must be BACKWARD-MONOTONE along
    legal steps.  Adding a gate buys vacuity at the post-state and simultaneously
    CHARGES this monotonicity obligation (this is the law that fails for a lemma's
    "weaker hypothesis is free" intuition — it holds for lemmas, NOT for invariant
    conjuncts).  A positive control class is generally NOT backward-monotone:
    `ControlHandshaking?` fails because the `ControlNew -> HsStarted` entry step
    (LocalStartHandshake, StateMachine.fst:490) ENTERS the class from outside it.
    The reliable construction is the COMPLEMENT OF AN ABSORBING SET: if no legal
    step leaves `S` then `~S` is backward-monotone by contraposition.  The terminal
    set is absorbing (`lemma_step_terminal_control_absorbing`, bare `()`, no
    reachability), so `not terminal` transfers across the local families where the
    acting endpoint is its OWN receiver and its control changes under a
    record-unchanged step.  Do NOT "simplify" this back to `ControlHandshaking?`.

    EQUIVALENCE (why this is not a soundness dodge).  `ControlHandshaking? ==>
    ~terminal`, so `not terminal` is the WEAKER GATE / STRONGER CONJUNCT — the
    HARDER thing to prove, not a way to duck the obligation.  Under the
    `R.Handshake? (rd receiver)` epoch gate the two gates COINCIDE on exactly the
    gated states: the non-terminal non-handshaking controls are `ControlNew` (read
    epoch `Initial`) and `ControlApplicationData` (read epoch `Application`,
    installed atomically at StateMachine.fst:738 for the client and required by
    :567's legality for the server) — both killed by the epoch conjunct.  So the
    coupling is semantically identical to the `ControlHandshaking?` version. **)
let terminal_control (c:CS.connection_control_state) : bool =
  CS.ControlFailed? c || CS.ControlClosing? c || CS.ControlClosed? c

(** ── C -> S direction (client writes, server reads). ──
    In flight: the sealed snapshot's handshake-write seq equals the server's
    handshake-read seq.  Settled: both endpoints' relevant epoch handshake =>
    write == read.  BOTH arms carry the SAME both-epoch discipline: the snapshot
    (resp. live) write epoch AND the receiver's read epoch must be `Handshake`.
    The receiver-read gate on the IN-FLIGHT arm is LOAD-BEARING, not decorative:
    a server/client can seal a PROTECTED alert (`Close_notify` -> `fail_model` via
    StateMachine.fst:968) under its still-installed handshake WRITE keys AFTER the
    peer has already collapsed to the application READ epoch (the asymmetric exit),
    putting a `Handshake`-snapshot record in flight to an `Application`-read
    receiver — a snapshot-ONLY gate would then spuriously demand `k == 0`.  Gating
    the in-flight arm on the receiver's read epoch makes exactly that exit window
    vacuous, matching the Quiet arm.  The faithful-decode CONSUMER is unaffected: at
    a genuine handshake delivery the receiver has NOT yet received the record, so it
    is still handshake-read and the gate fires. **)
let cs_hs_seq_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToServer p ->
      (R.Handshake? (ASP.snap_wr p).R.epoch /\ R.Handshake? (ASP.rd s.server).R.epoch /\
       not (terminal_control s.server.CS.cs_model.CS.model_control)) ==>
         snap_hs_wseq p == hs_rseq s.server
  | _ ->
      (R.Handshake? (ASP.wr s.client).R.epoch /\ R.Handshake? (ASP.rd s.server).R.epoch /\
       not (terminal_control s.server.CS.cs_model.CS.model_control)) ==>
         hs_wseq s.client == hs_rseq s.server

(** ── S -> C direction (server writes, client reads). ──

    NON-CIRCULARITY (establish-then-consume ordering; Condition 2, CONFIRMED).
    The soundness of DROPPING `~terminal(client)` from the delivery arms rests on
    an ordering invisible from the definition, in the same form as the
    `hs_seq_pairing`/`hs_channel_seal_ok` gate notes:

      * ESTABLISHMENT is DECODE-FREE, at the SEND.  The in-flight seq-alignment arm
        `snap_hs_wseq p == hs_rseq client` is established by `lemma_hsp_server_send`
        purely from the pre-state Quiet `_` arm `hs_wseq server == hs_rseq client`
        (a COUNTING fact — the channel is single-slot, so every prior record was
        delivered-or-blocked; via the Quiet byte pairing / `lemma_hsp_quiet_both_zero`
        it is a right-cancellation over record counts).  The send transfers it by a
        FROZEN-SLOT step (`lemma_sent_preserves_rd_full`: a `Sent` step leaves
        `record_read` whole, and `p.pl_snap == a.server`), reading NO post-state and
        appealing to NO faithful decode.  So the pre-state alignment is a genuine
        pre-condition, never a consequence of the step it justifies.

      * DELIVERY CONSUMES it.  `lemma_hsp_deliver_to_client` uses the pre-state
        alignment (this arm) + material persistence
        (`CSL.lemma_client_hs_read_slot_link_persist`, control-free, survives
        `ControlFailed`) to PIN the in-flight record's faithful decode to the sent
        message and show the step advances read `+1` (coupling-post holds) or blocks.
        Alignment-PRE => decode => alignment-POST is an ordinary induction, NOT
        "alignment proves decode proves alignment".

    Because establishment goes decode-free at the send, there is NO real
    circularity, and the `~terminal` gate is in principle DROPPABLE (the falsity it
    dodges is machine-checked dead in `lemma_condition1_sc_delivery_excluded`
    above).  NOTE — the gate is RETAINED in the definition below pending completion
    of the delivery-arm extension (the terminal-`c'` case needs the send/receive
    seq-coupling `write-delta == read-delta` decomposed per message constructor;
    the base fact is Condition-1-clean but not a single-VC `()`).

    BLOCKED-CHANNEL (Condition 3).  A failed-reader Quiet `_` arm is reachable via
    `LocalFail` at a Quiet state (read and write seq both frozen and already equal,
    so `hs_wseq server == hs_rseq client` transfers verbatim), AND via a
    `deliver_to_client` that FAILS the client on a received in-flight alert
    (fail_model, StateMachine.fst:968) -> Quiet.  In the latter the alert send
    fail_models the SERVER too (`M.TlsAlert _,_ -> Sent -> fail_model`, :968-969,
    which freezes `model_record`), so BOTH seqs freeze in lock-step and the arm
    still reads `k == k`.  Once a genuine handshake record then blocks (handshake
    into the failed client -> `:822` None -> no successor), the channel stays
    `ToClient` forever (locals require Quiet), so all downstream Quiet `_` clauses
    are vacuous thereafter. **)
let sc_hs_seq_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToClient p ->
      (R.Handshake? (ASP.snap_wr p).R.epoch /\ R.Handshake? (ASP.rd s.client).R.epoch /\
       not (terminal_control s.client.CS.cs_model.CS.model_control)) ==>
         snap_hs_wseq p == hs_rseq s.client
  | _ ->
      (R.Handshake? (ASP.wr s.server).R.epoch /\ R.Handshake? (ASP.rd s.client).R.epoch /\
       not (terminal_control s.client.CS.cs_model.CS.model_control)) ==>
         hs_wseq s.server == hs_rseq s.client

(** The handshake-epoch record-seq pairing invariant. **)
let hs_seq_pairing (s:SY.tls_system_state) : prop =
  cs_hs_seq_ok s /\ sc_hs_seq_ok s

(** The HANDSHAKE-epoch in-flight SEAL + faithful-decode conjunct.

    This carries ONLY the `ToClient` (server->client) handshake faithful-decode
    bridge: an in-flight server->client PROTECTED-HANDSHAKE record, sealed under
    the server's handshake WRITE material, is faithfully decodable by the client's
    handshake READ material (key/iv agreement + single-record seal + roundtrip).
    The `ToServer` arm is `True`: the client never sends a protected
    handshake-WRITE record (its only handshake-stage send is the cleartext
    ClientHello, and its Finished is sent under app-write keys), so the server
    never receives a protected-handshake payload that stays handshake-read
    post-step.

    The gate MIRRORS `sc_hs_seq_ok`'s in-flight arm: BOTH the sealing snapshot's
    write epoch AND the receiver's read epoch must be `Handshake`, and the
    receiver must be non-terminal.  `~terminal(client)` is BACKWARD-MONOTONE
    (terminal is absorbing).  The `Handshake?(rd client)` conjunct is LOAD-BEARING:
    without it a server at handshake-write sending a protected `Close_notify` to a
    live non-terminal client already collapsed to `Application` read would falsify
    the bridge (handshake-write vs app-read material). **)
let hs_channel_seal_ok (s:SY.tls_system_state) : prop =
  match s.channel with
  | MP.ToClient p ->
      (R.Handshake? (ASP.snap_wr p).R.epoch /\
       R.Handshake? (ASP.rd s.client).R.epoch) ==>
        ASP.inflight_bridge_ready p.SY.pl_snap s.client.CS.cs_model p.SY.pl_sent p.SY.pl_raw
  | _ -> True

module SMR  = TLS13.Spec.StateMachine.Reachability
module RTC  = FStar.ReflexiveTransitiveClosure
module PC   = TLS13.System.ProgressCount
module SCB  = TLS13.System.SeqCountBase
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module HSZ  = TLS13.ConnectionState.HandshakeSeqZero
module WFL  = TLS13.Spec.WireFormatLemmas
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module ID   = FStar.IndefiniteDescription
module Sem  = TLS13.Wire.Semantics
module GHS  = TLS13.Wire.Generated.Handshake
module GCert = TLS13.Wire.Generated.Certificate
module GCL  = TLS13.Wire.Generated.Certificate_certificate_list
module GCertE = TLS13.Wire.Generated.CertificateEntry
module GCV  = TLS13.Wire.Generated.CertificateVerify
module GEE  = TLS13.Wire.Generated.EncryptedExtensions
module GFin = TLS13.Wire.Generated.Finished
module GA   = TLS13.Wire.Generated.Alert
module GAL  = TLS13.Wire.Generated.AlertLevel
module RVDH = TLS13.Wire.Spec.Reveal.Handshake
module RVA  = TLS13.Wire.Spec.Reveal.Alert
module RVR  = TLS13.Wire.Spec.Reveal.Record
module LP   = LowParse.Spec
module WFSM = Common.WireFormatStateMachine
module SNC  = TLS13.System.ServerNotCFR
module SMCorr = TLS13.Spec.StateMachine.Correspondence

(** ─────────────────────────────────────────────────────────────────────────
    MODEL-LEVEL handshake-epoch seq projections.  Definitionally
    `hs_wseq st == m_hwseq st.cs_model` and `hs_rseq st == m_hrseq st.cs_model`.
    ───────────────────────────────────────────────────────────────────────── **)
let m_hwseq (m:CS.connection_model) : nat =
  if R.Handshake? (ASP.m_wr m).R.epoch then (ASP.m_wr m).R.seq else 0
let m_hrseq (m:CS.connection_model) : nat =
  if R.Handshake? (ASP.m_rd m).R.epoch then (ASP.m_rd m).R.seq else 0

(** A `Sent` model step never touches `record_read`, so it leaves the
    handshake-epoch READ projection unchanged. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_sent_preserves_hread (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m CL.Sent msg == Some m')
      (ensures m_hrseq m' == m_hrseq m)
  = ()
#pop-options

(** A `Received` model step never touches `record_write`, so it leaves the
    handshake-epoch WRITE projection unchanged. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_recv_preserves_hwrite (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m CL.Received msg == Some m')
      (ensures m_hwseq m' == m_hwseq m)
  = ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    THE cs DIRECTION IS `0 == 0`.

    A CLIENT never bumps its handshake-epoch WRITE seq (its only handshake-write
    record is its own Finished, which SEALS at handshake-write seq 0 and then
    INSTALLS the application write epoch), and a SERVER never bumps its
    handshake-epoch READ seq (its only handshake-read record is the client
    Finished, whose receive INSTALLS the application read epoch).  So
    `hs_wseq client == 0` and `hs_rseq server == 0` at every reachable state, and
    the cs-direction pairing (`hs_wseq client == hs_rseq server`) is `0 == 0`.

    Both facts are STAGE-gated per DESIGN NOTE 1 of `HandshakeSeqZero` (a
    role-gate makes the SMT do cross-role case reasoning it will not do), lifted
    over `connection_state_consistent` by RTC closure.  The shapes are the same
    ones `HandshakeSeqZero` uses internally, replicated here because that module
    only exports the two point lemmas.
    ───────────────────────────────────────────────────────────────────────── **)

(** Client pre-Finished chain WRITE-seq-zero stage-gate.

    NOTE: This is deliberately CONTROL-GATED, not unconditional.  At the CF-send
    arm (StateMachine.fst:809), `ks_client_application_traffic` is still `None`
    (Lemmas.fst:6045), so `install_client_application_write_after_finished` takes
    its None branch and the client lands at `ControlApplicationData` with
    record_write `(Handshake, 1)` — a genuinely nonzero handshake write seq.  So
    `hs_wseq client == 0` is FALSE at that window; the projection is rescued only
    by the both-epoch gate in the coupling (server read is `Application` there).
    Hence the shape only pins seq 0 at the pre-CF handshake controls, where the
    write epoch is genuinely `Handshake` and no protected handshake record has
    been sealed yet. **)
let cw_shape (model:CS.connection_model) : prop =
  match model.CS.model_control with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsNotStarted
  | CS.ControlHandshaking CS.HsStarted
  | CS.ControlHandshaking CS.HsClientHelloSent
  | CS.ControlHandshaking CS.HsServerHelloReceived
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
  | CS.ControlHandshaking CS.HsCertificateReceived
  | CS.ControlHandshaking CS.HsCertificateValidated
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified
  | CS.ControlHandshaking CS.HsServerFinishedReceived
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    model.CS.model_record.CS.record_write.R.epoch =!= R.Handshake \/
    model.CS.model_record.CS.record_write.R.seq == 0
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_cw_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires cw_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures cw_shape model')
  = ()
#pop-options

let conn_cw_shape (st:CS.connection_state) : prop = cw_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_cw_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_cw_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_cw_shape st1)
  = let delta_w =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_cw_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_cw_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_cw_shape y); (SMR.connection_state_single_step x y)}
          conn_cw_shape x /\ SMR.connection_state_single_step x y ==> conn_cw_shape y)
  = introduce forall x y.
      conn_cw_shape x /\ SMR.connection_state_single_step x y ==> conn_cw_shape y
    with introduce _ ==> _ with _.
      lemma_delta_cw_shape x y

let lemma_initial_cw_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_cw_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_client_hwseq_zero (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_cw_shape st)
  = lemma_initial_cw_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_cw_shape ();
    let p = conn_cw_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** ══════════════════════════════════════════════════════════════════════════
    CONDITION 1 — MACHINE-CHECKED DEATH OF THE MOTIVATING FALSITY.

    The gate `~terminal(receiver)` on the `sc_hs_seq_ok`/`cs_hs_seq_ok` delivery
    arms was introduced to dodge the state: a HANDSHAKE-write record in flight
    (`snap_wr.seq` advanced, `+1`) delivered to a FAILED receiver whose read seq is
    frozen (`+0`), where the collapsing identity `snap_hs_wseq p == hs_rseq receiver`
    would read `1 == 0`.  These two lemmas show — machine-checked — that once the
    seq-alignment AND material persistence bricks put the pre-state alignment
    `snap_write.seq == receiver_read.seq` and the key/iv agreement in hand, that
    state is EXCLUDED BY FAITHFUL DECODE, not by the gate.

    SC direction (server->client).  `lemma_condition1_sc_delivery_excluded`: the
    receiver faithfully decodes the in-flight record to the SENT handshake message
    (bridge `CSL.lemma_received_..._decode_..._seal_peer`, needing exactly the seq
    alignment + material agreement), and a handshake message into a TERMINAL control
    routes `M.TlsHandshake _,_ -> step_handshake_message` -> `| _,_,_ -> None`
    (StateMachine.fst:822 — every `step_handshake_message` arm demands
    `ControlHandshaking <stage>`), so there is NO successor: the delivery step does
    not exist and the delivery arm is VACUOUS.

    CS direction (client->server), the mirror.  Killed by a DIFFERENT mechanism,
    independent of `~terminal`: the client never seals a PROTECTED handshake-WRITE
    record, so its handshake-epoch write projection is `0` at every reachable
    pre-application client control (`lemma_condition1_cs_client_hwseq_zero`, via
    `cw_shape`) — its handshake-stage send is the cleartext ClientHello (Initial
    write epoch) and its Finished is an app-write (Application epoch).  So no
    `ToServer` payload ever carries a `Handshake`-snapshot PROTECTED record with an
    advanced write seq: the `+1` that would form the `1 == 0` never happens on the
    client-write side.
    ══════════════════════════════════════════════════════════════════════════ **)

(* A handshake message RECEIVED at a TERMINAL control has no successor: every arm
   of `step_handshake_message` (StateMachine.fst:587-821) requires a
   `ControlHandshaking <stage>` control, so a `ControlFailed`/`ControlClosing`/
   `ControlClosed` receiver falls through to `| _,_,_ -> None` (:822), and
   `step_tls_message` routes `M.TlsHandshake` straight into it (:831). *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 20"
let lemma_handshake_into_terminal_none
  (m:CS.connection_model) (hmsg:M.handshake_msg)
  : Lemma
      (requires terminal_control m.CS.model_control)
      (ensures
        CS.step_handshake_message m CL.Received hmsg == None /\
        CS.step_tls_message m CL.Received (M.TlsHandshake hmsg) == None)
  = ()
#pop-options

(* SC-direction death: pre-state seq alignment + material agreement pin the
   in-flight record's faithful decode to the sent handshake message; a handshake
   message into the terminal receiver has NO successor.  So the falsifying delivery
   step to a failed receiver does not exist. *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_condition1_sc_delivery_excluded
  (sender receiver:CS.connection_model) (hmsg:M.handshake_msg) (raw:B.bytes)
  : Lemma
      (requires
        terminal_control receiver.CS.model_control /\
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
           SMKM.record_direction_material sender.CS.model_record.CS.record_write,
           SMKM.record_direction_material receiver.CS.model_record.CS.record_read
         with
         | Some sender_write, Some receiver_read ->
           SMKM.record_key_iv_material_agrees sender_write receiver_read
         | _, _ -> False) /\
        SMCan.sent_single_protected_message_seal sender (M.TlsHandshake hmsg) raw /\
        (let (content_type, fragment) = W.serialize_tls_message (M.TlsHandshake hmsg) in
         W.parse_tls_message content_type fragment == Some (M.TlsHandshake hmsg)))
      (ensures
        SMCan.received_single_protected_message_decode receiver (M.TlsHandshake hmsg) raw /\
        CS.step_tls_message receiver CL.Received (M.TlsHandshake hmsg) == None)
  = CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
      sender receiver (M.TlsHandshake hmsg) raw;
    lemma_handshake_into_terminal_none receiver hmsg
#pop-options

(* CS-direction (mirror) death: at every reachable pre-application client control
   the client's handshake-epoch WRITE projection is `0`, so no `+1` can form on the
   client-write side — the `cs` in-flight `Handshake?(snap_wr client)` case cannot
   carry an advanced protected handshake-write seq. *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_condition1_cs_client_hwseq_zero (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        (* exactly the pre-application client control set tracked by `cw_shape` *)
        (match st.CS.cs_model.CS.model_control with
         | CS.ControlNew
         | CS.ControlHandshaking CS.HsNotStarted
         | CS.ControlHandshaking CS.HsStarted
         | CS.ControlHandshaking CS.HsClientHelloSent
         | CS.ControlHandshaking CS.HsServerHelloReceived
         | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
         | CS.ControlHandshaking CS.HsCertificateReceived
         | CS.ControlHandshaking CS.HsCertificateValidated
         | CS.ControlHandshaking CS.HsCertificateVerifyReceived
         | CS.ControlHandshaking CS.HsCertificateVerifyVerified
         | CS.ControlHandshaking CS.HsServerFinishedReceived
         | CS.ControlHandshaking CS.HsServerFinishedVerified -> True
         | _ -> False))
      (ensures hs_wseq st == 0)
  = lemma_client_hwseq_zero st
#pop-options

(** Server pre-delivery chain READ-seq-zero stage-gate. **)
let sr_shape (model:CS.connection_model) : prop =
  match model.CS.model_control with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsNotStarted
  | CS.ControlHandshaking CS.HsAwaitingClientHello
  | CS.ControlHandshaking CS.HsClientHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent ->
    model.CS.model_record.CS.record_read.R.epoch =!= R.Handshake \/
    model.CS.model_record.CS.record_read.R.seq == 0
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_sr_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires sr_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures sr_shape model')
  = ()
#pop-options

let conn_sr_shape (st:CS.connection_state) : prop = sr_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_sr_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_sr_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_sr_shape st1)
  = let delta_w =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_sr_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_sr_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_sr_shape y); (SMR.connection_state_single_step x y)}
          conn_sr_shape x /\ SMR.connection_state_single_step x y ==> conn_sr_shape y)
  = introduce forall x y.
      conn_sr_shape x /\ SMR.connection_state_single_step x y ==> conn_sr_shape y
    with introduce _ ==> _ with _.
      lemma_delta_sr_shape x y

let lemma_initial_sr_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_sr_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_hrseq_zero (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_sr_shape st)
  = lemma_initial_sr_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_sr_shape ();
    let p = conn_sr_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** Server pre-EE chain WRITE-seq-zero stage-gate.  The write counter is never
    bumped within this chain: SH-send (HsClientHelloReceived -> HsServerHelloSent)
    does NOT `next_seq` the write (StateMachine.fst:617), and the first bump is at
    the EE send (HsServerHelloSent -> HsServerEncryptedFlightSent), which EXITS the
    chain (under `_ -> True`).  So the whole chain keeps `write.epoch =!= Handshake`
    (Initial) OR (post handshake-write install at HsServerHelloSent) `write.seq == 0`.
    Consumed at `HsServerHelloSent` by `lemma_server_hs_server_hello_sent_write_seq_zero`. **)
let sw_shape (model:CS.connection_model) : prop =
  match model.CS.model_control with
  | CS.ControlNew
  | CS.ControlHandshaking CS.HsNotStarted
  | CS.ControlHandshaking CS.HsAwaitingClientHello
  | CS.ControlHandshaking CS.HsClientHelloReceived
  | CS.ControlHandshaking CS.HsServerHelloSent ->
    model.CS.model_record.CS.record_write.R.epoch =!= R.Handshake \/
    model.CS.model_record.CS.record_write.R.seq == 0
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_sw_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires sw_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures sw_shape model')
  = ()
#pop-options

let conn_sw_shape (st:CS.connection_state) : prop = sw_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_sw_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_sw_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_sw_shape st1)
  = let delta_w =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_sw_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_sw_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_sw_shape y); (SMR.connection_state_single_step x y)}
          conn_sw_shape x /\ SMR.connection_state_single_step x y ==> conn_sw_shape y)
  = introduce forall x y.
      conn_sw_shape x /\ SMR.connection_state_single_step x y ==> conn_sw_shape y
    with introduce _ ==> _ with _.
      lemma_delta_sw_shape x y

let lemma_initial_sw_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_sw_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_hwseq_zero (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_sw_shape st)
  = lemma_initial_sw_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_sw_shape ();
    let p = conn_sw_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** conjA — a CONSISTENT server at `HsServerHelloSent` with a Handshake write epoch
    has write seq 0 (its handshake write keys were just installed; no protected send
    yet).  Used to close the cleartext-ServerHello in-flight case of the delivery. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_server_hs_server_hello_sent_write_seq_zero (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent)
      (ensures
        st.CS.cs_model.CS.model_record.CS.record_write.R.epoch =!= R.Handshake \/
        st.CS.cs_model.CS.model_record.CS.record_write.R.seq == 0)
  = lemma_server_hwseq_zero st
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    SHARED-SECRET reachable shape.  A Handshake record epoch (write OR read)
    forces `Some? ks_shared_secret`: the only step installing a Handshake record
    epoch is a `LocalInstallTrafficKeys{,ForRole}` whose legality demands
    `traffic_install_matches_key_schedule` = `Some? expected_traffic_secret` =
    `Some? ks_handshake_secret` (StateMachine.fst:1126, via `traffic_secret_for_label`),
    and `ks_handshake_secret`/`ks_shared_secret` are set TOGETHER (only in
    `derive_shared_secret_model`) and never cleared.  Carried as a per-step-stable
    reachable shape (RTC closure), the mirror of the `sw_shape` seq-zero machine.
    ═══════════════════════════════════════════════════════════════════════════ **)
let ss_shape (model:CS.connection_model) : prop =
  (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==>
     Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret) /\
  (R.Handshake? model.CS.model_record.CS.record_write.R.epoch ==>
     Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret) /\
  (R.Handshake? model.CS.model_record.CS.record_read.R.epoch ==>
     Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_ss_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires ss_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures ss_shape model')
  = match ev with
    | CS.ConnLocalEvent lev ->
      (match lev, model.CS.model_control with
       | CS.LocalInstallTrafficKeys install, CS.ControlHandshaking _ ->
         // legality => traffic_install_matches_key_schedule hs install
         //          => Some? (expected_traffic_secret ...) => Some? ks_handshake_secret
         (match install.CS.install_epoch with
          | CS.TrafficHandshake ->
              assert (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
          | CS.TrafficApplication -> ())
       | CS.LocalInstallTrafficKeysForRole role_install, CS.ControlHandshaking _ ->
         (match role_install.CS.install_payload.CS.install_epoch with
          | CS.TrafficHandshake ->
              assert (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
          | CS.TrafficApplication -> ())
       | _ -> ())
    | CS.ConnNetworkEvent _ -> ()
#pop-options

let conn_ss_shape (st:CS.connection_state) : prop = ss_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_ss_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_ss_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_ss_shape st1)
  = let delta_w =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_ss_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_ss_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_ss_shape y); (SMR.connection_state_single_step x y)}
          conn_ss_shape x /\ SMR.connection_state_single_step x y ==> conn_ss_shape y)
  = introduce forall x y.
      conn_ss_shape x /\ SMR.connection_state_single_step x y ==> conn_ss_shape y
    with introduce _ ==> _ with _.
      lemma_delta_ss_shape x y

let lemma_initial_ss_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_ss_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_ss_shape (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_ss_shape st)
  = lemma_initial_ss_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_ss_shape ();
    let p = conn_ss_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** A consistent endpoint with a Handshake WRITE epoch has its shared secret. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_consistent_hs_write_shared_secret (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        R.Handshake? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
  = lemma_consistent_ss_shape st

(** A consistent endpoint with a Handshake READ epoch has its shared secret. **)
let lemma_consistent_hs_read_shared_secret (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        R.Handshake? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
      (ensures Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
  = lemma_consistent_ss_shape st
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    CLIENT read-epoch CONTROL pin.  A non-failed CLIENT with a Handshake READ
    epoch is at one of the six client handshake-flight controls where both hellos
    are recorded (`client_stage_ok`).  The handshake READ key installs only at
    `HsServerHelloReceived` (`traffic_install_allowed_at_stage`), and the read
    epoch leaves `Handshake` (to `Application`) atomically at the server-Finished
    receive (`HsCertificateVerifyVerified -> HsServerFinishedVerified`), which
    installs the application read key in the SAME step (StateMachine.fst:738).
    Hence read stays `Handshake` exactly across the six controls below;
    `HsServerFinished{Received,Verified}` and `ControlApplicationData` already
    carry an Application read epoch, and the alert routes land in `ControlFailed`
    (excluded).  Role-gated (immutable) so server states are vacuous.  Carried as
    an RTC-stable shape.
    ═══════════════════════════════════════════════════════════════════════════ **)
let client_read_hs_control (st:CS.handshake_stage) : bool =
  match st with
  | CS.HsServerHelloReceived | CS.HsEncryptedExtensionsReceived
  | CS.HsCertificateReceived | CS.HsCertificateValidated
  | CS.HsCertificateVerifyReceived | CS.HsCertificateVerifyVerified -> true
  | _ -> false

let cr_ctrl_shape (model:CS.connection_model) : prop =
  (model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
   R.Handshake? model.CS.model_record.CS.record_read.R.epoch /\
   ~(CS.ControlFailed? model.CS.model_control)) ==>
    (match model.CS.model_control with
     | CS.ControlHandshaking st -> client_read_hs_control st
     | _ -> False)

#push-options "--fuel 2 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_step_cr_ctrl_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires cr_ctrl_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures cr_ctrl_shape model')
  = ()
#pop-options

let conn_cr_ctrl_shape (st:CS.connection_state) : prop = cr_ctrl_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_cr_ctrl_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_cr_ctrl_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_cr_ctrl_shape st1)
  = let delta_w =
      FStar.IndefiniteDescription.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_cr_ctrl_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_cr_ctrl_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_cr_ctrl_shape y); (SMR.connection_state_single_step x y)}
          conn_cr_ctrl_shape x /\ SMR.connection_state_single_step x y ==> conn_cr_ctrl_shape y)
  = introduce forall x y.
      conn_cr_ctrl_shape x /\ SMR.connection_state_single_step x y ==> conn_cr_ctrl_shape y
    with introduce _ ==> _ with _.
      lemma_delta_cr_ctrl_shape x y

let lemma_initial_cr_ctrl_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_cr_ctrl_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_cr_ctrl_shape (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_cr_ctrl_shape st)
  = lemma_initial_cr_ctrl_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_cr_ctrl_shape ();
    let p = conn_cr_ctrl_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    REACHABLE COUNTING LEMMAS.

    The gated per-endpoint handshake-region seq-counting invariants
    `SCB.pwrite_ok` (write side) and `SCB.pread_ok` (read side) hold at every
    REACHABLE endpoint state, established by trace induction over the official
    wire state machine.  The per-step preservation is discharged by the
    counting-algebra core of `SeqCountBase`, fed with the reachable coupling lifts
    (`connection_state_consistent`) and the reachable byte-parse witnesses.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** A single legal connection step preserves `connection_state_consistent`
    (config is immutable, and one step extends the reflexive-transitive
    reachability closure). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_step_preserves_consistent (st0 st1:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        SMR.connection_state_single_step st0 st1)
      (ensures SMR.connection_state_consistent st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    WStep.lemma_step_model_preserves_config
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
    // config immutable ⇒ initial states coincide
    assert (st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config);
    // one step ⇒ evolves st0 st1 (closure_step SMTPat)
    RTC.closure_step SMR.connection_state_single_step st0 st1;
    assert (SMR.connection_state_evolves st0 st1);
    // consistent st0 : evolves (initial cfg) st0 ; transitivity ⇒ evolves (initial cfg) st1
    assert (SMR.connection_state_evolves
              (CS.initial st0.CS.cs_model.CS.model_config) st0);
    assert (SMR.connection_state_evolves
              (CS.initial st0.CS.cs_model.CS.model_config) st1)
#pop-options

(** An official server step is a single legal connection delta. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_server_step_single_step
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 ev st1 out)
      (ensures SMR.connection_state_single_step st0 st1)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         SMCan.canonical_wire_step st0 st1 conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns SMR.connection_state_single_step st0 st1
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent =
              WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
            CS.delta_raw_received = CW.wire_serialize wire } in
        introduce exists (delta:CS.connection_delta).
          CS.legal_connection_delta st0 delta st1
        with d and ()
      )
    | SM.LocalEvent local ->
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (ES.server_representation_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
      returns SMR.connection_state_single_step st0 st1
      with _.
      (
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        introduce exists (delta:CS.connection_delta).
          CS.legal_connection_delta st0 delta st1
        with d and ()
      )
#pop-options

(** `pwrite_ok`/`pread_ok` hold trivially at the initial state (Initial epochs,
    empty wire logs). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_pwrite_ok_initial (cfg:CS.connection_config)
  : Lemma (ensures SCB.pwrite_ok (CS.initial cfg))
  = WStep.lemma_raw_appdata_count_empty ();
    WStep.lemma_raw_appdata_count_seq_equal
      (CS.initial cfg).CS.cs_wire_log.CL.raw_sent B.empty

let lemma_pread_ok_initial (cfg:CS.connection_config)
  : Lemma (ensures SCB.pread_ok (CS.initial cfg))
  = WStep.lemma_raw_appdata_count_empty ();
    WStep.lemma_raw_appdata_count_seq_equal
      (CS.initial cfg).CS.cs_wire_log.CL.raw_received B.empty
#pop-options

(** WRITE-side counting preserved by a SERVER SEND (nonempty sent delta): the
    protected flight sends (EE/Cert/CV/SF) bump the handshake-write seq by one
    and append one ApplicationData record; the cleartext ServerHello send appends
    a Handshake record (count 0) at the Initial write epoch.  Fed by the
    `SeqCountBase` model-fact core plus the append law.  The ClientHello premise
    of the core is vacuous for a server: a `Sent` ClientHello is legal only at
    `HsStarted`, which `server_ctrl_ok` excludes. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_server_sent_pwrite
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msg:M.tls_message) (msgs:list CW.wire_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        d.CS.delta_event == SMKM.sent_tls_event msg /\
        SMCan.sent_event_nonempty_seal_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
        SCB.pwrite_ok st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        SCB.record_key_epoch_coupling st0.CS.cs_model /\
        WStep.server_ctrl_ok st0.CS.cs_model.CS.model_control /\
        WF.parses_as CW.tls_record_wire_format
          st0.CS.cs_wire_log.CL.raw_sent msgs Seq.empty)
      (ensures SCB.pwrite_ok st1)
  = // cleartext ServerHello send ⇒ appdata count 0
    introduce (M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) ==>
              WStep.raw_appdata_count d.CS.delta_raw_sent == 0
    with _.
      WStep.lemma_cleartext_raw_count_zero msg d.CS.delta_raw_sent;
    // ClientHello send is impossible for a server (legal only at HsStarted)
    introduce (M.TlsHandshake? msg /\ M.ClientHello? (M.TlsHandshake?._0 msg)) ==>
              WStep.raw_appdata_count d.CS.delta_raw_sent == 0
    with _.
      assert False;
    SCB.lemma_sent_write_model_facts
      st0.CS.cs_model msg st1.CS.cs_model
      d.CS.delta_raw_sent d.CS.delta_raw_received;
    WStep.lemma_raw_appdata_count_append
      st0.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent msgs;
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent);
    SCB.lemma_pre_appdata_back st0 d st1
#pop-options

(** Per-step WRITE-side counting preservation for a reachable server. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_server_step_pwrite
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        SCB.pwrite_ok st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.server_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0 /\
        WStep.server_ctrl_ok st0.CS.cs_model.CS.model_control)
      (ensures SCB.pwrite_ok st1)
  = let cfg = st0.CS.cs_model.CS.model_config in
    SCB.lemma_consistent_record_key_epoch_coupling st0;
    SCB.lemma_consistent_record_schedule_coupling st0;
    SCB.lemma_consistent_record_app_epoch_coupling st0;
    SCB.lemma_consistent_app_slots_none_shape st0;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         SMCan.canonical_wire_step st0 st1 conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns SCB.pwrite_ok st1
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent =
              WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
            CS.delta_raw_received = CW.wire_serialize wire } in
        SCB.lemma_pwrite_received st0 d st1 msg
      )
    | SM.LocalEvent local ->
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (ES.server_representation_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
      returns SCB.pwrite_ok st1
      with _.
      (
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        match conn_ev with
        | CS.ConnLocalEvent _ ->
          SCB.lemma_server_local_pwrite st0 d st1
        | CS.ConnNetworkEvent dm ->
          (match dm.CL.message_direction with
           | CL.Received ->
             assert (conn_ev == SMKM.received_tls_event dm.CL.message_value);
             SCB.lemma_pwrite_received st0 d st1 dm.CL.message_value
           | CL.Sent ->
             let msg = dm.CL.message_value in
             assert (conn_ev == SMKM.sent_tls_event msg);
             SCB.lemma_server_reachable_raw_sent_parses cfg st0;
             eliminate exists (msgs:list CW.wire_message).
               WF.parses_as CW.tls_record_wire_format
                 st0.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
             returns SCB.pwrite_ok st1
             with _.
               lemma_server_sent_pwrite st0 d st1 msg msgs)
      )
#pop-options

(** Trace-induction driver: WRITE-side counting is preserved along any official
    reachable server trace, threading `pwrite_ok`, `connection_state_consistent`,
    `server_reachable` and `server_ctrl_ok` as induction invariants. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_server_trace_pwrite
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        SCB.pwrite_ok st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.server_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0 /\
        WStep.server_ctrl_ok st0.CS.cs_model.CS.model_control)
      (ensures SCB.pwrite_ok st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      let cfg = st0.CS.cs_model.CS.model_config in
      // per-step preservation of pwrite_ok
      lemma_server_step_pwrite st0 tr.SM.tr_event s' tr.SM.tr_output;
      // re-establish the induction invariants at s'
      lemma_server_step_single_step st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_step_preserves_consistent st0 s';
      WStep.lemma_server_reachable_step
        (CS.initial cfg) st0 s' tr.SM.tr_event tr.SM.tr_output;
      WStep.lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      // config is immutable ⇒ s'.config == cfg
      assert (s'.CS.cs_model.CS.model_config == cfg);
      lemma_server_trace_pwrite init s' st1 rest
#pop-options

(** ═══ SERVER write-side reachable counting invariant. ═══ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_pwrite_ok (st:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures SCB.pwrite_ok st)
  = let cfg = st.CS.cs_model.CS.model_config in
    let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace st
    returns SCB.pwrite_ok st
    with _.
    (
      lemma_pwrite_ok_initial cfg;
      WStep.lemma_server_reachable_initial cfg;
      // init is consistent (reflexivity of evolves) and server_ctrl_ok (ControlNew)
      assert (SMR.connection_state_evolves (CS.initial cfg) init);
      lemma_server_trace_pwrite init init st trace
    )
#pop-options

(** ── CLIENT READ-side reachable counting (mirror of the server write side). ── **)

(** An official client step is a single legal connection delta. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_step_single_step
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 ev st1 out)
      (ensures SMR.connection_state_single_step st0 st1)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         SMCan.canonical_wire_step st0 st1 conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.network_input_message_projection st0 wire msg /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns SMR.connection_state_single_step st0 st1
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent =
              WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
            CS.delta_raw_received = CW.wire_serialize wire } in
        introduce exists (delta:CS.connection_delta).
          CS.legal_connection_delta st0 delta st1
        with d and ()
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
      returns SMR.connection_state_single_step st0 st1
      with _.
      (
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        introduce exists (delta:CS.connection_delta).
          CS.legal_connection_delta st0 delta st1
        with d and ()
      )
#pop-options

(** READ-side counting preserved by a CLIENT RECEIVE (nonempty received delta):
    protected receives (EE/Cert/CV/Finished) bump the handshake-read seq by one
    and append one ApplicationData record; cleartext receives (ServerHello / HRR /
    ChangeCipherSpec / ClientHello) append a non-ApplicationData record (count 0).
    Mirror of `lemma_server_sent_pwrite`. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_client_recv_pread
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msg:M.tls_message) (msgs:list CW.wire_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        d.CS.delta_event == SMKM.received_tls_event msg /\
        SMCan.received_event_nonempty_decode_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received /\
        SCB.pread_ok st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        SCB.record_key_epoch_coupling st0.CS.cs_model /\
        WF.parses_as CW.tls_record_wire_format
          st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty)
      (ensures SCB.pread_ok st1)
  = SCB.lemma_recv_read_model_facts
      st0.CS.cs_model msg st1.CS.cs_model
      d.CS.delta_raw_sent d.CS.delta_raw_received;
    WStep.lemma_raw_appdata_count_append
      st0.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received msgs;
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received);
    SCB.lemma_pre_appdata_back st0 d st1
#pop-options

(** Per-step READ-side counting preservation for a reachable client. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_client_step_pread
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        SCB.pread_ok st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.client_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures SCB.pread_ok st1)
  = let cfg = st0.CS.cs_model.CS.model_config in
    SCB.lemma_consistent_record_key_epoch_coupling st0;
    SCB.lemma_consistent_record_schedule_coupling st0;
    SCB.lemma_consistent_record_app_epoch_coupling st0;
    SCB.lemma_consistent_app_slots_none_shape st0;
    match ev with
    | SM.WireEvent wire ->
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         SMCan.canonical_wire_step st0 st1 conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.network_input_message_projection st0 wire msg /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns SCB.pread_ok st1
      with _.
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent =
              WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
            CS.delta_raw_received = CW.wire_serialize wire } in
        assert (conn_ev == SMKM.received_tls_event msg);
        WStep.lemma_client_reachable_raw_received_parses cfg st0;
        eliminate exists (msgs:list CW.wire_message).
          WF.parses_as CW.tls_record_wire_format
            st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty
        returns SCB.pread_ok st1
        with _.
          lemma_client_recv_pread st0 d st1 msg msgs
      )
    | SM.LocalEvent local ->
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.client_local_event_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 st1 conn_ev raw_sent B.empty)
      returns SCB.pread_ok st1
      with _.
      (
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev;
            CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        match conn_ev with
        | CS.ConnLocalEvent _ ->
          SCB.lemma_client_local_pread st0 d st1
        | CS.ConnNetworkEvent dm ->
          (match dm.CL.message_direction with
           | CL.Sent ->
             assert (conn_ev == SMKM.sent_tls_event dm.CL.message_value);
             SCB.lemma_pread_sent st0 d st1 dm.CL.message_value
           | CL.Received ->
             assert (conn_ev == SMKM.received_tls_event dm.CL.message_value);
             WStep.lemma_client_reachable_raw_received_parses cfg st0;
             eliminate exists (msgs:list CW.wire_message).
               WF.parses_as CW.tls_record_wire_format
                 st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty
             returns SCB.pread_ok st1
             with _.
               lemma_client_recv_pread st0 d st1 dm.CL.message_value msgs)
      )
#pop-options

(** Trace-induction driver: READ-side counting is preserved along any official
    reachable client trace. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_trace_pread
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        SCB.pread_ok st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.client_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures SCB.pread_ok st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      let cfg = st0.CS.cs_model.CS.model_config in
      lemma_client_step_pread st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_single_step st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_step_preserves_consistent st0 s';
      WStep.lemma_client_reachable_step
        (CS.initial cfg) st0 s' tr.SM.tr_event tr.SM.tr_output;
      WStep.lemma_client_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event st0.CS.cs_model ce /\
        CS.step_model st0.CS.cs_model ce == Some s'.CS.cs_model
      returns s'.CS.cs_model.CS.model_config == cfg
      with _.
        WStep.lemma_step_model_preserves_config st0.CS.cs_model ce s'.CS.cs_model;
      lemma_client_trace_pread init s' st1 rest
#pop-options

(** ═══ CLIENT read-side reachable counting invariant. ═══ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_reachable_pread_ok (st:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        WFL.supported_client_config_wire_profile st.CS.cs_model.CS.model_config /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures SCB.pread_ok st)
  = let cfg = st.CS.cs_model.CS.model_config in
    let init : EC.client_initial_state = CS.initial cfg in
    let sm = WStep.client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace st
    returns SCB.pread_ok st
    with _.
    (
      lemma_pread_ok_initial cfg;
      WStep.lemma_client_reachable_initial cfg;
      assert (SMR.connection_state_evolves (CS.initial cfg) init);
      lemma_client_trace_pread init init st trace
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    sc-DIRECTION POINTWISE ALIGNMENT (the establishment payoff).

    At a Quiet state where BOTH the server's write and the client's read are at
    the Handshake record epoch AND both endpoints are still in the honest
    pre-application-data region, the server's handshake-write seq equals the
    client's handshake-read seq.  This is exactly `SCB.lemma_hseq_from_counts`
    fed by the two reachable counting invariants and the Quiet `byte_pairing`
    byte-equality `ss == cr`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_sc_quiet_align (a:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        MP.Quiet? a.channel /\
        R.Handshake? (ASP.wr a.server).R.epoch /\
        R.Handshake? (ASP.rd a.client).R.epoch /\
        PC.pre_appdata_control a.server.CS.cs_model.CS.model_control /\
        PC.pre_appdata_control a.client.CS.cs_model.CS.model_control)
      (ensures hs_wseq a.server == hs_rseq a.client)
  = lemma_server_reachable_pwrite_ok a.server;
    lemma_client_reachable_pread_ok a.client;
    SCB.lemma_hseq_from_counts a.server a.client
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    UNGATED REACHABLE COUNTING : `record_write.seq <= raw_appdata_count raw_sent`
    (write side) and the read-side mirror.  These hold at EVERY reachable state
    (including closing / failed), unlike the gated equalities `pwrite_ok`/`pread_ok`.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** LOCAL re-proof of the (un-exported) record-stream decomposition: a positive
    record count peels the head record and leaves a tail decomposing into
    `count - 1` records of the same outer type.  Mirrors
    `TLS13.ConnectionState.Lemmas.lemma_raw_records_exactly_nonempty_decompose`
    (which is not in that module's `.fsti`), over the transparent `ConnectionLog`. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_hsp_raw_records_exactly_decompose
  (raw:B.bytes) (outer:T.content_type) (count:nat)
  : Lemma
      (requires CS.raw_records_exactly raw outer count /\ count > 0)
      (ensures exists (fragment:M.sealed_record) (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\ consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         L.length tail.CL.values == count - 1 /\
         CS.all_records_outer_type outer tail.CL.values))
  = let parsed = CL.parse_record_prefix raw in
    assert (CL.record_stream_serializes raw parsed);
    assert (Seq.equal parsed.CL.residual B.empty);
    assert (L.length parsed.CL.values == count);
    assert (CS.all_records_outer_type outer parsed.CL.values);
    match W.parse_record raw with
    | None ->
      assert (B.length raw + 1 > 0);
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    | Some (content_type, fragment, consumed) ->
      W.lemma_parse_record_serializes raw;
      if consumed = 0 || consumed > B.length raw then (
        assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
        assert (parsed.CL.values == []);
        assert False
      ) else (
        let rest = Seq.slice raw consumed (B.length raw) in
        let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
        let record =
          { M.record_outer_type = content_type;
            M.record_fragment = fragment } in
        assert (CL.parse_record_prefix raw ==
          {
            CL.values = record :: tail.CL.values;
            CL.consumed = consumed + tail.CL.consumed;
            CL.residual = tail.CL.residual;
          });
        assert (parsed.CL.values == record :: tail.CL.values);
        assert (parsed.CL.residual == tail.CL.residual);
        assert (CS.all_records_outer_type outer (record :: tail.CL.values));
        assert (content_type == outer);
        assert (CS.all_records_outer_type outer tail.CL.values);
        CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
        assert (CL.record_stream_serializes rest tail);
        assert (Seq.equal tail.CL.residual B.empty);
        assert (L.length tail.CL.values == count - 1);
        assert (W.parse_record raw == Some (outer, fragment, consumed));
        introduce exists (fragment':M.sealed_record) (consumed':nat).
          W.parse_record raw == Some (outer, fragment', consumed') /\
          consumed' > 0 /\ consumed' <= B.length raw /\
          (let rest' = Seq.slice raw consumed' (B.length raw) in
           let tail' = CL.parse_record_prefix_fuel (B.length raw) rest' in
           CL.record_stream_serializes rest' tail' /\
           Seq.equal tail'.CL.residual B.empty /\
           L.length tail'.CL.values == count - 1 /\
           CS.all_records_outer_type outer tail'.CL.values)
        with fragment consumed
        and ()
      )
#pop-options

(** GENERAL COUNT BRIDGE: a byte log that decomposes EXACTLY into `n`
    ApplicationData records has appdata-count `n`.  (The gated chain only needed
    the `n == 1` special case `WStep.lemma_protected_raw_count_one`.)  Structural
    recursion on `n`, peeling one record per step. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let rec lemma_raw_records_exactly_appdata_count (raw:B.bytes) (n:nat)
  : Lemma
      (requires CS.raw_records_exactly raw T.Application_data n)
      (ensures WStep.raw_appdata_count raw == n)
      (decreases n)
  = if n = 0 then (
      WStep.lemma_raw_records_exactly_zero_empty raw T.Application_data;
      WStep.lemma_raw_appdata_count_empty ();
      WStep.lemma_raw_appdata_count_seq_equal raw B.empty
    ) else (
      lemma_hsp_raw_records_exactly_decompose raw T.Application_data n;
      eliminate exists (fragment:M.sealed_record) (consumed:nat).
        W.parse_record raw == Some (T.Application_data, fragment, consumed) /\
        consumed > 0 /\ consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         L.length tail.CL.values == n - 1 /\
         CS.all_records_outer_type T.Application_data tail.CL.values)
      returns WStep.raw_appdata_count raw == n
      with _.
      (
        let rest = Seq.slice raw consumed (B.length raw) in
        let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
        W.lemma_parse_record_implies_parse_record_wire raw;
        W.lemma_parse_record_wire_some_consumed_positive
          raw T.Application_data fragment consumed;
        Seq.lemma_len_slice raw consumed (B.length raw);
        CL.lemma_parse_record_prefix_fuel_eq_parse_record_prefix (B.length raw) rest;
        assert (CL.parse_record_prefix rest == tail);
        assert (CS.raw_records_exactly rest T.Application_data (n - 1));
        lemma_raw_records_exactly_appdata_count rest (n - 1)
      )
    )
#pop-options

(** UNGATED per-SENT-event WRITE-seq bound (the `<=` analogue of the gated
    equality `SCB.lemma_sent_write_model_facts`).  On a Sent event: the protected
    handshake sends bump the write seq by one against one appdata record; an
    ApplicationData send advances it by `n` against `n` appdata records; a
    Close_notify send bumps by one against one appdata record; every other send
    leaves `record_write` untouched (or installs at seq 0 / the Application
    epoch).  In all cases the seq rise is bounded by the sent-delta appdata count,
    and any move INTO the Handshake epoch (there are none on a Sent event) would
    reset the seq to 0. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_write_seq_step_bound_sent
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.legal_event m (SMKM.sent_tls_event msg) /\
        CS.step_model m (SMKM.sent_tls_event msg) == Some m' /\
        CS.event_raw_delta_legal m (SMKM.sent_tls_event msg) rs rr /\
        SCB.record_key_epoch_coupling m)
      (ensures
        (let w0 = m.CS.model_record.CS.record_write in
         let w1 = m'.CS.model_record.CS.record_write in
         w1.R.epoch == R.Handshake ==>
           ((w0.R.epoch == R.Handshake ==>
               w1.R.seq <= w0.R.seq + WStep.raw_appdata_count rs) /\
            (~(w0.R.epoch == R.Handshake) ==> w1.R.seq == 0))))
  = match msg with
    | M.TlsHandshake (M.EncryptedExtensions _)
    | M.TlsHandshake (M.Certificate _)
    | M.TlsHandshake (M.CertificateVerify _)
    | M.TlsHandshake (M.Finished _) ->
      assert (CS.raw_records_exactly rs T.Application_data 1);
      WStep.lemma_protected_raw_count_one rs
    | M.TlsApplicationData bytes ->
      let n = RF.application_data_record_count bytes in
      assert (CS.raw_records_exactly rs T.Application_data n);
      lemma_raw_records_exactly_appdata_count rs n;
      ASP.lemma_advance_direction_records_seq m.CS.model_record.CS.record_write n;
      ASP.lemma_advance_direction_records_epoch m.CS.model_record.CS.record_write n
    | M.TlsAlert _ ->
      assert (CS.raw_records_exactly rs T.Application_data 1);
      WStep.lemma_protected_raw_count_one rs
    | _ -> ()
#pop-options

(** UNGATED per-event WRITE-seq bound for ANY legal event.  A local event leaves
    `record_write` untouched or installs it at seq 0; a received event never
    touches `record_write`; a sent event is handled by
    `lemma_write_seq_step_bound_sent`. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_write_seq_step_bound
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        CS.event_raw_delta_legal m ev rs rr /\
        SCB.record_key_epoch_coupling m)
      (ensures
        (let w0 = m.CS.model_record.CS.record_write in
         let w1 = m'.CS.model_record.CS.record_write in
         w1.R.epoch == R.Handshake ==>
           ((w0.R.epoch == R.Handshake ==>
               w1.R.seq <= w0.R.seq + WStep.raw_appdata_count rs) /\
            (~(w0.R.epoch == R.Handshake) ==> w1.R.seq == 0))))
  = match ev with
    | CS.ConnLocalEvent local ->
      assert (m'.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write \/
              m'.CS.model_record.CS.record_write.R.seq == 0)
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Received ->
         assert (m'.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write)
       | CL.Sent ->
         assert (ev == SMKM.sent_tls_event dm.CL.message_value);
         lemma_write_seq_step_bound_sent m dm.CL.message_value m' rs rr)
#pop-options

(** UNGATED write-side counting predicate: at the Handshake write epoch, the
    write seq is bounded by the appdata-record count of the sent byte log.  Holds
    at EVERY reachable state (closing / failed included). **)
let pwrite_le (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
    st.CS.cs_model.CS.model_record.CS.record_write.R.seq <=
      WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_sent

(** `pwrite_le` holds at the initial state (Initial write epoch, vacuous). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_pwrite_le_initial (cfg:CS.connection_config)
  : Lemma (ensures pwrite_le (CS.initial cfg))
  = ()
#pop-options

(** COUNTING ALGEBRA: a single legal connection delta preserves `pwrite_le`.
    Count monotonicity (`lemma_raw_appdata_count_append`) plus the per-event
    write-seq bound feed the inequality directly, threading the pre-state bound as
    induction hypothesis. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pwrite_le_algebra
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msgs:list CW.wire_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        pwrite_le st0 /\
        SCB.record_key_epoch_coupling st0.CS.cs_model /\
        WF.parses_as CW.tls_record_wire_format
          st0.CS.cs_wire_log.CL.raw_sent msgs Seq.empty)
      (ensures pwrite_le st1)
  = lemma_write_seq_step_bound
      st0.CS.cs_model d.CS.delta_event st1.CS.cs_model
      d.CS.delta_raw_sent d.CS.delta_raw_received;
    WStep.lemma_raw_appdata_count_append
      st0.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent msgs;
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent d.CS.delta_raw_sent)
#pop-options

(** Per-step preservation of `pwrite_le` for a reachable server: extract the
    legal delta (single-step + indefinite description), the reachable byte-parse
    witness, and the record/key coupling, then apply the algebra. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_step_pwrite_le
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        pwrite_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.server_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pwrite_le st1)
  = let cfg = st0.CS.cs_model.CS.model_config in
    lemma_server_step_single_step st0 ev st1 out;
    SCB.lemma_consistent_record_key_epoch_coupling st0;
    SCB.lemma_server_reachable_raw_sent_parses cfg st0;
    let d = ID.indefinite_description_ghost
              CS.connection_delta
              (fun delta -> CS.legal_connection_delta st0 delta st1) in
    eliminate exists (msgs:list CW.wire_message).
      WF.parses_as CW.tls_record_wire_format
        st0.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
    returns pwrite_le st1
    with _.
      lemma_pwrite_le_algebra st0 d st1 msgs
#pop-options

(** Trace-induction driver: `pwrite_le` is preserved along any reachable server
    trace, threading `pwrite_le`, `connection_state_consistent` and
    `server_reachable`. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_server_trace_pwrite_le
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        pwrite_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.server_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pwrite_le st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      let cfg = st0.CS.cs_model.CS.model_config in
      lemma_server_step_pwrite_le st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_step_single_step st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_step_preserves_consistent st0 s';
      WStep.lemma_server_reachable_step
        (CS.initial cfg) st0 s' tr.SM.tr_event tr.SM.tr_output;
      WStep.lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      assert (s'.CS.cs_model.CS.model_config == cfg);
      lemma_server_trace_pwrite_le init s' st1 rest
#pop-options

(** ═══ SERVER write-side UNGATED reachable counting invariant. ═══ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_pwrite_le (st:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures pwrite_le st)
  = let cfg = st.CS.cs_model.CS.model_config in
    let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace st
    returns pwrite_le st
    with _.
    (
      lemma_pwrite_le_initial cfg;
      WStep.lemma_server_reachable_initial cfg;
      assert (SMR.connection_state_evolves (CS.initial cfg) init);
      lemma_server_trace_pwrite_le init init st trace
    )
#pop-options

(** ═══ TARGET 1 : SERVER write-side handshake-seq ≤ appdata count. ═══ **)
let lemma_server_reachable_writehs_seq_le_count (st:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        st.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
          st.CS.cs_model.CS.model_record.CS.record_write.R.seq <=
            WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_sent)
  = lemma_server_reachable_pwrite_le st

(** ─── CLIENT READ side: the exact mirror of the server write side. ─────────── **)

(** UNGATED per-RECEIVED-event READ-seq bound (mirror of
    `lemma_write_seq_step_bound_sent`).  Every protected received record
    (handshake flight, application data, post-handshake, close alert) advances the
    read seq by one against exactly one appdata record; cleartext receives leave
    `record_read` untouched. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_read_seq_step_bound_recv
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.legal_event m (SMKM.received_tls_event msg) /\
        CS.step_model m (SMKM.received_tls_event msg) == Some m' /\
        CS.event_raw_delta_legal m (SMKM.received_tls_event msg) rs rr /\
        SCB.record_key_epoch_coupling m)
      (ensures
        (let r0 = m.CS.model_record.CS.record_read in
         let r1 = m'.CS.model_record.CS.record_read in
         r1.R.epoch == R.Handshake ==>
           ((r0.R.epoch == R.Handshake ==>
               r1.R.seq <= r0.R.seq + WStep.raw_appdata_count rr) /\
            (~(r0.R.epoch == R.Handshake) ==> r1.R.seq == 0))))
  = match msg with
    | M.TlsHandshake (M.EncryptedExtensions _)
    | M.TlsHandshake (M.Certificate _)
    | M.TlsHandshake (M.CertificateVerify _)
    | M.TlsHandshake (M.Finished _) ->
      assert (CS.raw_records_exactly rr T.Application_data 1);
      WStep.lemma_protected_raw_count_one rr
    | M.TlsApplicationData _ ->
      assert (CS.raw_records_exactly rr T.Application_data 1);
      WStep.lemma_protected_raw_count_one rr
    | M.TlsIgnoredPostHandshake _ ->
      assert (CS.raw_records_exactly rr T.Application_data 1);
      WStep.lemma_protected_raw_count_one rr
    | M.TlsAlert _ ->
      assert (CS.raw_records_exactly rr T.Application_data 1);
      WStep.lemma_protected_raw_count_one rr
    | _ -> ()
#pop-options

(** UNGATED per-event READ-seq bound for ANY legal event.  A local event leaves
    `record_read` untouched or installs it at seq 0; a sent event never touches
    `record_read`; a received event is handled by
    `lemma_read_seq_step_bound_recv`. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_read_seq_step_bound
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        CS.event_raw_delta_legal m ev rs rr /\
        SCB.record_key_epoch_coupling m)
      (ensures
        (let r0 = m.CS.model_record.CS.record_read in
         let r1 = m'.CS.model_record.CS.record_read in
         r1.R.epoch == R.Handshake ==>
           ((r0.R.epoch == R.Handshake ==>
               r1.R.seq <= r0.R.seq + WStep.raw_appdata_count rr) /\
            (~(r0.R.epoch == R.Handshake) ==> r1.R.seq == 0))))
  = match ev with
    | CS.ConnLocalEvent local ->
      assert (m'.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read \/
              m'.CS.model_record.CS.record_read.R.seq == 0)
    | CS.ConnNetworkEvent dm ->
      (match dm.CL.message_direction with
       | CL.Sent ->
         assert (m'.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read)
       | CL.Received ->
         assert (ev == SMKM.received_tls_event dm.CL.message_value);
         lemma_read_seq_step_bound_recv m dm.CL.message_value m' rs rr)
#pop-options

(** UNGATED read-side counting predicate (mirror of `pwrite_le`). **)
let pread_le (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
    st.CS.cs_model.CS.model_record.CS.record_read.R.seq <=
      WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_received

(** `pread_le` holds at the initial state (Initial read epoch, vacuous). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_pread_le_initial (cfg:CS.connection_config)
  : Lemma (ensures pread_le (CS.initial cfg))
  = ()
#pop-options

(** COUNTING ALGEBRA (read side). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pread_le_algebra
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  (msgs:list CW.wire_message)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        pread_le st0 /\
        SCB.record_key_epoch_coupling st0.CS.cs_model /\
        WF.parses_as CW.tls_record_wire_format
          st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty)
      (ensures pread_le st1)
  = lemma_read_seq_step_bound
      st0.CS.cs_model d.CS.delta_event st1.CS.cs_model
      d.CS.delta_raw_sent d.CS.delta_raw_received;
    WStep.lemma_raw_appdata_count_append
      st0.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received msgs;
    WStep.lemma_raw_appdata_count_seq_equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received d.CS.delta_raw_received)
#pop-options

(** Per-step preservation of `pread_le` for a reachable client. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_step_pread_le
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        pread_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.client_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pread_le st1)
  = let cfg = st0.CS.cs_model.CS.model_config in
    lemma_client_step_single_step st0 ev st1 out;
    SCB.lemma_consistent_record_key_epoch_coupling st0;
    WStep.lemma_client_reachable_raw_received_parses cfg st0;
    let d = ID.indefinite_description_ghost
              CS.connection_delta
              (fun delta -> CS.legal_connection_delta st0 delta st1) in
    eliminate exists (msgs:list CW.wire_message).
      WF.parses_as CW.tls_record_wire_format
        st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty
    returns pread_le st1
    with _.
      lemma_pread_le_algebra st0 d st1 msgs
#pop-options

(** Trace-induction driver: `pread_le` is preserved along any reachable client
    trace. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_trace_pread_le
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        pread_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.client_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pread_le st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      let cfg = st0.CS.cs_model.CS.model_config in
      lemma_client_step_pread_le st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_single_step st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_step_preserves_consistent st0 s';
      WStep.lemma_client_reachable_step
        (CS.initial cfg) st0 s' tr.SM.tr_event tr.SM.tr_output;
      WStep.lemma_client_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event st0.CS.cs_model ce /\
        CS.step_model st0.CS.cs_model ce == Some s'.CS.cs_model
      returns s'.CS.cs_model.CS.model_config == cfg
      with _.
        WStep.lemma_step_model_preserves_config st0.CS.cs_model ce s'.CS.cs_model;
      lemma_client_trace_pread_le init s' st1 rest
#pop-options

(** ═══ CLIENT read-side UNGATED reachable counting invariant. ═══ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_reachable_pread_le (st:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures pread_le st)
  = let cfg = st.CS.cs_model.CS.model_config in
    let init : EC.client_initial_state = CS.initial cfg in
    let sm = WStep.client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace st
    returns pread_le st
    with _.
    (
      lemma_pread_le_initial cfg;
      WStep.lemma_client_reachable_initial cfg;
      assert (SMR.connection_state_evolves (CS.initial cfg) init);
      lemma_client_trace_pread_le init init st trace
    )
#pop-options

(** ═══ TARGET 2 : CLIENT read-side handshake-seq ≤ appdata count. ═══ **)
let lemma_client_reachable_readhs_seq_le_count (st:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        WFL.supported_client_config_wire_profile st.CS.cs_model.CS.model_config /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
          st.CS.cs_model.CS.model_record.CS.record_read.R.seq <=
            WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_received)
  = lemma_client_reachable_pread_le st

(** ─────────────────────────────────────────────────────────────────────────
    ESTABLISHMENT payoff (robust, closing/failure-agnostic).

    At a Quiet state whose server has sent ZERO ApplicationData-typed records,
    BOTH handshake-epoch projections are 0: the server's handshake-write seq is
    ≤ its sent appdata count (= 0) by the ungated inequality, and the client's
    handshake-read seq is ≤ its received appdata count, which equals the server's
    sent count (= 0) by the Quiet `byte_pairing` byte-equality.  Unlike
    `lemma_sc_quiet_align`, this needs NO `pre_appdata` hypothesis — the ungated
    inequalities absorb the closing/failure exits. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_sc_quiet_zero (a:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        MP.Quiet? a.channel /\
        WStep.raw_appdata_count a.server.CS.cs_wire_log.CL.raw_sent == 0)
      (ensures hs_wseq a.server == 0 /\ hs_rseq a.client == 0)
  = lemma_server_reachable_writehs_seq_le_count a.server;
    lemma_client_reachable_readhs_seq_le_count a.client;
    WStep.lemma_raw_appdata_count_seq_equal
      a.server.CS.cs_wire_log.CL.raw_sent
      a.client.CS.cs_wire_log.CL.raw_received
#pop-options


(** ═══════════════════════════════════════════════════════════════════════════
    MIRROR 1 : CLIENT write-side UNGATED reachable counting invariant.
    Exact mirror of the SERVER write-side chain, for the client state machine.
    Reuses the direction-generic helpers `pwrite_le`, `lemma_pwrite_le_initial`,
    `lemma_write_seq_step_bound`, `lemma_pwrite_le_algebra`; only the per-step,
    trace-driver and reachable-wrapper drivers are role-swapped to the client.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** Per-step preservation of `pwrite_le` for a reachable client (mirror of
    `lemma_server_step_pwrite_le`): extract the legal delta, the reachable
    outgoing byte-parse witness, and the record/key coupling, then apply the
    algebra. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_step_pwrite_le
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        pwrite_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.client_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pwrite_le st1)
  = let cfg = st0.CS.cs_model.CS.model_config in
    lemma_client_step_single_step st0 ev st1 out;
    SCB.lemma_consistent_record_key_epoch_coupling st0;
    WStep.lemma_client_reachable_raw_sent_parses cfg st0;
    let d = ID.indefinite_description_ghost
              CS.connection_delta
              (fun delta -> CS.legal_connection_delta st0 delta st1) in
    eliminate exists (msgs:list CW.wire_message).
      WF.parses_as CW.tls_record_wire_format
        st0.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
    returns pwrite_le st1
    with _.
      lemma_pwrite_le_algebra st0 d st1 msgs
#pop-options

(** Trace-induction driver: `pwrite_le` is preserved along any reachable client
    trace (mirror of `lemma_server_trace_pwrite_le`).  Config preservation is
    threaded via the client model-stepped fact, exactly as the client read-side
    trace driver does. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_trace_pwrite_le
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        pwrite_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.client_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pwrite_le st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      let cfg = st0.CS.cs_model.CS.model_config in
      lemma_client_step_pwrite_le st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_single_step st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_step_preserves_consistent st0 s';
      WStep.lemma_client_reachable_step
        (CS.initial cfg) st0 s' tr.SM.tr_event tr.SM.tr_output;
      WStep.lemma_client_step_model_stepped st0 tr.SM.tr_event s' tr.SM.tr_output;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event st0.CS.cs_model ce /\
        CS.step_model st0.CS.cs_model ce == Some s'.CS.cs_model
      returns s'.CS.cs_model.CS.model_config == cfg
      with _.
        WStep.lemma_step_model_preserves_config st0.CS.cs_model ce s'.CS.cs_model;
      lemma_client_trace_pwrite_le init s' st1 rest
#pop-options

(** ═══ CLIENT write-side UNGATED reachable counting invariant. ═══ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_reachable_pwrite_le (st:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures pwrite_le st)
  = let cfg = st.CS.cs_model.CS.model_config in
    let init : EC.client_initial_state = CS.initial cfg in
    let sm = WStep.client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace st
    returns pwrite_le st
    with _.
    (
      lemma_pwrite_le_initial cfg;
      WStep.lemma_client_reachable_initial cfg;
      assert (SMR.connection_state_evolves (CS.initial cfg) init);
      lemma_client_trace_pwrite_le init init st trace
    )
#pop-options

(** ═══ MIRROR TARGET 1 : CLIENT write-side handshake-seq ≤ appdata count. ═══ **)
let lemma_client_reachable_writehs_seq_le_count (st:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        WFL.supported_client_config_wire_profile st.CS.cs_model.CS.model_config /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        st.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
          st.CS.cs_model.CS.model_record.CS.record_write.R.seq <=
            WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_sent)
  = lemma_client_reachable_pwrite_le st

(** ═══════════════════════════════════════════════════════════════════════════
    MIRROR 2 : SERVER read-side UNGATED reachable counting invariant.
    Exact mirror of the CLIENT read-side chain, for the server state machine.
    Reuses the direction-generic helpers `pread_le`, `lemma_pread_le_initial`,
    `lemma_read_seq_step_bound`, `lemma_pread_le_algebra`; only the per-step,
    trace-driver and reachable-wrapper drivers are role-swapped to the server.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** Per-step preservation of `pread_le` for a reachable server (mirror of
    `lemma_client_step_pread_le`): extract the legal delta, the reachable
    incoming byte-parse witness, and the record/key coupling, then apply the
    algebra. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_step_pread_le
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        pread_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.server_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pread_le st1)
  = let cfg = st0.CS.cs_model.CS.model_config in
    lemma_server_step_single_step st0 ev st1 out;
    SCB.lemma_consistent_record_key_epoch_coupling st0;
    WStep.lemma_server_reachable_raw_received_parses cfg st0;
    let d = ID.indefinite_description_ghost
              CS.connection_delta
              (fun delta -> CS.legal_connection_delta st0 delta st1) in
    eliminate exists (msgs:list CW.wire_message).
      WF.parses_as CW.tls_record_wire_format
        st0.CS.cs_wire_log.CL.raw_received msgs Seq.empty
    returns pread_le st1
    with _.
      lemma_pread_le_algebra st0 d st1 msgs
#pop-options

(** Trace-induction driver: `pread_le` is preserved along any reachable server
    trace (mirror of `lemma_client_trace_pread_le`).  Config preservation is
    threaded via the server model-facts lemma, exactly as the server write-side
    trace driver does. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_server_trace_pread_le
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        pread_le st0 /\
        SMR.connection_state_consistent st0 /\
        WStep.server_reachable (CS.initial st0.CS.cs_model.CS.model_config) st0)
      (ensures pread_le st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (ES.server_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      let cfg = st0.CS.cs_model.CS.model_config in
      lemma_server_step_pread_le st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_server_step_single_step st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_step_preserves_consistent st0 s';
      WStep.lemma_server_reachable_step
        (CS.initial cfg) st0 s' tr.SM.tr_event tr.SM.tr_output;
      WStep.lemma_server_step_model_facts st0 tr.SM.tr_event s' tr.SM.tr_output;
      assert (s'.CS.cs_model.CS.model_config == cfg);
      lemma_server_trace_pread_le init s' st1 rest
#pop-options

(** ═══ SERVER read-side UNGATED reachable counting invariant. ═══ **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_pread_le (st:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures pread_le st)
  = let cfg = st.CS.cs_model.CS.model_config in
    let init : ES.server_initial_state = CS.initial cfg in
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace st
    returns pread_le st
    with _.
    (
      lemma_pread_le_initial cfg;
      WStep.lemma_server_reachable_initial cfg;
      assert (SMR.connection_state_evolves (CS.initial cfg) init);
      lemma_server_trace_pread_le init init st trace
    )
#pop-options

(** ═══ MIRROR TARGET 2 : SERVER read-side handshake-seq ≤ appdata count. ═══ **)
let lemma_server_reachable_readhs_seq_le_count (st:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial st.CS.cs_model.CS.model_config) st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
          st.CS.cs_model.CS.model_record.CS.record_read.R.seq <=
            WStep.raw_appdata_count st.CS.cs_wire_log.CL.raw_received)
  = lemma_server_reachable_pread_le st

(** ─────────────────────────────────────────────────────────────────────────
    cs-direction ESTABLISHMENT payoff (mirror of `lemma_sc_quiet_zero`).
    At a Quiet state whose CLIENT has sent ZERO ApplicationData-typed records,
    BOTH cs-direction handshake projections are 0: the client's handshake-write
    seq ≤ its sent appdata count (= 0), and the server's handshake-read seq ≤ its
    received appdata count = client's sent count (= 0) via Quiet byte_pairing
    `Seq.equal cs sr`.  Closing/failure-agnostic (ungated inequalities). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_cs_quiet_zero (a:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        MP.Quiet? a.channel /\
        WStep.raw_appdata_count a.client.CS.cs_wire_log.CL.raw_sent == 0)
      (ensures hs_wseq a.client == 0 /\ hs_rseq a.server == 0)
  = lemma_client_reachable_writehs_seq_le_count a.client;
    lemma_server_reachable_readhs_seq_le_count a.server;
    WStep.lemma_raw_appdata_count_seq_equal
      a.client.CS.cs_wire_log.CL.raw_sent
      a.server.CS.cs_wire_log.CL.raw_received
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ENDPOINT-LEVEL establishment helpers.  Unlike `lemma_{cs,sc}_quiet_zero`
    (which consume a whole `tls_system_state` under `tls_system_inv`), these take
    the two endpoints and the byte-log alignment directly, so a preservation
    family can apply them to a POST-state without reconstructing `tls_system_inv`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_cs_zero_from_counts (c s:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial c.CS.cs_model.CS.model_config) c /\
        WFL.supported_client_config_wire_profile c.CS.cs_model.CS.model_config /\
        c.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        WStep.server_reachable (CS.initial s.CS.cs_model.CS.model_config) s /\
        s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Seq.equal c.CS.cs_wire_log.CL.raw_sent s.CS.cs_wire_log.CL.raw_received /\
        WStep.raw_appdata_count c.CS.cs_wire_log.CL.raw_sent == 0)
      (ensures hs_wseq c == 0 /\ hs_rseq s == 0)
  = lemma_client_reachable_writehs_seq_le_count c;
    lemma_server_reachable_readhs_seq_le_count s;
    WStep.lemma_raw_appdata_count_seq_equal
      c.CS.cs_wire_log.CL.raw_sent
      s.CS.cs_wire_log.CL.raw_received
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_sc_zero_from_counts (c s:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial c.CS.cs_model.CS.model_config) c /\
        WFL.supported_client_config_wire_profile c.CS.cs_model.CS.model_config /\
        c.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        WStep.server_reachable (CS.initial s.CS.cs_model.CS.model_config) s /\
        s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Seq.equal s.CS.cs_wire_log.CL.raw_sent c.CS.cs_wire_log.CL.raw_received /\
        WStep.raw_appdata_count c.CS.cs_wire_log.CL.raw_received == 0)
      (ensures hs_wseq s == 0 /\ hs_rseq c == 0)
  = lemma_server_reachable_writehs_seq_le_count s;
    lemma_client_reachable_readhs_seq_le_count c;
    WStep.lemma_raw_appdata_count_seq_equal
      s.CS.cs_wire_log.CL.raw_sent
      c.CS.cs_wire_log.CL.raw_received
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    CLIENT local-step record effect.  A legal client `local_event` step either
    leaves `model_record` untouched, or is a key install at exactly one of the
    two client install stages: a HANDSHAKE install at `HsServerHelloReceived`
    (control preserved; both projections reset to seq 0), or an APPLICATION READ
    install at `HsServerFinishedVerified` (read epoch becomes `Application`, write
    slot untouched).  The client APPLICATION WRITE install is a no-op on the
    record, folded into the "unchanged" disjunct.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_client_local_record_effect
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ce /\
        CS.step_model m ce == Some m' /\
        CS.event_raw_delta_legal m ce B.empty B.empty /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        m'.CS.model_record == m.CS.model_record \/
        m'.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived \/
        (~(R.Handshake? m'.CS.model_record.CS.record_read.R.epoch) /\
         m'.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write))
  = match ce with
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated m dm m'
#pop-options

(** CLIENT local step with no wire output leaves both raw byte logs unchanged. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_local_wire_unchanged
  (st0 c':CS.connection_state) (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [])
      (ensures
        Seq.equal c'.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal c'.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received)
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
    returns
      (Seq.equal c'.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent /\
       Seq.equal c'.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received)
    with _.
    (
      WStep.lemma_serialize_all_nil_wire ();
      Seq.lemma_eq_elim raw_sent B.empty
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    LOCAL family — CLIENT.  Channel stays `Quiet`; only the client steps by a
    local event with no wire output.  Three cases (via the record-effect lemma):
    (i) record unchanged ⇒ direct transfer of `hs_seq_pairing a`;
    (ii) HANDSHAKE key install at `HsServerHelloReceived` ⇒ ESTABLISHMENT: the
         client has sent AND received zero ApplicationData records, so via the
         Quiet byte pairing all four handshake projections are 0 and both
         directions collapse to `0 == 0`;
    (iii) APPLICATION READ install ⇒ read epoch leaves `Handshake` (sc-direction
         gate off, vacuous) while the write slot is untouched (cs transfers).
    ═══════════════════════════════════════════════════════════════════════════ **)
(** Projection-zero from a per-epoch seq bound: if the handshake epoch implies a
    zero seq, the collapsing projection is 0.  Isolated so the (unfold-heavy)
    reasoning is done once, in a tiny VC. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_hwseq_zero_of_bound (st:CS.connection_state)
  : Lemma
      (requires (R.Handshake? (ASP.wr st).R.epoch ==> (ASP.wr st).R.seq == 0))
      (ensures hs_wseq st == 0)
  = ()

let lemma_hrseq_zero_of_bound (st:CS.connection_state)
  : Lemma
      (requires (R.Handshake? (ASP.rd st).R.epoch ==> (ASP.rd st).R.seq == 0))
      (ensures hs_rseq st == 0)
  = ()
#pop-options

(** TERMINAL-CONTROL ABSORPTION.  The terminal set
    (`ControlFailed`/`ControlClosing`/`ControlClosed`) is forward-closed under
    legal steps: `fail_model` and the alert/close arms only ever move WITHIN the
    terminal set, and no arm steps OUT of it.  Hence `not (terminal_control)` is
    BACKWARD-monotone across a step — the fact the re-keyed `cs/sc_hs_seq_ok` gates
    need to transfer a receiver's control gate across that endpoint's own
    record-unchanged local step.  STRUCTURAL: no reachability or record-epoch
    hypothesis (unlike a positive `ControlHandshaking?` monotonicity, which fails
    at the `ControlNew -> HsStarted` entry). **)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_step_terminal_control_absorbing
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires CS.legal_event m ce /\ CS.step_model m ce == Some m')
      (ensures
        terminal_control m.CS.model_control ==> terminal_control m'.CS.model_control)
  = ()
#pop-options

(** Establishment bundle: at a Quiet state where the CLIENT has sent AND received
    zero ApplicationData records, all four handshake projections (of both
    endpoints) are 0.  Proven in isolation so its VC localizes. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_hsp_quiet_both_zero (c s:CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial c.CS.cs_model.CS.model_config) c /\
        WFL.supported_client_config_wire_profile c.CS.cs_model.CS.model_config /\
        c.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        WStep.server_reachable (CS.initial s.CS.cs_model.CS.model_config) s /\
        s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        WStep.raw_appdata_count c.CS.cs_wire_log.CL.raw_sent == 0 /\
        WStep.raw_appdata_count c.CS.cs_wire_log.CL.raw_received == 0 /\
        Seq.equal c.CS.cs_wire_log.CL.raw_sent s.CS.cs_wire_log.CL.raw_received /\
        Seq.equal s.CS.cs_wire_log.CL.raw_sent c.CS.cs_wire_log.CL.raw_received)
      (ensures
        hs_wseq c == 0 /\ hs_rseq c == 0 /\ hs_wseq s == 0 /\ hs_rseq s == 0)
  = // transport the two zero counts to the server's byte logs
    WStep.lemma_raw_appdata_count_seq_equal
      c.CS.cs_wire_log.CL.raw_sent s.CS.cs_wire_log.CL.raw_received;
    WStep.lemma_raw_appdata_count_seq_equal
      s.CS.cs_wire_log.CL.raw_sent c.CS.cs_wire_log.CL.raw_received;
    // per-epoch seq bounds
    lemma_client_reachable_writehs_seq_le_count c;
    lemma_client_reachable_readhs_seq_le_count c;
    lemma_server_reachable_writehs_seq_le_count s;
    lemma_server_reachable_readhs_seq_le_count s;
    // collapse each projection to 0
    lemma_hwseq_zero_of_bound c;
    lemma_hrseq_zero_of_bound c;
    lemma_hwseq_zero_of_bound s;
    lemma_hrseq_zero_of_bound s
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hsp_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ hs_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_local a b)
      (ensures hs_seq_pairing b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns hs_seq_pairing b
    with _.
    (
      let cfg = a.client.CS.cs_model.CS.model_config in
      WStep.lemma_client_reachable_step
        (CS.initial cfg) a.client c' (SM.LocalEvent local) out;
      lemma_client_local_wire_unchanged a.client c' local out;
      ASP.lemma_client_local_extract a.client c' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.client.CS.cs_model ce /\
        CS.step_model a.client.CS.cs_model ce == Some c'.CS.cs_model /\
        CS.event_raw_delta_legal a.client.CS.cs_model ce B.empty B.empty
      returns hs_seq_pairing b
      with _pe.
      (
      lemma_client_local_record_effect a.client.CS.cs_model c'.CS.cs_model ce;
      lemma_step_terminal_control_absorbing a.client.CS.cs_model c'.CS.cs_model ce;
      WStep.lemma_step_model_preserves_config a.client.CS.cs_model ce c'.CS.cs_model;
      if c'.CS.cs_model.CS.model_record = a.client.CS.cs_model.CS.model_record then
        ()
      else if c'.CS.cs_model.CS.model_control
              = CS.ControlHandshaking CS.HsServerHelloReceived then begin
        // client-side counts are zero at HsServerHelloReceived
        WStep.lemma_client_preappdata_sent_no_appdata cfg c';
        WStep.lemma_client_hsserverhelloreceived_recv_zero cfg c';
        // Quiet byte pairing (from tls_system_inv a) + wire-log unchanged (from
        // the local step) — chain to the c'/server alignments the bundle wants.
        assert (Seq.equal c'.CS.cs_wire_log.CL.raw_sent
                          a.server.CS.cs_wire_log.CL.raw_received);
        assert (Seq.equal a.server.CS.cs_wire_log.CL.raw_sent
                          c'.CS.cs_wire_log.CL.raw_received);
        lemma_hsp_quiet_both_zero c' a.server
      end else
        ()
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    SERVER local-step record effect.  A legal server `local_event` step either
    leaves `model_record` untouched, or is a key install: HANDSHAKE install at
    `HsServerHelloSent` (control preserved; both projections reset to seq 0),
    APPLICATION WRITE install at `HsServerFinishedSent` (write epoch leaves
    `Handshake`; read slot untouched), or APPLICATION READ install at
    `HsClientFinishedReceived` (read epoch leaves `Handshake`; write untouched).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_server_local_record_effect
  (m m':CS.connection_model) (ce:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ce /\
        CS.step_model m ce == Some m' /\
        CS.event_raw_delta_legal m ce B.empty B.empty /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        m'.CS.model_record == m.CS.model_record \/
        m'.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
        (~(R.Handshake? m'.CS.model_record.CS.record_write.R.epoch) /\
         m'.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read) \/
        (~(R.Handshake? m'.CS.model_record.CS.record_read.R.epoch) /\
         m'.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write))
  = match ce with
    | CS.ConnLocalEvent lev -> ()
    | CS.ConnNetworkEvent dm ->
      ASP.lemma_network_empty_delta_record_unchanged_ungated m dm m'
#pop-options

(** SERVER local step with no wire output leaves both raw byte logs unchanged. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_local_wire_unchanged
  (st0 s':CS.connection_state) (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [])
      (ensures
        Seq.equal s'.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal s'.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received)
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
    returns
      (Seq.equal s'.CS.cs_wire_log.CL.raw_sent st0.CS.cs_wire_log.CL.raw_sent /\
       Seq.equal s'.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received)
    with _.
    (
      WStep.lemma_serialize_all_nil_wire ();
      Seq.lemma_eq_elim raw_sent B.empty
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    LOCAL family — SERVER (mirror of the client local family).  Cases: record
    unchanged ⇒ transfer; HANDSHAKE install at `HsServerHelloSent` ⇒ ESTABLISHMENT
    (server sent AND received zero ApplicationData records ⇒ all four projections
    0 via the Quiet byte pairing); APPLICATION write/read install ⇒ one direction's
    gate turns off (vacuous) while the other slot is untouched (transfers).
    ═══════════════════════════════════════════════════════════════════════════ **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_hsp_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ hs_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_local a b)
      (ensures hs_seq_pairing b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns hs_seq_pairing b
    with _.
    (
      let cfg = a.server.CS.cs_model.CS.model_config in
      WStep.lemma_server_reachable_step
        (CS.initial cfg) a.server s' (SM.LocalEvent local) out;
      lemma_server_local_wire_unchanged a.server s' local out;
      ASP.lemma_server_local_extract a.server s' local out;
      eliminate exists (ce:CS.conn_event).
        CS.legal_event a.server.CS.cs_model ce /\
        CS.step_model a.server.CS.cs_model ce == Some s'.CS.cs_model /\
        CS.event_raw_delta_legal a.server.CS.cs_model ce B.empty B.empty
      returns hs_seq_pairing b
      with _pe.
      (
      lemma_server_local_record_effect a.server.CS.cs_model s'.CS.cs_model ce;
      lemma_step_terminal_control_absorbing a.server.CS.cs_model s'.CS.cs_model ce;
      WStep.lemma_step_model_preserves_config a.server.CS.cs_model ce s'.CS.cs_model;
      if s'.CS.cs_model.CS.model_record = a.server.CS.cs_model.CS.model_record then
        ()
      else if s'.CS.cs_model.CS.model_control
              = CS.ControlHandshaking CS.HsServerHelloSent then begin
        // server-side counts are zero at HsServerHelloSent
        WStep.lemma_server_hsserverhellosent_sent_zero cfg s';
        WStep.lemma_server_hsserverhellosent_recv_zero cfg s';
        // Quiet byte pairing (b) + server wire-log unchanged → client alignments
        assert (Seq.equal a.client.CS.cs_wire_log.CL.raw_sent
                          s'.CS.cs_wire_log.CL.raw_received);
        assert (Seq.equal s'.CS.cs_wire_log.CL.raw_sent
                          a.client.CS.cs_wire_log.CL.raw_received);
        // transport server's zero counts to the (unchanged) client logs
        WStep.lemma_raw_appdata_count_seq_equal
          a.client.CS.cs_wire_log.CL.raw_sent s'.CS.cs_wire_log.CL.raw_received;
        WStep.lemma_raw_appdata_count_seq_equal
          s'.CS.cs_wire_log.CL.raw_sent a.client.CS.cs_wire_log.CL.raw_received;
        lemma_hsp_quiet_both_zero a.client s'
      end else
        ()
      )
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    FULL slot-preservation bridges.  A `Sent` model step never touches
    `record_read`; a `Received` model step never touches `record_write`.  These
    give the FULL direction-state equality (epoch AND seq), which the send/deliver
    families need to transfer the receiver-read (resp. sender-write) EPOCH gate
    across the acting endpoint's step — the projection-only lemmas
    (`lemma_sent_preserves_hread`) do not carry the epoch.
    ═══════════════════════════════════════════════════════════════════════════ **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_sent_preserves_rd_full (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m CL.Sent msg == Some m')
      (ensures
        m'.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read)
  = PWRA.lemma_step_sent_network_event_preserves_record_read m msg m'

let lemma_recv_preserves_wr_full (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m CL.Received msg == Some m')
      (ensures
        m'.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write)
  = PWRA.lemma_step_received_network_event_preserves_record_write m msg m'
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    SEND family — SERVER.  A `server_send` enters `MP.ToClient p` from `Quiet`,
    with `p.pl_snap == a.server.cs_model` (the PRE-send server snapshot).  The
    in-flight `sc` arm reads the SNAPSHOT write seq — which is the PRE-send server
    write — so the pre-state Quiet `sc` clause (both-epoch gated) supplies it
    DIRECTLY under the post-state gate (whose `Handshake?(rd b.client)` conjunct is
    exactly the receiver-read gate of the pre-state Quiet clause; the client is
    untouched).  The `cs` arm (server is the READER) freezes via
    `lemma_sent_preserves_rd_full` (a `Sent` step leaves `record_read` whole, so its
    epoch and seq transfer), and the pre-state Quiet `cs` clause carries it.
    ═══════════════════════════════════════════════════════════════════════════ **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_hsp_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ hs_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b)
      (ensures hs_seq_pairing b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns hs_seq_pairing b
    with _pf.
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      // `Sent` step freezes the server's `record_read` whole (epoch + seq), so the
      // `cs` (server-reader) gate transfers from the pre-state Quiet clause.
      lemma_sent_preserves_rd_full a.server.CS.cs_model s'.CS.cs_model sent
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    SEND family — CLIENT (mirror).  Enters `MP.ToServer p` from `Quiet`; the
    in-flight `cs` arm reads the pre-send client write snapshot (pre-state Quiet
    `cs` clause supplies it under the post gate), and the `sc` arm (client is the
    READER) freezes via `lemma_sent_preserves_rd_full`.
    ═══════════════════════════════════════════════════════════════════════════ **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_hsp_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ hs_seq_pairing a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b)
      (ensures hs_seq_pairing b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns hs_seq_pairing b
    with _pf.
    (
      ASP.lemma_client_send_pins_model a.client c' local out sent;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Sent sent == Some c'.CS.cs_model);
      lemma_sent_preserves_rd_full a.client.CS.cs_model c'.CS.cs_model sent
    )
#pop-options

(* ══════════════════════════════════════════════════════════════════════
   hs_channel_seal_ok — helper machinery (migrated, proven in scratch)
   ══════════════════════════════════════════════════════════════════════ *)

(* ---- STEP 2: per-constructor serialize->parse roundtrip + send seal ---- *)
#set-options "--fuel 2 --ifuel 2 --z3rlimit 40"

let roundtrip (sent:M.tls_message) : prop =
  let (ct, frag) = W.serialize_tls_message sent in
  W.parse_tls_message ct frag == Some sent

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_list_bytesize_bound (cl:list GCertE.certificateEntry)
  : Lemma (ensures GCL.certificate_certificate_list_list_bytesize cl
                   <= 65540 * L.length (Sem.cert_entries_data cl)
                      + W.cert_chain_total_bytes (Sem.cert_entries_data cl))
          (decreases cl)
  = match cl with
    | [] -> GCL.certificate_certificate_list_list_bytesize_nil
    | e :: tl ->
      lemma_list_bytesize_bound tl;
      GCL.certificate_certificate_list_list_bytesize_cons e tl;
      assert (Sem.cert_entries_data (e :: tl)
              == (e.GCertE.cert_data <: Seq.seq FStar.UInt8.t) :: Sem.cert_entries_data tl);
      W.lemma_cert_chain_total_bytes_cons (e.GCertE.cert_data) (Sem.cert_entries_data tl);
      assert (GCertE.certificateEntry_extensions_list_bytesize (e.GCertE.extensions) <= 65535)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_cert_bytesize_of_representable (cert:GCert.certificate)
  : Lemma (requires W.certificate_representable cert)
          (ensures GCert.certificate_bytesize cert <= 16777215)
  = W.lemma_certificate_representable cert;
    let cl = (cert.GCert.certificate_list <: list GCertE.certificateEntry) in
    lemma_list_bytesize_bound cl;
    FStar.Math.Lemmas.lemma_mult_le_left 65540 (L.length (Sem.cert_entries_data cl)) 8
#pop-options

let lemma_rt_hs_generic (hs:M.handshake_msg) (v:GHS.handshake)
  : Lemma
    (requires
      Seq.equal (W.serialize_handshake hs) (LP.serialize GHS.handshake_serializer v) /\
      RVDH.handshake_synth v == Some hs)
    (ensures roundtrip (M.TlsHandshake hs))
  = let fragment = W.serialize_handshake hs in
    W.lemma_serialize_tls_message_handshake hs;
    LP.parse_serialize GHS.handshake_serializer v;
    Seq.lemma_eq_elim fragment (LP.serialize GHS.handshake_serializer v);
    RVDH.lemma_ptm_handshake_some fragment v hs

let lemma_rt_finished (fin:GFin.finished)
  : Lemma (roundtrip (M.TlsHandshake (M.Finished fin)))
  = RVDH.lemma_serialize_handshake_finished fin;
    RVDH.lemma_handshake_synth_finished fin;
    lemma_rt_hs_generic (M.Finished fin) (GHS.Body_finished fin)

let lemma_rt_ee (ee:GEE.encryptedExtensions)
  : Lemma (requires W.encryptedExtensions_representable ee)
          (ensures roundtrip (M.TlsHandshake (M.EncryptedExtensions ee)))
  = RVDH.lemma_serialize_handshake_encrypted_extensions ee;
    RVDH.lemma_handshake_synth_encrypted_extensions ee;
    lemma_rt_hs_generic (M.EncryptedExtensions ee) (GHS.Body_encrypted_extensions ee)

let lemma_rt_cv (cv:GCV.certificateVerify)
  : Lemma (requires W.certificateVerify_representable cv)
          (ensures roundtrip (M.TlsHandshake (M.CertificateVerify cv)))
  = RVDH.lemma_serialize_handshake_certificate_verify cv;
    RVDH.lemma_handshake_synth_certificate_verify cv;
    lemma_rt_hs_generic (M.CertificateVerify cv) (GHS.Body_certificate_verify cv)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_rt_cert (cert:GCert.certificate)
  : Lemma (requires W.certificate_representable cert)
          (ensures roundtrip (M.TlsHandshake (M.Certificate cert)))
  = lemma_cert_bytesize_of_representable cert;
    let b : GHS.handshake_body_certificate = cert in
    RVDH.lemma_serialize_handshake_certificate cert;
    RVDH.lemma_handshake_synth_certificate b;
    lemma_rt_hs_generic (M.Certificate cert) (GHS.Body_certificate b)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_rt_close_notify (_:unit)
  : Lemma (ensures roundtrip (M.TlsAlert T.Close_notify))
  = let a : GA.alert = { GA.level = GAL.Fatal; GA.description = T.Close_notify } in
    let frag = LP.serialize GA.alert_serializer a in
    W.lemma_serialize_tls_message_close_notify ();
    assert (W.serialize_tls_message (M.TlsAlert T.Close_notify) == (T.Alert, frag));
    LP.parse_serialize GA.alert_serializer a;
    RVA.lemma_ptm_alert frag
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_rt_appdata (data:B.bytes)
  : Lemma (ensures roundtrip (M.TlsApplicationData data))
  = W.lemma_serialize_tls_message_application_data data;
    RVR.lemma_ptm_application_data data
#pop-options

module SMCan = TLS13.Spec.StateMachine.Canonical
module SMKM  = TLS13.Spec.StateMachine.KeyMaterial
module RF    = TLS13.Spec.StateMachine.RecordFraming

(* STEP 2b: roundtrip dispatcher for endpoint-emittable, gate-surviving sends. *)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_send_roundtrip (model:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        CS.legal_tls_message model CL.Sent sent /\
        CS.network_message_is_cleartext CL.Sent sent == false /\
        (M.TlsAlert? sent ==> M.TlsAlert?._0 sent == T.Close_notify) /\
        ~(M.TlsKeyUpdate? sent))
      (ensures roundtrip sent)
  = match sent with
    | M.TlsHandshake hs ->
      (match hs with
       | M.Finished fin -> lemma_rt_finished fin
       | M.EncryptedExtensions ee ->
         W.lemma_encryptedExtensions_representable ee;
         lemma_rt_ee ee
       | M.Certificate c -> lemma_rt_cert c
       | M.CertificateVerify cv -> lemma_rt_cv cv
       | _ -> ())    (* ClientHello/ServerHello cleartext; HRR illegal Sent *)
    | M.TlsApplicationData d -> lemma_rt_appdata d
    | M.TlsAlert a -> lemma_rt_close_notify ()
    | _ -> ()        (* CCS cleartext; KeyUpdate excluded; Ignored illegal Sent *)
#pop-options

(* STEP 2a: seal extraction from the send-time nonempty seal projection. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_send_seal (model:CS.connection_model) (sent:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        SMCan.sent_event_nonempty_seal_projection model (SMKM.sent_tls_event sent) raw /\
        CS.network_message_is_cleartext CL.Sent sent == false /\
        CS.protected_record_count CL.Sent sent == 1 /\
        B.length raw > 0)
      (ensures SMCan.sent_single_protected_message_seal model sent raw)
  = match sent with
    | M.TlsApplicationData bytes ->
      if B.length bytes > RF.max_application_data_fragment_len then
        RF.lemma_application_data_record_count_len_step (B.length bytes)
      else ()
    | _ -> ()
#pop-options

(* ---- STEP 3: reachable write-epoch shapes (cleartext exclusion) ---- *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* Client: at pre-handshake-write-key controls, write epoch is Initial. *)
let cinit_shape (model:CS.connection_model) : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
  (match model.CS.model_control with
   | CS.ControlNew
   | CS.ControlHandshaking CS.HsNotStarted
   | CS.ControlHandshaking CS.HsStarted ->
     model.CS.model_record.CS.record_write.R.epoch == R.Initial
   | _ -> True)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_cinit_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires cinit_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures cinit_shape model')
  = ()
#pop-options

(* Server: at pre-handshake-write-key controls, write epoch is Initial. *)
let sinit_shape (model:CS.connection_model) : prop =
  model.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
  (match model.CS.model_control with
   | CS.ControlNew
   | CS.ControlHandshaking CS.HsNotStarted
   | CS.ControlHandshaking CS.HsAwaitingClientHello
   | CS.ControlHandshaking CS.HsClientHelloReceived ->
     model.CS.model_record.CS.record_write.R.epoch == R.Initial
   | _ -> True)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_sinit_shape (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires sinit_shape model /\ CS.legal_event model ev /\ CS.step_model model ev == Some model')
      (ensures sinit_shape model')
  = ()
#pop-options

let conn_cinit_shape (st:CS.connection_state) : prop = cinit_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_cinit_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_cinit_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_cinit_shape st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_cinit_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_cinit_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_cinit_shape y); (SMR.connection_state_single_step x y)}
          conn_cinit_shape x /\ SMR.connection_state_single_step x y ==> conn_cinit_shape y)
  = introduce forall x y.
      conn_cinit_shape x /\ SMR.connection_state_single_step x y ==> conn_cinit_shape y
    with introduce _ ==> _ with _.
      lemma_delta_cinit_shape x y

let lemma_initial_cinit_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_cinit_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_cinit_shape (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_cinit_shape st)
  = lemma_initial_cinit_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_cinit_shape ();
    let p = conn_cinit_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

let conn_sinit_shape (st:CS.connection_state) : prop = sinit_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_sinit_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_sinit_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_sinit_shape st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_sinit_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_sinit_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_sinit_shape y); (SMR.connection_state_single_step x y)}
          conn_sinit_shape x /\ SMR.connection_state_single_step x y ==> conn_sinit_shape y)
  = introduce forall x y.
      conn_sinit_shape x /\ SMR.connection_state_single_step x y ==> conn_sinit_shape y
    with introduce _ ==> _ with _.
      lemma_delta_sinit_shape x y

let lemma_initial_sinit_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_sinit_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_sinit_shape (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_sinit_shape st)
  = lemma_initial_sinit_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_sinit_shape ();
    let p = conn_sinit_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(* ---- endpoint message-class lemmas (no CCS; alert => close_notify) ---- *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_send_msg_class
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
      (ensures
        ~(M.TlsChangeCipherSpec? sent) /\
        (M.TlsAlert? sent ==> M.TlsAlert?._0 sent == T.Close_notify))
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      EC.client_representation_matches st0 local conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 c' conn_ev raw_sent B.empty
    returns
      ~(M.TlsChangeCipherSpec? sent) /\
      (M.TlsAlert? sent ==> M.TlsAlert?._0 sent == T.Close_notify)
    with _pf.
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      EC.client_representation_exact st0 local conn_ev
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_send_msg_class
  (st0 s':CS.connection_state)
  (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        ES.server_step #CTy.server_local_event st0 (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        s'.CS.cs_event_log == st0.CS.cs_event_log @ [SMKM.sent_tls_event sent])
      (ensures
        ~(M.TlsChangeCipherSpec? sent) /\
        (M.TlsAlert? sent ==> M.TlsAlert?._0 sent == T.Close_notify))
  = eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ES.server_representation_matches local conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty
    returns
      ~(M.TlsChangeCipherSpec? sent) /\
      (M.TlsAlert? sent ==> M.TlsAlert?._0 sent == T.Close_notify)
    with _pf.
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      ES.server_representation_exact local conn_ev
    )
#pop-options

(* ---- raw>0 for a single protected record ---- *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_rre_nonempty (raw:B.bytes)
  : Lemma (requires CS.raw_records_exactly raw T.Application_data 1)
          (ensures B.length raw > 0)
  = CSL.lemma_raw_records_exactly_one_parse_record raw T.Application_data

(* ---- gate exclusions: under a Handshake write epoch, a legal non-CCS Sent
        message is protected (not cleartext) and is not a KeyUpdate. ---- *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_client_gate_excludes (st0:CS.connection_state) (sent:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_tls_message st0.CS.cs_model CL.Sent sent /\
        ~(M.TlsChangeCipherSpec? sent) /\
        R.Handshake? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures
        CS.network_message_is_cleartext CL.Sent sent == false /\
        ~(M.TlsKeyUpdate? sent))
  = lemma_consistent_cinit_shape st0;
    (match sent with
     | M.TlsApplicationData _ | M.TlsKeyUpdate _ ->
         CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint st0;
         CSL.lemma_connection_application_ready_record_epochs_installed CS.ClientEndpoint st0
     | _ -> ())
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_server_gate_excludes (st0:CS.connection_state) (sent:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_tls_message st0.CS.cs_model CL.Sent sent /\
        ~(M.TlsChangeCipherSpec? sent) /\
        R.Handshake? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures
        CS.network_message_is_cleartext CL.Sent sent == false /\
        ~(M.TlsKeyUpdate? sent))
  = lemma_consistent_sinit_shape st0;
    (match sent with
     | M.TlsApplicationData _ | M.TlsKeyUpdate _ ->
         CSL.lemma_connection_appdata_keys_installed_for_role CS.ServerEndpoint st0;
         CSL.lemma_connection_application_ready_record_epochs_installed CS.ServerEndpoint st0
     | _ -> ())
#pop-options

(* ---- send-time seal + roundtrip extraction (client) ---- *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_client_send_seal_rt
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
        R.Handshake? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures
        SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
        roundtrip sent)
  = ASP.lemma_client_send_count st0 c' local out w sent;
    lemma_client_send_msg_class st0 c' local out w sent;
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      EC.client_representation_matches st0 local conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 c' conn_ev raw_sent B.empty
    returns
      SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
      roundtrip sent
    with _pf.
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      SY.lemma_serialize_all_single w;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
      assert (CS.legal_tls_message st0.CS.cs_model CL.Sent sent);
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      lemma_client_gate_excludes st0 sent;
      assert (CS.raw_records_exactly raw_sent T.Application_data 1);
      lemma_rre_nonempty raw_sent;
      lemma_send_seal st0.CS.cs_model sent raw_sent;
      lemma_send_roundtrip st0.CS.cs_model sent
    )
#pop-options

(* ---- send-time seal + roundtrip extraction (server) ---- *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_server_send_seal_rt
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
        R.Handshake? st0.CS.cs_model.CS.model_record.CS.record_write.R.epoch)
      (ensures
        SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
        roundtrip sent)
  = ASP.lemma_server_send_count st0 s' local out w sent;
    lemma_server_send_msg_class st0 s' local out w sent;
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ES.server_representation_matches local conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty
    returns
      SMCan.sent_single_protected_message_seal st0.CS.cs_model sent (SY.emitted_raw out) /\
      roundtrip sent
    with _pf.
    (
      L.append_inv_head st0.CS.cs_event_log [conn_ev] [SMKM.sent_tls_event sent];
      assert (conn_ev == SMKM.sent_tls_event sent);
      SY.lemma_serialize_all_single w;
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
      assert (CS.legal_tls_message st0.CS.cs_model CL.Sent sent);
      assert (CS.network_message_raw_delta_legal st0.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      lemma_server_gate_excludes st0 sent;
      assert (CS.raw_records_exactly raw_sent T.Application_data 1);
      lemma_rre_nonempty raw_sent;
      lemma_send_seal st0.CS.cs_model sent raw_sent;
      lemma_send_roundtrip st0.CS.cs_model sent
    )
#pop-options

(** MACHINE-CHECK (condition a): under the option-0 composite gate, a RECEIVE that
    is NOT cleartext advances the Handshake read seq by EXACTLY 1.  CCS (the +0 trap
    that survives the control/epoch gate) is killed by the ~cleartext hypothesis;
    SH/HRR need PRE Initial read (excluded by PRE Handshake gate); Finished/alerts
    leave ControlHandshaking (excluded by POST control gate); appdata/keyupdate need
    App read (excluded by PRE Handshake gate).  Only EE/Cert/CV survive: each +1.
    NO seal, NO key/iv material, NO faithful decode. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_hs_recv_plus_one
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Received msg == Some m' /\
        CS.network_message_is_cleartext CL.Received msg == false /\
        R.Handshake? (ASP.m_rd m).R.epoch /\
        CS.ControlHandshaking? m'.CS.model_control /\
        R.Handshake? (ASP.m_rd m').R.epoch)
      (ensures (ASP.m_rd m').R.seq == (ASP.m_rd m).R.seq + 1)
  = ()
#pop-options

(** GATED +1 receive helper.  Strengthens `lemma_hs_recv_plus_one` by DERIVING its
    two structural preconditions — PRE Handshake read and POST `ControlHandshaking?`
    — from the delivery-time facts POST Handshake read + `~terminal(st')` + `~cleartext`,
    plus PRE consistency.  Under those the surviving receive arms are EE/Cert/CV: each
    does `record_read = next_seq` (epoch-preserving, so PRE Handshake read follows from
    POST), stays `ControlHandshaking`, and advances the read seq by exactly 1.  Finished
    installs the Application read epoch (excluded by POST Handshake read);
    appdata/ignored-post-handshake at `ControlApplicationData` are Application-read at a
    CONSISTENT state (excluded via `lemma_connection_appdata_keys_installed_for_role` +
    `lemma_connection_application_ready_record_epochs_installed`); keyupdate installs
    Application read (excluded structurally); alerts land in `ControlFailed`/`ControlClosed`
    (excluded by `~terminal`); CCS/hellos are cleartext (excluded).

    PRE-consistency is LOAD-BEARING and cannot be dropped: for an inconsistent model at
    `ControlApplicationData` with a `Handshake` read epoch, an application-data receive
    keeps `ControlApplicationData` yet POST Handshake read, contradicting the
    `ControlHandshaking?` conclusion — so the model-level (no-consistency) version is
    genuinely false at an unreachable state, and consistency (available at every
    delivery, `a.server`/`a.client` are reachable) is the right guard. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 40 --split_queries always"
let lemma_hs_recv_plus_one_gated
  (st st':CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        CS.step_tls_message st.CS.cs_model CL.Received msg == Some st'.CS.cs_model /\
        CS.network_message_is_cleartext CL.Received msg == false /\
        R.Handshake? (ASP.rd st').R.epoch /\
        not (terminal_control st'.CS.cs_model.CS.model_control))
      (ensures
        R.Handshake? (ASP.rd st).R.epoch /\
        CS.ControlHandshaking? st'.CS.cs_model.CS.model_control /\
        (ASP.rd st').R.seq == (ASP.rd st).R.seq + 1)
  = match msg, st.CS.cs_model.CS.model_control with
    | M.TlsHandshake (M.EncryptedExtensions _), CS.ControlHandshaking CS.HsServerHelloReceived ->
        ()
    | M.TlsHandshake (M.Certificate _), CS.ControlHandshaking CS.HsEncryptedExtensionsReceived ->
        ()
    | M.TlsHandshake (M.CertificateVerify _), CS.ControlHandshaking CS.HsCertificateValidated ->
        ()
    | _, CS.ControlApplicationData ->
        // appdata / ignored-post-handshake receives keep `ControlApplicationData`
        // and preserve the read epoch; at a CONSISTENT state that epoch is
        // `Application`, contradicting POST Handshake read.  Every other message at
        // this control steps to `None` (contradiction) or a terminal control
        // (excluded by `~terminal`).
        let role = st.CS.cs_model.CS.model_config.CS.config_role in
        CSL.lemma_connection_appdata_keys_installed_for_role role st;
        CSL.lemma_connection_application_ready_record_epochs_installed role st
    | _ -> ()
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    DELIVERY preservation — the two standalone `deliver` lemmas.

    A `deliver_to_server`/`deliver_to_client` consumes an in-flight payload
    (`MP.ToServer p`/`MP.ToClient p`) and steps the RECEIVING endpoint by the
    message it decodes, landing the channel back at `MP.Quiet`.  Both post-state
    `hs_seq_pairing` conjuncts are the Quiet `_` arms.  Structure (mirror of
    `ASP.lemma_asp_deliver_to_{server,client}`, dual gate on `snap_wr`):

      * EASY arm (the frozen-writer direction): a `Received` step freezes the
        acting endpoint's WRITE slot (`lemma_recv_preserves_wr_full`) and the peer
        is untouched, so the pre-state Quiet-analog clause transfers 1:1.
      * SUBSTANTIVE arm (the receiver-read direction): the `+1` receive
        (`lemma_hs_recv_plus_one_gated`) chained with the pre-state IN-FLIGHT arm
        (`snap_hs_wseq p == hs_rseq <receiver>`) and the SEND `+1` delta carried by
        `ASP.inflight_sender_stepped`.
    ═══════════════════════════════════════════════════════════════════════════ **)

(** ─────────────────────────────────────────────────────────────────────────
    SERVER-SIDE HsClientFinishedVerified EXCLUSION.

    The server control `HsClientFinishedVerified` is produced by NO transition arm
    of the state machine (the client Finished is processed ATOMICALLY at
    `StateMachine.fst:774`, `HsServerFinishedSent -> ControlApplicationData`, and
    `LocalVerifyClientFinished` at `HsClientFinishedReceived` also steps directly to
    `ControlApplicationData` at `StateMachine.fst:564`).  So a legal step never
    yields it, and it is single-step-stable; hence a consistent connection is never
    at `HsClientFinishedVerified`.  Mirrors `SNC.lemma_consistent_not_cfr`.
    ───────────────────────────────────────────────────────────────────────── **)
let ctrl_not_hscfv_m (m:CS.connection_model) : prop =
  m.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedVerified

let ctrl_not_hscfv (st:CS.connection_state) : prop =
  ctrl_not_hscfv_m st.CS.cs_model

#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_step_handshake_not_hscfv
  (m:CS.connection_model) (dir:CS.direction) (hm:M.handshake_msg) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_hscfv_m m /\ CS.step_handshake_message m dir hm == Some m')
      (ensures ctrl_not_hscfv_m m')
  = ()
#pop-options

(** Factored: the handshake case delegates to `lemma_step_handshake_not_hscfv`; every
    other `step_tls_message` arm sets the control to `ControlApplicationData` /
    `ControlClosing` / `ControlClosed` / `ControlFailed` or leaves the model
    unchanged (CCS), none of which is `HsClientFinishedVerified`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_tls_not_hscfv
  (m:CS.connection_model) (dir:CS.direction) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_hscfv_m m /\ CS.step_tls_message m dir msg == Some m')
      (ensures ctrl_not_hscfv_m m')
  = match msg with
    | M.TlsHandshake hm -> lemma_step_handshake_not_hscfv m dir hm m'
    | _ -> ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_step_local_not_hscfv
  (m:CS.connection_model) (lev:CS.local_event) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_hscfv_m m /\ CS.step_local_event m lev == Some m')
      (ensures ctrl_not_hscfv_m m')
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_step_model_ctrl_not_hscfv
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires ctrl_not_hscfv_m m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures ctrl_not_hscfv_m m')
  = match ev with
    | CS.ConnNetworkEvent dm ->
      lemma_step_tls_not_hscfv m dm.CL.message_direction dm.CL.message_value m'
    | CS.ConnLocalEvent lev ->
      lemma_step_local_not_hscfv m lev m'
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_ctrl_not_hscfv (st0 st1:CS.connection_state)
  : Lemma
      (requires ctrl_not_hscfv st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures ctrl_not_hscfv st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_model_ctrl_not_hscfv
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_ctrl_not_hscfv (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (ctrl_not_hscfv y); (SMR.connection_state_single_step x y)}
          ctrl_not_hscfv x /\ SMR.connection_state_single_step x y ==>
          ctrl_not_hscfv y)
  = introduce forall x y.
      ctrl_not_hscfv x /\ SMR.connection_state_single_step x y ==> ctrl_not_hscfv y
    with introduce _ ==> _ with _.
      lemma_delta_ctrl_not_hscfv x y

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_not_hscfv (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures
        st.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsClientFinishedVerified)
  = lemma_single_step_ctrl_not_hscfv ();
    let p = ctrl_not_hscfv in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config))
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    SERVER RECEIVED count == 0 at a Handshake READ epoch.

    A reachable, consistent server whose record READ epoch is `Handshake` and which
    is not in a terminal control has RECEIVED zero ApplicationData-typed records.
    The server's only protected receive is the client Finished, which lands it in
    the post-CF region (`WStep.server_recv_prior == 1`) at `ControlApplicationData`
    (App read).  Under a Handshake read epoch the control is therefore NOT post-CF:
    CAD is excluded because a consistent CAD server has App read (contradiction);
    `HsClientFinishedReceived`/`HsClientFinishedVerified` are excluded because a
    consistent connection is never there; terminals are excluded by hypothesis.  So
    `server_recv_prior == 0`, and the trace-potential telescoping upper-bounds the
    received count by 0.  Mirrors `WStep.lemma_server_finished_sent_recv_eq0`.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_server_hs_read_recv_count_zero
  (cfg:CS.connection_config) (server:CS.connection_state)
  : Lemma
      (requires
        WStep.server_reachable (CS.initial cfg) server /\
        cfg.CS.config_role == CS.ServerEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        SMR.connection_state_consistent server /\
        R.Handshake? (ASP.rd server).R.epoch /\
        not (terminal_control server.CS.cs_model.CS.model_control))
      (ensures
        WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_received == 0)
  = let init : ES.server_initial_state = CS.initial cfg in
    // Exclude the post-CF controls so `server_recv_prior server == 0` and
    // `pre_appdata_ctrl server`.
    //   CAD: a consistent server at CAD has its record_read epoch on Application,
    //   contradicting the Handshake read hypothesis.
    introduce CS.ControlApplicationData? server.CS.cs_model.CS.model_control ==> False
    with _cad.
    (
      CSL.lemma_connection_appdata_keys_installed_for_role CS.ServerEndpoint server;
      CSL.lemma_connection_application_ready_record_epochs_installed CS.ServerEndpoint server
    );
    //   HsClientFinishedReceived / HsClientFinishedVerified: excluded for any
    //   consistent connection.
    SNC.lemma_consistent_not_cfr server;
    lemma_consistent_not_hscfv server;
    assert (WStep.server_recv_prior server.CS.cs_model == 0);
    let sm = WStep.server_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace server
    returns WStep.raw_appdata_count server.CS.cs_wire_log.CL.raw_received == 0
    with _.
    (
      WStep.lemma_server_trace_recv_potential init init server trace;
      PNTWL.lemma_server_trace_wire_logs_match init init trace server;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal server.CS.cs_wire_log.CL.raw_received sm_bytes);
      WStep.lemma_raw_appdata_count_serialize_all in_msgs;
      WStep.lemma_raw_appdata_count_seq_equal
        server.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_hsp_deliver_to_server
  (a:SY.tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ hs_seq_pairing a /\
        a.channel == SY.tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
        SY.tls_no_rekeying ({ a with server = s'; channel = MP.Quiet }))
      (ensures hs_seq_pairing ({ a with server = s'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with server = s'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
    assert (cs_hs_seq_ok a /\ sc_hs_seq_ok a);
    assert (a.channel == MP.ToServer p);
    eliminate exists (msg:M.tls_message).
      (let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
       SMCan.canonical_wire_step a.server s' conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
         (CW.wire_serialize wire) /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns hs_seq_pairing b
    with _pd.
    (
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Received msg == Some s'.CS.cs_model);
      // server WRITE frozen by the receive: full slot equality (epoch + seq).
      lemma_recv_preserves_wr_full a.server.CS.cs_model s'.CS.cs_model msg;
      // SC arm (EASY): server writes, client reads; the client is untouched, and
      // the frozen server write transfers the pre-state Quiet-analog `sc` clause.
      assert (sc_hs_seq_ok b);
      // CS arm (SUBSTANTIVE, but 0==0 here — this model has no client auth, so
      // the client never advances a protected HANDSHAKE-write while the server is
      // at a Handshake READ, and the server never advances a Handshake READ at all;
      // the CF-window client HANDSHAKE-write-1 is rescued because delivering it
      // moves the server to the post-CF (App-read) region, killing the gate).
      introduce (R.Handshake? (ASP.wr a.client).R.epoch /\
                 R.Handshake? (ASP.rd s').R.epoch /\
                 not (terminal_control s'.CS.cs_model.CS.model_control))
                ==> hs_wseq a.client == hs_rseq s'
      with _g.
      (
        let cfg_s = a.server.CS.cs_model.CS.model_config in
        // s' is reachable and consistent (one legal server step from a.server).
        WStep.lemma_server_reachable_step
          (CS.initial cfg_s) a.server s' (SM.WireEvent wire) out;
        lemma_server_step_single_step a.server (SM.WireEvent wire) s' out;
        lemma_step_preserves_consistent a.server s';
        WStep.lemma_step_model_preserves_config a.server.CS.cs_model conn_ev s'.CS.cs_model;
        // BYTE EQUALITY  a.client.raw_sent == s'.raw_received.
        //   canonical_wire_step:  s'.raw_received == a.server.raw_received ++ raw
        //   byte_pairing (ToServer p):  a.client.raw_sent == a.server.raw_received ++ raw
        assert (Seq.equal s'.CS.cs_wire_log.CL.raw_received
                  (B.append a.server.CS.cs_wire_log.CL.raw_received raw));
        assert (Seq.equal a.client.CS.cs_wire_log.CL.raw_sent
                  (B.append a.server.CS.cs_wire_log.CL.raw_received raw));
        Seq.lemma_eq_elim a.client.CS.cs_wire_log.CL.raw_sent
                          s'.CS.cs_wire_log.CL.raw_received;
        // The server, at a Handshake READ epoch (non-terminal), has received ZERO
        // ApplicationData-typed records.
        lemma_server_hs_read_recv_count_zero cfg_s s';
        WStep.lemma_raw_appdata_count_seq_equal
          s'.CS.cs_wire_log.CL.raw_received a.client.CS.cs_wire_log.CL.raw_sent;
        // Both cs-direction handshake projections collapse to 0.
        lemma_cs_zero_from_counts a.client s'
      );
      assert (cs_hs_seq_ok b)
    )
#pop-options

(** SEND write-epoch monotonicity (the piece that dissolves the "snapshot NOT
    handshake write" branch).  A non-`KeyUpdate` `Sent` step NEVER installs a
    Handshake write epoch — the only Handshake-write installer is a LOCAL key-install
    event (`step_local_message`), and the only write-epoch-changing `Sent` arms are
    `KeyUpdate` (excluded) and the client-Finished-at-`HsServerFinishedVerified`
    install (which lands on `Application`, excluded by the POST Handshake-write
    premise).  Every other `Sent` arm does `next_seq` (epoch-preserving) or leaves the
    record untouched.  So a POST Handshake write forces a PRE Handshake write. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_hs_send_preserves_hs_write
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent msg == Some m' /\
        ~(M.TlsKeyUpdate? msg) /\
        R.Handshake? m'.CS.model_record.CS.record_write.R.epoch)
      (ensures R.Handshake? m.CS.model_record.CS.record_write.R.epoch)
  = ()
#pop-options

(** A `Received` handshake message that lands in `ControlHandshaking` at a Handshake
    read epoch (and is not cleartext) is one of EE / Cert / CV.  Finished installs the
    Application read epoch (excluded by POST Handshake read); appdata / ignored-post-
    handshake at `ControlApplicationData` are Application-read at a CONSISTENT state
    (excluded); SH/HRR/CCS/ClientHello are cleartext (excluded).  Mirrors the
    enumeration of `lemma_hs_recv_plus_one_gated`. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 40 --split_queries always"
let lemma_hs_recv_is_ee_cert_cv
  (st st':CS.connection_state) (msg:M.tls_message)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        CS.step_tls_message st.CS.cs_model CL.Received msg == Some st'.CS.cs_model /\
        CS.network_message_is_cleartext CL.Received msg == false /\
        R.Handshake? (ASP.rd st').R.epoch /\
        CS.ControlHandshaking? st'.CS.cs_model.CS.model_control)
      (ensures
        M.TlsHandshake? msg /\
        (M.EncryptedExtensions? (M.TlsHandshake?._0 msg) \/
         M.Certificate? (M.TlsHandshake?._0 msg) \/
         M.CertificateVerify? (M.TlsHandshake?._0 msg)))
  = match msg, st.CS.cs_model.CS.model_control with
    | M.TlsHandshake (M.EncryptedExtensions _), _ -> ()
    | M.TlsHandshake (M.Certificate _), _ -> ()
    | M.TlsHandshake (M.CertificateVerify _), _ -> ()
    | _, CS.ControlApplicationData ->
        let role = st.CS.cs_model.CS.model_config.CS.config_role in
        CSL.lemma_connection_appdata_keys_installed_for_role role st;
        CSL.lemma_connection_application_ready_record_epochs_installed role st
    | _ -> ()
#pop-options

(** SEND `+1`.  An EE / Cert / CV `Sent` step from a Handshake write epoch advances
    the write seq by EXACTLY 1 (`record_write = next_seq`) and preserves the Handshake
    epoch.  The send arm for each fires at a unique control (HsServerHelloSent /
    HsServerEncryptedFlightSent), so step-success pins it. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_hs_send_plus_one
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires
        CS.step_tls_message m CL.Sent msg == Some m' /\
        R.Handshake? m.CS.model_record.CS.record_write.R.epoch /\
        M.TlsHandshake? msg /\
        (M.EncryptedExtensions? (M.TlsHandshake?._0 msg) \/
         M.Certificate? (M.TlsHandshake?._0 msg) \/
         M.CertificateVerify? (M.TlsHandshake?._0 msg)))
      (ensures
        R.Handshake? m'.CS.model_record.CS.record_write.R.epoch /\
        m'.CS.model_record.CS.record_write.R.seq ==
          m.CS.model_record.CS.record_write.R.seq + 1)
  = ()
#pop-options

(** Handshake-read-gated NOT-CLEARTEXT hinge (the analogue of
    `ASP.lemma_client_recv_msg_not_cleartext`, which is App-read-gated).  Given that
    the received wire record `raw` is `Application_data`-typed, a cleartext RECEIVE is
    impossible: ClientHello / CCS pin `raw` to a non-`Application_data` record
    (`WStep.lemma_cleartext_recv_not_appdata`); ServerHello pins `raw` to the
    serialized Handshake record (whose `parse_record_wire` is `Handshake`, not
    `Application_data`, or — if oversize — empty, contradicting the nonempty parse);
    HRR steps to `fail_model` (terminal, excluded by `~terminal`). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 50 --split_queries always"
let lemma_hsp_client_recv_not_cleartext
  (client:CS.connection_state) (msg:M.tls_message) (m':CS.connection_model) (raw:B.bytes)
  : Lemma
      (requires
        CS.step_tls_message client.CS.cs_model CL.Received msg == Some m' /\
        CS.network_message_raw_delta_legal client.CS.cs_model
          ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw /\
        (match W.parse_record_wire raw with
         | Some (ct, _, _) -> ct == T.Application_data
         | None -> False) /\
        not (terminal_control m'.CS.model_control))
      (ensures CS.network_message_is_cleartext CL.Received msg == false)
  = if CS.network_message_is_cleartext CL.Received msg then
      (match msg with
       | M.TlsHandshake (M.ClientHello _) ->
           WStep.lemma_cleartext_recv_not_appdata client.CS.cs_model msg raw
       | M.TlsChangeCipherSpec ->
           WStep.lemma_cleartext_recv_not_appdata client.CS.cs_model msg raw
       | M.TlsHandshake (M.ServerHello sh) ->
           // received cleartext ServerHello: raw == serialized_cleartext SH, a
           // Handshake record — its parse_record_wire is Handshake, not
           // Application_data (or, if oversize, empty — contradicting nonempty parse).
           let hsm = M.ServerHello sh in
           W.lemma_serialize_tls_message_handshake hsm;
           let frag = W.serialize_handshake hsm in
           Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message (M.TlsHandshake hsm));
           if B.length frag <= 16640 then
             (W.lemma_parse_record_serialize_record T.Handshake frag;
              W.lemma_parse_record_implies_parse_record_wire
                (W.serialize_record T.Handshake frag))
           else
             (W.lemma_serialize_record_oversize T.Handshake frag;
              match W.parse_record_wire raw with
              | Some (ct, f, consumed) ->
                  W.lemma_parse_record_wire_some_consumed_positive raw ct f consumed
              | None -> ())
       | _ ->
           // HelloRetryRequest: the ONLY `Received` arm steps to `fail_model`
           // (ControlFailed — terminal), contradicting `~terminal`.
           ())
    else ()
#pop-options

(** SENT-side analogue of `lemma_cleartext_recv_not_appdata`: a cleartext SEND
    (ClientHello / ServerHello / CCS) pins `raw` to a non-`Application_data` record
    (a Handshake record for the hellos, a Change_cipher_spec record for CCS), so
    `parse_record_wire raw` is never `Application_data` (or empty, if oversize). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 50 --split_queries always"
let lemma_cleartext_sent_raw_not_appdata
  (sent:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Sent sent == true /\
        CS.cleartext_tls_message_raw sent raw)
      (ensures
        (match W.parse_record_wire raw with
         | Some (ct, _, _) -> ~(ct == T.Application_data)
         | None -> True))
  = match sent with
    | M.TlsChangeCipherSpec ->
        W.lemma_serialize_tls_message_change_cipher_spec ();
        WFL.lemma_parse_record_wire_serialize_record T.Change_cipher_spec (B.singleton 1uy);
        Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec)
    | M.TlsHandshake hsm ->
        // ClientHello or ServerHello: raw == serialized_cleartext, a Handshake record
        W.lemma_serialize_tls_message_handshake hsm;
        let frag = W.serialize_handshake hsm in
        Seq.lemma_eq_elim raw (CS.serialized_cleartext_tls_message (M.TlsHandshake hsm));
        if B.length frag <= 16640 then
          (W.lemma_parse_record_serialize_record T.Handshake frag;
           W.lemma_parse_record_implies_parse_record_wire
             (W.serialize_record T.Handshake frag))
        else
          (W.lemma_serialize_record_oversize T.Handshake frag;
           match W.parse_record_wire raw with
           | Some (ct, f, consumed) ->
               W.lemma_parse_record_wire_some_consumed_positive raw ct f consumed
           | None -> ())
#pop-options

(** A network RECEIVE never installs a Handshake read epoch: every receive arm
    either preserves `record_read` (`with_handshake_stage` / `fail_model` / CCS),
    advances it with `next_seq` (epoch-preserving), or installs an APPLICATION
    read epoch (Finished / KeyUpdate).  Hence a post-receive Handshake read epoch
    forces a pre-receive Handshake read epoch. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_recv_preserves_read_epoch_handshake
  (client c':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message client CL.Received msg == Some c')
      (ensures
        R.Handshake? c'.CS.model_record.CS.record_read.R.epoch ==>
        R.Handshake? client.CS.model_record.CS.record_read.R.epoch)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_hsp_deliver_to_client
  (a:SY.tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\ hs_seq_pairing a /\
        a.channel == SY.tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
        hs_channel_seal_ok a /\
        SY.tls_no_rekeying ({ a with client = c'; channel = MP.Quiet }))
      (ensures hs_seq_pairing ({ a with client = c'; channel = MP.Quiet }))
  = let b : SY.tls_system_state = { a with client = c'; channel = MP.Quiet } in
    let p : SY.tls_payload = { SY.pl_raw = raw; SY.pl_snap = snap; SY.pl_sent = sent } in
    assert (cs_hs_seq_ok a /\ sc_hs_seq_ok a);
    assert (a.channel == MP.ToClient p);
    eliminate exists (msg:M.tls_message).
      (let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
       SMCan.canonical_wire_step a.client c' conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
         (CW.wire_serialize wire) /\
       EC.network_input_message_projection a.client wire msg /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns hs_seq_pairing b
    with _pd.
    (
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
      assert (CS.step_tls_message a.client.CS.cs_model CL.Received msg == Some c'.CS.cs_model);
      // client WRITE frozen by the receive: full slot equality (epoch + seq).
      lemma_recv_preserves_wr_full a.client.CS.cs_model c'.CS.cs_model msg;
      // CS arm (EASY): client writes, server reads; the server is untouched, and
      // the frozen client write transfers the pre-state Quiet-analog `cs` clause.
      assert (cs_hs_seq_ok b);
      // SC arm (SUBSTANTIVE): server writes EE/Cert/CV at Handshake write seq 1..4,
      // the client receives `+1` each.  Closed via FAITHFUL DECODE of the in-flight
      // server handshake record (`msg == sent`), obtained from the added
      // `inflight_bridge_ready` precondition (key/iv agreement + single-record seal +
      // roundtrip) plus the cross-endpoint seq alignment carried by `sc_hs_seq_ok a`.
      // This is the Handshake analogue of `ASP.lemma_asp_deliver_to_client`'s App
      // branch; the bridge is Handshake-write-gated on the sealing SNAPSHOT so that
      // the alert-inflation window (snapshot NOT on handshake write) does not assert
      // it — protocol-faithful, since a handshake-keyed record is undecodable to a
      // peer that has left the handshake read epoch.
      introduce (R.Handshake? (ASP.wr a.server).R.epoch /\
                 R.Handshake? (ASP.rd c').R.epoch /\
                 not (terminal_control c'.CS.cs_model.CS.model_control))
                ==> hs_wseq a.server == hs_rseq c'
      with _g.
      (
        // Expose the carried in-flight facts from `app_extras`.
        assert (ASP.inflight_sender_stepped a /\ ASP.inflight_raw_delta_legal a /\
                ASP.inflight_single_record a);
        // (0) The frozen SENDER stepped from the snapshot: step snap Sent sent ==
        //     Some a.server.cs_model, with ~KeyUpdate sent.
        assert (CS.step_tls_message snap CL.Sent sent == Some a.server.CS.cs_model);
        assert (~(M.TlsKeyUpdate? sent));
        // (1) A non-KeyUpdate Sent step never installs a Handshake write epoch, so the
        //     POST Handshake write (gate) forces a PRE (snapshot) Handshake write.
        lemma_hs_send_preserves_hs_write snap a.server.CS.cs_model sent;
        assert (R.Handshake? snap.CS.model_record.CS.record_write.R.epoch);
        assert (R.Handshake? (ASP.snap_wr p).R.epoch);
        // (2) The pre-state client is non-terminal (terminal set is absorbing).
        lemma_step_terminal_control_absorbing a.client.CS.cs_model c'.CS.cs_model conn_ev;
        assert (not (terminal_control a.client.CS.cs_model.CS.model_control));
        if CS.network_message_is_cleartext CL.Sent sent then
        (
          // CLEARTEXT in-flight send: `sent` is ClientHello / ServerHello / CCS, and
          // `raw` is the cleartext (Handshake / CCS) record for `sent`.
          assert (CS.network_message_raw_delta_legal snap
                    ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw);
          assert (CS.cleartext_tls_message_raw sent raw);
          lemma_cleartext_sent_raw_not_appdata sent raw;
          // parse_record_wire raw is NOT Application_data-typed.
          if R.Handshake? (ASP.rd a.client).R.epoch then
          (
            // With snap_wr Handshake + rd a.client Handshake + ~terminal a.client the
            // gate fires: the seal claims `raw` parses as an Application_data record,
            // contradicting the cleartext (non-Application_data) record above.
            assert (ASP.inflight_bridge_ready snap a.client.CS.cs_model sent raw);
            assert (SMCan.sent_single_protected_message_seal snap sent raw);
            W.lemma_parse_record_implies_parse_record_wire raw;
            // parse_record_wire raw == Some (Application_data, ...) — contradiction.
            assert (hs_wseq a.server == hs_rseq c')
          )
          else
          (
            // rd a.client is NOT Handshake.  A network receive never installs a
            // Handshake read epoch, so `rd c'` is not Handshake either —
            // contradicting the gate `R.Handshake? (ASP.rd c')`.
            lemma_recv_preserves_read_epoch_handshake
              a.client.CS.cs_model c'.CS.cs_model msg;
            assert (hs_wseq a.server == hs_rseq c')
          )
        )
        else
        (
          // NON-cleartext in-flight send: `pl_raw` is a single Application_data
          // record (`inflight_raw_delta_legal` + `inflight_single_record`).
          assert (CS.protected_record_count CL.Sent sent == 1);
          assert (CS.network_message_raw_delta_legal snap
                    ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw);
          assert (CS.raw_records_exactly raw T.Application_data 1);
          lemma_rre_nonempty raw;
          assert (B.length raw > 0);
          CSL.lemma_raw_records_exactly_one_parse_record raw T.Application_data;
          W.lemma_parse_record_implies_parse_record_wire raw;
          // (3) The received message is NOT cleartext (raw is Application_data-typed).
          assert (CS.network_message_raw_delta_legal a.client.CS.cs_model
                    ({ CL.message_direction = CL.Received; CL.message_value = msg }) raw);
          lemma_hsp_client_recv_not_cleartext a.client msg c'.CS.cs_model raw;
          assert (CS.network_message_is_cleartext CL.Received msg == false);
          // (4) The receive is a `+1` handshake receive: pre Handshake read,
          //     ControlHandshaking post, read seq advanced by exactly one.
          assert (SMR.connection_state_consistent a.client);
          lemma_hs_recv_plus_one_gated a.client c' msg;
          assert (R.Handshake? (ASP.rd a.client).R.epoch);
          assert ((ASP.rd c').R.seq == (ASP.rd a.client).R.seq + 1);
          // (5) With snap_wr Handshake + rd a.client Handshake + ~terminal a.client,
          //     `hs_channel_seal_ok a` fires: the faithful-decode bridge holds.
          assert (ASP.inflight_bridge_ready snap a.client.CS.cs_model sent raw);
          assert (SMCan.sent_single_protected_message_seal snap sent raw);
          // (6) Fire the pre-state in-flight `sc` clause: snap handshake write ==
          //     a.client handshake read seq.
          assert (snap_hs_wseq p == hs_rseq a.client);
          assert (snap.CS.model_record.CS.record_write.R.seq ==
                  a.client.CS.cs_model.CS.model_record.CS.record_read.R.seq);
          // (7) FAITHFUL DECODE: the client decodes raw to `sent`.
          CSL.lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
            snap a.client.CS.cs_model sent raw;
          assert (SMCan.received_single_protected_message_decode a.client.CS.cs_model sent raw);
          assert (SMCan.received_single_protected_message_decode a.client.CS.cs_model msg raw);
          ASP.lemma_decode_functional a.client.CS.cs_model msg sent raw;
          assert (msg == sent);
          // (8) `sent` (== msg) is EE / Cert / CV, so the matching SEND advances the
          //      server's handshake write seq by exactly one.
          lemma_hs_recv_is_ee_cert_cv a.client c' msg;
          lemma_hs_send_plus_one snap a.server.CS.cs_model sent;
          assert (a.server.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
                  snap.CS.model_record.CS.record_write.R.seq + 1);
          // (9) Chain: hs_wseq a.server == snap.write.seq + 1
          //                            == a.client.read.seq + 1 == c'.read.seq == hs_rseq c'.
          assert (hs_wseq a.server == hs_rseq c')
        )
      );
      assert (sc_hs_seq_ok b)
    )
#pop-options

(* ══════════════════════════════════════════════════════════════════════
   PART 2 — `hs_channel_seal_ok` step-family PRESERVATION.

   Only SERVER-SEND is substantive (it enters `MP.ToClient p` with a protected
   server handshake record in flight; the bridge must be established from
   `tls_system_inv a`).  Every other family lands the channel at `MP.Quiet`
   (locals/deliveries) or `MP.ToServer` (client-send), both of which hit the
   `_ -> True` arm of `hs_channel_seal_ok`, so they are vacuous.
   ══════════════════════════════════════════════════════════════════════ *)

(** A `Sent` step is never taken from a `ControlFailed` control (the only
    `ControlFailed` arm of `step_tls_message` is the `TlsAlert` receive, which
    returns `None` for `CL.Sent`; every other arm gates on a non-failed control
    or hits the catch-all `None`). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_sent_step_not_failed
  (m m':CS.connection_model) (msg:M.tls_message)
  : Lemma
      (requires CS.step_tls_message m CL.Sent msg == Some m')
      (ensures ~(CS.ControlFailed? m.CS.model_control))
  = ()
#pop-options

(** VACUOUS — CLIENT SEND (post channel `MP.ToServer` -> `_ -> True`). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_hscs_client_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_send a b /\ SY.tls_no_rekeying b)
      (ensures hs_channel_seal_ok b)
  = SY.lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = SY.tls_to_server (SY.emitted_raw out) a.client.CS.cs_model sent }
    returns hs_channel_seal_ok b
    with _pf. ()
#pop-options

(** VACUOUS — SERVER LOCAL (channel unchanged = `MP.Quiet`). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_hscs_server_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_local a b)
      (ensures hs_channel_seal_ok b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns hs_channel_seal_ok b
    with _pf. ()
#pop-options

(** VACUOUS — CLIENT LOCAL (channel unchanged = `MP.Quiet`). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_hscs_client_local (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_client_local a b)
      (ensures hs_channel_seal_ok b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns hs_channel_seal_ok b
    with _pf. ()
#pop-options

(** VACUOUS — DELIVER TO SERVER (post channel `MP.Quiet`). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_hscs_deliver_to_server
  (a:SY.tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        a.channel == SY.tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
        SY.tls_no_rekeying ({ a with server = s'; channel = MP.Quiet }))
      (ensures hs_channel_seal_ok ({ a with server = s'; channel = MP.Quiet }))
  = ()
#pop-options

(** VACUOUS — DELIVER TO CLIENT (post channel `MP.Quiet`). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_hscs_deliver_to_client
  (a:SY.tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        SY.tls_system_inv a /\ ASP.app_extras a /\
        a.channel == SY.tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
        SY.tls_no_rekeying ({ a with client = c'; channel = MP.Quiet }))
      (ensures hs_channel_seal_ok ({ a with client = c'; channel = MP.Quiet }))
  = ()
#pop-options

(** CLIENT hellos from the client read-Hs control pin.  Under the gate the client
    has a Handshake READ epoch and is non-terminal (hence non-failed); `cr_ctrl_shape`
    pins its control to one of the six client handshake-flight controls, each of
    which lower-bounds both hellos in `client_stage_ok`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_client_read_hs_hellos (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        R.Handshake? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch /\
        ~(CS.ControlFailed? st.CS.cs_model.CS.model_control) /\
        SY.client_stage_ok st)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_hello)
  = lemma_consistent_cr_ctrl_shape st
#pop-options

(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 2 support — CF-TOLERANT client hellos.

   A reachable CLIENT with a Handshake READ epoch has both hellos present,
   INCLUDING at ControlFailed (where [client_stage_ok]/[lemma_client_read_hs_hellos]
   give nothing).  [cr_ctrl_shape] pins the NON-failed control to a
   client_read_hs_control (each lower-bounding both hellos); [client_ctrl_hellos_lb]
   supplies that lower bound as a pure control-keyed MONOTONE shape; the epoch-
   gated conjunct BRIDGES the fail step ([fail_model] preserves model_handshake +
   model_record wholesale).  This is what supplies the four-hello / checkpoint
   ingredients to the SEAL bridge at a FAILED reader once [~terminal(client)] is
   dropped from [hs_channel_seal_ok]. *)
let client_ctrl_hellos_lb (model:CS.connection_model) : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
  (match model.CS.model_control with
   | CS.ControlHandshaking CS.HsClientHelloSent ->
     Some? model.CS.model_handshake.CS.hs_client_hello
   | CS.ControlHandshaking CS.HsServerHelloReceived
   | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
   | CS.ControlHandshaking CS.HsCertificateReceived
   | CS.ControlHandshaking CS.HsCertificateValidated
   | CS.ControlHandshaking CS.HsCertificateVerifyReceived
   | CS.ControlHandshaking CS.HsCertificateVerifyVerified
   | CS.ControlHandshaking CS.HsServerFinishedReceived
   | CS.ControlHandshaking CS.HsServerFinishedVerified
   | CS.ControlHandshaking CS.HsClientFinishedSent
   | CS.ControlApplicationData
   | CS.ControlClosing
   | CS.ControlClosed ->
     Some? model.CS.model_handshake.CS.hs_client_hello /\
     Some? model.CS.model_handshake.CS.hs_server_hello
   | _ -> True)

let hellos_present (model:CS.connection_model) : prop =
  Some? model.CS.model_handshake.CS.hs_client_hello /\
  Some? model.CS.model_handshake.CS.hs_server_hello

let client_read_hellos_shape (st:CS.connection_state) : prop =
  conn_cr_ctrl_shape st /\
  client_ctrl_hellos_lb st.CS.cs_model /\
  ( (st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
     R.Handshake? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
    ==> hellos_present st.CS.cs_model )

#push-options "--fuel 2 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_step_client_ctrl_hellos_lb
  (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires client_ctrl_hellos_lb model /\ CS.legal_event model ev /\
                CS.step_model model ev == Some model')
      (ensures client_ctrl_hellos_lb model')
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 10 --z3rlimit 200 --split_queries always"
let lemma_step_failed_preserves_hs_record
  (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires CS.legal_event model ev /\ CS.step_model model ev == Some model' /\
                CS.ControlFailed? model'.CS.model_control)
      (ensures model'.CS.model_handshake == model.CS.model_handshake /\
               model'.CS.model_record == model.CS.model_record)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_delta_client_read_hellos_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires client_read_hellos_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures client_read_hellos_shape st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    WStep.lemma_step_model_preserves_config
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
    lemma_delta_cr_ctrl_shape st0 st1;
    lemma_step_client_ctrl_hellos_lb st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
    introduce
      (st1.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       R.Handshake? st1.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
      ==> hellos_present st1.CS.cs_model
    with _hyp.
    (
      if CS.ControlFailed? st1.CS.cs_model.CS.model_control then
      (
        lemma_step_failed_preserves_hs_record
          st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
        assert (R.Handshake? st0.CS.cs_model.CS.model_record.CS.record_read.R.epoch);
        assert (st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert (hellos_present st0.CS.cs_model)
      )
      else
      (
        assert (conn_cr_ctrl_shape st1);
        assert (~(CS.ControlFailed? st1.CS.cs_model.CS.model_control));
        assert (client_ctrl_hellos_lb st1.CS.cs_model)
      )
    )
#pop-options

let lemma_single_step_client_read_hellos_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (client_read_hellos_shape y); (SMR.connection_state_single_step x y)}
          client_read_hellos_shape x /\ SMR.connection_state_single_step x y ==>
            client_read_hellos_shape y)
  = introduce forall x y.
      client_read_hellos_shape x /\ SMR.connection_state_single_step x y ==>
        client_read_hellos_shape y
    with introduce _ ==> _ with _.
      lemma_delta_client_read_hellos_shape x y

let lemma_initial_client_read_hellos_shape (cfg:CS.connection_config)
  : Lemma (ensures client_read_hellos_shape (CS.initial cfg))
  = lemma_initial_cr_ctrl_shape cfg

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_client_hs_read_hellos_cf (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        R.Handshake? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_hello)
  = lemma_initial_client_read_hellos_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_client_read_hellos_shape ();
    let p = client_read_hellos_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(* ── SERVER hello-presence shape ────────────────────────────────────────────
   A server's two hellos (`hs_client_hello` from the CH receive, `hs_server_hello`
   from the SH send) are set once and never cleared, so their presence is a
   MONOTONE property.  `server_stage_ok` lower-bounds them only up through
   `ControlApplicationData`; this shape extends the same lower bound to the
   closing region (`ControlClosing`/`ControlClosed`), which is reachable only from
   `ControlApplicationData`.  Being purely monotone (every transition either sets a
   hello or preserves the ones already present), the shape is single-step
   inductive on its own — it does not need the deeper reachable-shape machinery. *)
let server_hellos_shape (model:CS.connection_model) : prop =
  model.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
  (match model.CS.model_control with
   | CS.ControlHandshaking CS.HsClientHelloReceived ->
     Some? model.CS.model_handshake.CS.hs_client_hello
   | CS.ControlHandshaking CS.HsServerHelloSent
   | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
   | CS.ControlHandshaking CS.HsServerFinishedSent
   | CS.ControlHandshaking CS.HsClientFinishedReceived
   | CS.ControlHandshaking CS.HsClientFinishedVerified
   | CS.ControlApplicationData
   | CS.ControlClosing
   | CS.ControlClosed ->
     Some? model.CS.model_handshake.CS.hs_client_hello /\
     Some? model.CS.model_handshake.CS.hs_server_hello
   | _ -> True)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_server_hellos_shape
  (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma
      (requires server_hellos_shape model /\ CS.legal_event model ev /\
                CS.step_model model ev == Some model')
      (ensures server_hellos_shape model')
  = ()
#pop-options

let conn_server_hellos_shape (st:CS.connection_state) : prop =
  server_hellos_shape st.CS.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_server_hellos_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires conn_server_hellos_shape st0 /\ SMR.connection_state_single_step st0 st1)
      (ensures conn_server_hellos_shape st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    lemma_step_server_hellos_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model
#pop-options

let lemma_single_step_server_hellos_shape (_:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (conn_server_hellos_shape y); (SMR.connection_state_single_step x y)}
          conn_server_hellos_shape x /\ SMR.connection_state_single_step x y ==>
            conn_server_hellos_shape y)
  = introduce forall x y.
      conn_server_hellos_shape x /\ SMR.connection_state_single_step x y ==>
        conn_server_hellos_shape y
    with introduce _ ==> _ with _.
      lemma_delta_server_hellos_shape x y

let lemma_initial_server_hellos_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_server_hellos_shape (CS.initial cfg))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_consistent_server_hellos_shape (st:CS.connection_state)
  : Lemma
      (requires SMR.connection_state_consistent st)
      (ensures conn_server_hellos_shape st)
  = lemma_initial_server_hellos_shape st.CS.cs_model.CS.model_config;
    lemma_single_step_server_hellos_shape ();
    let p = conn_server_hellos_shape in
    let stable :
      squash (forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** SERVER hellos at a protected-handshake SEND.  `~ControlFailed` excludes the
    failed control; `sinit_shape` (write epoch Handshake) excludes the pre-handshake
    controls (`ControlNew`/`HsNotStarted`/`HsAwaitingClientHello`, write epoch
    `Initial`); `server_stage_ok = False` rules out the client-only controls.  For
    every remaining control — the handshake-flight controls through
    `ControlApplicationData` (via `server_stage_ok`) and the closing region (via
    `server_hellos_shape`) — both hellos are present. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_server_hs_send_hellos (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(CS.ControlFailed? st.CS.cs_model.CS.model_control) /\
        R.Handshake? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch /\
        SY.server_stage_ok st)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_hello)
  = lemma_consistent_sinit_shape st;
    lemma_consistent_server_hellos_shape st
#pop-options

(** The `same_key_derivation_checkpoint` discharge, factored (copied verbatim from
    `HsMaterialFamilies.lemma_establish_cf`, adjusted to `client=a.client`,
    `server=a.server`).  Requires the four cleartext hellos present and the two
    wire-equivalence facts (both `tls_system_inv` conjuncts). **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_hscs_checkpoint (s:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv s /\
        Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
        Some? s.server.CS.cs_model.CS.model_handshake.CS.hs_server_hello)
      (ensures
        SMCorr.same_key_derivation_checkpoint SMKI.DeriveHandshakeTraffic s.client s.server)
  = let client = s.client in
    let server = s.server in
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
       returns SMCorr.same_key_derivation_checkpoint SMKI.DeriveHandshakeTraffic client server
       with _p1.
         eliminate exists raw2.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
         returns SMCorr.same_key_derivation_checkpoint SMKI.DeriveHandshakeTraffic client server
         with _p2.
           WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
             client server client_ch server_ch client_sh server_sh
             raw1 raw1 raw2 raw2
     | _ -> ())
#pop-options

(** COMP 1 assembly — the server-write/client-read handshake key/iv material
    agreement, packaged as `peer_record_material_agrees` for `ServerTraffic`.
    The two record→slot LINKS produce the `record_direction_material_matches_
    key_schedule_for_role` inputs (and, as a by-product, the presence of the two
    `ks_server_handshake_traffic` slots), and `HANR`'s ControlFailed-aware
    server-traffic slot-agreement producer supplies the slot-level agreement. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_hscs_bridge_material (client server:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent client /\
        SMR.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        R.Handshake? client.CS.cs_model.CS.model_record.CS.record_read.R.epoch /\
        R.Handshake? server.CS.cs_model.CS.model_record.CS.record_write.R.epoch /\
        ~(CS.ControlFailed? server.CS.cs_model.CS.model_control) /\
        Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        WFL.paired_cleartext_hello_key_shares client server /\
        SMCorr.same_key_derivation_checkpoint SMKI.DeriveHandshakeTraffic client server)
      (ensures
        SMKM.peer_record_material_agrees
          (SMKI.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server)
  = // record-keys consistency for the server (at its config role).
    CSL.lemma_connection_state_consistent_record_keys_consistent_for_config_role server;
    assert (SMKM.model_record_keys_consistent_for_role CS.ServerEndpoint server.CS.cs_model);
    // WRITE link (server, non-failed) and READ link (client, via PERSISTENCE —
    // holds even at ControlFailed), both at the Handshake epoch.
    CSL.lemma_handshake_record_direction_material_matches_key_schedule_for_role
      CS.ServerEndpoint CS.TrafficWrite server.CS.cs_model;
    CSL.lemma_client_hs_read_slot_link_persist client;
    assert (SMKI.traffic_id CS.TrafficHandshake
              (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite)
              == SMKI.traffic_id CS.TrafficHandshake CS.ServerTraffic);
    assert (SMKI.traffic_id CS.TrafficHandshake
              (CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead)
              == SMKI.traffic_id CS.TrafficHandshake CS.ServerTraffic);
    // slot presence falls out of the two links (traffic_material_for_label match).
    assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    // slot-level agreement (ControlFailed-aware, server-traffic).
    HANR.lemma_handshake_server_traffic_key_schedule_material_agrees_nonready_cf client server;
    // inputs assembled -> peer_record_material_agrees.
    assert (SMKM.peer_record_material_inputs_agree
              (SMKI.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server);
    CSL.lemma_peer_record_material_agrees
      (SMKI.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server
#pop-options

(** SUBSTANTIVE — SERVER SEND.  Enters `MP.ToClient p` with `p.pl_snap ==
    a.server.cs_model`, `p.pl_sent == sent`, `p.pl_raw == emitted_raw out`, and
    `b.client == a.client`.  Under the post-state gate the sealing snapshot's
    write epoch and the client's read epoch are `Handshake` and the client is
    non-terminal; the bridge (key/iv agreement + single-record seal + roundtrip)
    is assembled from `tls_system_inv a`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_hscs_server_send (a b:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\ MP.Quiet? a.channel /\
        SY.tls_step_server_send a b /\ SY.tls_no_rekeying b)
      (ensures hs_channel_seal_ok b)
  = SY.lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = SY.tls_to_client (SY.emitted_raw out) a.server.CS.cs_model sent }
    returns hs_channel_seal_ok b
    with _pf.
    (
      ASP.lemma_server_send_pins_model a.server s' local out sent;
      assert (CS.step_tls_message a.server.CS.cs_model CL.Sent sent == Some s'.CS.cs_model);
      // b.channel = MP.ToClient p with p.pl_snap = a.server.cs_model, p.pl_sent = sent,
      // p.pl_raw = emitted_raw out, and b.client = a.client.
      introduce
        (R.Handshake? a.server.CS.cs_model.CS.model_record.CS.record_write.R.epoch /\
         R.Handshake? (ASP.rd a.client).R.epoch) ==>
          ASP.inflight_bridge_ready a.server.CS.cs_model a.client.CS.cs_model sent
            (SY.emitted_raw out)
      with _g.
      (
        // ~ControlFailed on the SERVER (sender); the CLIENT may be ControlFailed —
        // persistence (Phase 1A) supplies its record<->slot READ link regardless.
        lemma_sent_step_not_failed a.server.CS.cs_model s'.CS.cs_model sent;
        assert (~(CS.ControlFailed? a.server.CS.cs_model.CS.model_control));
        // COMP 2 + COMP 3 — seal + roundtrip.
        lemma_server_send_seal_rt a.server s' local out w sent;
        // FOUR HELLOS — client hellos via the CF-tolerant reachable shape.
        assert (SY.server_stage_ok a.server);
        lemma_client_hs_read_hellos_cf a.client;
        lemma_server_hs_send_hellos a.server;
        assert (WFL.paired_cleartext_hello_key_shares a.client a.server);
        lemma_hscs_checkpoint a;
        // shared secret both.
        lemma_consistent_hs_write_shared_secret a.server;
        lemma_consistent_hs_read_shared_secret a.client;
        // COMP 1 — key/iv material agreement.
        lemma_hscs_bridge_material a.client a.server;
        assert (SMKM.peer_record_material_agrees
                  (SMKI.traffic_id CS.TrafficHandshake CS.ServerTraffic) a.client a.server)
      )
    )
#pop-options
