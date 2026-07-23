module TLS13.System

(**
  The combined TLS 1.3 client<->server system — WIRE-LEVEL channel.

  This scales the `calc_sample` combined-system + temporal approach up to real
  TLS.  It composes two `TLS13.Spec.ConnectionState.connection_state`s (a client
  and a server) with an explicit in-flight *raw-byte* channel, and advances each
  endpoint by exactly one step of the OFFICIAL canonical TLS transition relation
  (`TLS13.Impl.Client.CanonicalProtocol.client_step` /
  `TLS13.Impl.Server.CanonicalProtocol.server_step`) — used verbatim, with no
  wrapper and no event-log pin.

  Because the channel carries raw bytes, a delivery feeds the receiver *real wire
  bytes*, which the receiver parses into its own (body=full) message.  This makes
  deliveries genuinely inhabited (unlike a body=empty semantic delivery, which is
  unsatisfiable against `CS.received_cleartext_tls_message_raw`), so the flagship
  record-material-agreement theorem is NON-VACUOUS.  The body asymmetry (sender
  body=empty, receiver body=full) is reconciled by WIRE EQUIVALENCE, exactly what
  the pairing payoff lemma expects.
**)

module CS  = TLS13.Spec.ConnectionState
module M   = TLS13.Messages
module CL  = TLS13.ConnectionLog
module B   = TLS13.Bytes
module Seq = FStar.Seq
module RTC = FStar.ReflexiveTransitiveClosure
module CD  = TLS13.Impl.Client.Driver
module SD  = TLS13.Impl.Server.Driver
module P   = TLS13.Impl.Driver.Pairing
module CSL = TLS13.ConnectionState.Lemmas
module SM  = Common.StateMachine
module CW  = TLS13.Impl.CanonicalWire
module CTy = TLS13.Impl.CanonicalTypes
module CCP = TLS13.Impl.Client.CanonicalProtocol
module SCP = TLS13.Impl.Server.CanonicalProtocol
module WF  = Common.WireFormat
module WFL = TLS13.Spec.WireFormatLemmas
module W   = TLS13.Wire.Spec
module T   = TLS13.Types
module R   = TLS13.Record.Spec
module S   = TLS13.StateMachine
module WStep = TLS13.System.WireStep
module CTy2 = TLS13.Impl.Client.Types
module U8   = FStar.UInt8
module TM   = TLS13.Impl.Messages
module SHPB = TLS13.Wire.Spec.Reveal.ServerHello.Parseback
// PHASE-1 clean16 removal: SBD (StagedBoundaryDerivation), PNTN (Normalized) and
// PNT (PairingNoTail) modules moved to the attic — no longer referenced now that
// lemma_pw_establish is the tracked gap.  PNTWL (WireLogs) is retained.
module WFSM = Common.WireFormatStateMachine
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module PC   = TLS13.System.ProgressCount
module PWL  = TLS13.ConnectionState.ProtectedWireBase
module ST   = TLS13.Impl.Server.Types
module SWR  = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank
module Bounds = TLS13.Impl.ConnectionState.Bounds
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module Sem = TLS13.Wire.Semantics
module SCB = TLS13.System.SeqCountBase
module C   = TLS13.Crypto.Spec
module ID  = FStar.IndefiniteDescription
module PWB = TLS13.ConnectionState.ProtectedWireBase
module RVDH = TLS13.Wire.Spec.Reveal.Handshake
module RVDF = TLS13.Wire.Spec.Reveal.Finished
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module GHS = TLS13.Wire.Generated.Handshake
module LP  = LowParse.Spec
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module PWH = TLS13.ConnectionState.ProtectedWireHead

open FStar.List.Tot

(** ─────────────────────────────────────────────────────────────────────────
    States
    ───────────────────────────────────────────────────────────────────────── **)

(** The in-flight raw-byte channel: at most one raw record in flight, tagged with
    the endpoint role that will receive it. **)
noeq
type tls_channel =
  | TlsQuiet    : tls_channel
  | TlsInFlight : recipient:CS.endpoint_role -> raw:B.bytes -> sender_snapshot:CS.connection_model -> sent:M.tls_message -> tls_channel

(** The combined system state: a client endpoint, a server endpoint, and the raw
    channel between them. **)
noeq
type tls_system_state = {
  client:  CS.connection_state;
  server:  CS.connection_state;
  channel: tls_channel;
}

(** The raw bytes an official step emits on the wire. **)
let emitted_raw (out:SM.step_output CW.wire_message CTy.local_output) : GTot B.bytes =
  WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs

(** A single-record wire output serializes to exactly that record's bytes. **)
let lemma_serialize_all_single (w:CW.wire_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format [w])
          (CW.wire_serialize w))
  = Seq.append_empty_r (CW.wire_serialize w)

(** The system is quiescent when nothing is in flight. **)
let tls_quiescent (s:tls_system_state) : prop = TlsQuiet? s.channel

(** Both endpoints have completed the handshake and installed application keys,
    at the canonical no-tail completion boundary (event log length exactly 16 on
    each side — the corrected handshake-completion length; see
    `TLS13.Impl.Driver.PairingNoTail`/`PairingNoTailServerShape`).  Pinning the
    boundary length is what makes the `clean16` byte-trace entry predicate
    available at a ready+quiescent state, from which the protected-flight
    projection witnesses (FACT 4) are derived on demand. **)
let tls_application_ready (s:tls_system_state) : prop =
  TLS13.Impl.Client.Driver.client_driver_application_ready s.client /\
  TLS13.Impl.Server.Driver.server_driver_application_ready s.server

(** Neither endpoint has performed a key update ("no rekeying"). **)
let tls_no_rekeying (s:tls_system_state) : prop =
  CS.connection_state_no_key_update_trace s.client /\
  CS.connection_state_no_key_update_trace s.server

(** Initial state: fresh client and server from their configs, empty channel. **)
let initial_tls_system (cfg_c cfg_s:CS.connection_config) : tls_system_state = {
  client  = CS.initial cfg_c;
  server  = CS.initial cfg_s;
  channel = TlsQuiet;
}

(** Handy projections. **)
let hsf (st:CS.connection_state) : CS.handshake_state =
  st.CS.cs_model.CS.model_handshake

let ctrl (st:CS.connection_state) : CS.connection_control_state =
  st.CS.cs_model.CS.model_control

(** ─────────────────────────────────────────────────────────────────────────
    Per-endpoint stage predicates (unchanged from the semantic version): they
    pin an endpoint to a role-appropriate control state and record which paired
    handshake fields must be populated at that stage.
    ───────────────────────────────────────────────────────────────────────── **)

let client_stage_ok (st:CS.connection_state) : prop =
  let h = hsf st in
  match ctrl st with
  | CS.ControlNew -> True
  | CS.ControlHandshaking CS.HsStarted -> True
  | CS.ControlHandshaking CS.HsClientHelloSent ->
    Some? h.CS.hs_client_hello
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions
  | CS.ControlHandshaking CS.HsCertificateReceived ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate
  | CS.ControlHandshaking CS.HsCertificateValidated ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify
  | CS.ControlHandshaking CS.HsServerFinishedReceived ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished
  | CS.ControlApplicationData ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished /\
    Some? h.CS.hs_client_finished
  // Terminal (post-application) control states, reached by sending/receiving an
  // alert (close-notify or a fatal alert).  No field lower bound is imposed
  // here — these stages carry no key-material obligation for the payoff, which
  // fires only at `ControlApplicationData`.
  | CS.ControlClosing -> True
  | CS.ControlClosed -> True
  | CS.ControlFailed _ -> True
  | _ -> False

(**
  Per-endpoint stage predicate for the *server* role.  The one stage with
  internal branching is `HsServerEncryptedFlightSent` (the server emits EE,
  Certificate, CertificateVerify and Finished while remaining at that control),
  so only `CH, SH, EE` are guaranteed there; the `Sent Finished` step separately
  requires Certificate and CertificateVerify before advancing.
**)
let server_stage_ok (st:CS.connection_state) : prop =
  let h = hsf st in
  match ctrl st with
  | CS.ControlNew -> True
  | CS.ControlHandshaking CS.HsAwaitingClientHello -> True
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    Some? h.CS.hs_client_hello
  | CS.ControlHandshaking CS.HsServerHelloSent ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions
  | CS.ControlHandshaking CS.HsServerFinishedSent ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished
  | CS.ControlHandshaking CS.HsClientFinishedReceived ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished /\
    Some? h.CS.hs_client_finished
  | CS.ControlHandshaking CS.HsClientFinishedVerified ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished /\
    Some? h.CS.hs_client_finished
  | CS.ControlApplicationData ->
    Some? h.CS.hs_client_hello /\ Some? h.CS.hs_server_hello /\
    Some? h.CS.hs_encrypted_extensions /\ Some? h.CS.hs_certificate /\
    Some? h.CS.hs_certificate_verify /\ Some? h.CS.hs_server_finished /\
    Some? h.CS.hs_client_finished
  | CS.ControlClosing -> True
  | CS.ControlClosed -> True
  | CS.ControlFailed _ -> True
  | _ -> False

(** ─────────────────────────────────────────────────────────────────────────
    The wire / projection FACTS composing the structural invariant.
    ───────────────────────────────────────────────────────────────────────── **)

(** FACT 1 — ClientHello wire-equivalence (client=sender, server=receiver). **)
let ch_wire_equiv (s:tls_system_state) : prop =
  match (hsf s.client).CS.hs_client_hello, (hsf s.server).CS.hs_client_hello with
  | Some client_ch, Some server_ch ->
    WFL.supported_client_hello_wire_profile client_ch /\
    (exists raw.
       CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw /\
       CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw)
  | _ -> True

(** FACT 2 — ServerHello wire-equivalence (server=sender, client=receiver). **)
let sh_wire_equiv (s:tls_system_state) : prop =
  match (hsf s.server).CS.hs_server_hello, (hsf s.client).CS.hs_server_hello with
  | Some server_sh, Some client_sh ->
    (exists raw.
       CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw /\
       CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw)
  | _ -> True

(** FACT 3 — paired key shares once all four hellos are present on both sides. **)
let hello_key_shares_ok (s:tls_system_state) : prop =
  (Some? (hsf s.client).CS.hs_client_hello /\ Some? (hsf s.server).CS.hs_client_hello /\
   Some? (hsf s.client).CS.hs_server_hello /\ Some? (hsf s.server).CS.hs_server_hello) ==>
    WFL.paired_cleartext_hello_key_shares s.client s.server

(** FACT 4 — protected event-projection witnesses.  Redefined (Phase 4) with a
    BOTH-READY antecedent; the definition appears below, next to `server_ready`,
    because it mentions `client_ready`/`server_ready`. **)

(** FACT 5 — channel consistency, RAW-KEYED.  The in-flight raw byte string alone
    determines whether a *cleartext hello* is mid-flight: a client->server record
    that parses as a cleartext ClientHello pins the client's stored CH (with wire
    profile); a server->client record that parses as a cleartext ServerHello pins
    the server's stored SH.  A *protected* record (Finished/appdata/etc.) parses as
    an ApplicationData record, so the hello antecedent is FALSE and the clause is
    vacuously true — no cross-endpoint control coupling is needed.  At a delivery
    the receiver's own parse of the raw supplies the antecedent, which then yields
    the sender-side hello for the wire-equivalence FACTS. **)
let channel_consistent (s:tls_system_state) : prop =
  match s.channel with
  | TlsQuiet -> True
  | TlsInFlight CS.ServerEndpoint raw _snap _sent ->
    ((exists server_ch.
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw)
     ==>
     (match (hsf s.client).CS.hs_client_hello with
      | Some client_ch ->
        WFL.supported_client_hello_wire_profile client_ch /\
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw
      | None -> False))
  | TlsInFlight CS.ClientEndpoint raw _snap _sent ->
    ((exists frag server_sh.
        W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw) /\
        W.parse_tls_message T.Handshake frag == Some (M.TlsHandshake (M.ServerHello server_sh)))
     ==>
     (match (hsf s.server).CS.hs_server_hello with
      | Some server_sh ->
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw
      | None -> False))

(** Client's recorded handshake start (if any) matches its config. **)
let start_ok_model (m:CS.connection_model) : prop =
  match m.CS.model_handshake.CS.hs_start with
  | Some start -> CS.start_matches_config m.CS.model_config start
  | None -> True

let client_start_ok (s:tls_system_state) : prop =
  start_ok_model s.client.CS.cs_model

(** Cross-endpoint hello coupling — the two MONOTONE clauses.  A received hello
    implies the peer sent it: the server has a stored ClientHello only after the
    client stored (sent) its CH (`sch ==> cch`), and the client has a stored
    ServerHello only after the server stored (sent) its SH (`csh ==> ssh`).  Both
    are preserved because the only transitions that set the receiver flag are the
    deliveries, and there `channel_consistent` supplies the matching sender hello
    from the in-flight raw. **)
let hello_coupling (s:tls_system_state) : prop =
  let cch = Some? (hsf s.client).CS.hs_client_hello in
  let csh = Some? (hsf s.client).CS.hs_server_hello in
  let sch = Some? (hsf s.server).CS.hs_client_hello in
  let ssh = Some? (hsf s.server).CS.hs_server_hello in
  (csh ==> ssh) /\
  (sch ==> cch)

(** ─────────────────────────────────────────────────────────────────────────
    Byte-level invariant families (STAGE B).

    Two families replace the inductively-maintained `protected_witnesses_ok`
    (FACT 4).  FACT 4 is instead established ON DEMAND at the ready+quiescent
    state (`lemma_ready_quiescent_agrees`) from these byte-level facts + the hello
    key-share agreement, via the `clean16` producer.

    (i) Per-endpoint REACHABILITY from the endpoint's own `CS.initial cfg`, via
        the OFFICIAL canonical step relation.  At a reachable state this yields
        `WFSM.valid_byte_trace` (WireStep), the byte-level entry predicate of
        `clean16`.
    (ii) The channel-aware BYTE PAIRING: the concatenation of one endpoint's
         sent bytes equals the other endpoint's received bytes PLUS whatever is
         currently in flight.  At `TlsQuiet` (nothing in flight) this collapses
         to exact `CS.paired_wire_logs`.
    ───────────────────────────────────────────────────────────────────────── **)

let client_byte_reachable (s:tls_system_state) : prop =
  WStep.client_reachable (CS.initial s.client.CS.cs_model.CS.model_config) s.client

let server_byte_reachable (s:tls_system_state) : prop =
  WStep.server_reachable (CS.initial s.server.CS.cs_model.CS.model_config) s.server

(** The channel-aware byte pairing.  `raw` in flight to the server extends the
    server's received bytes to reach the client's sent bytes (and symmetrically). **)
let byte_pairing (s:tls_system_state) : prop =
  let cs = s.client.CS.cs_wire_log.CL.raw_sent in
  let cr = s.client.CS.cs_wire_log.CL.raw_received in
  let ss = s.server.CS.cs_wire_log.CL.raw_sent in
  let sr = s.server.CS.cs_wire_log.CL.raw_received in
  match s.channel with
  | TlsQuiet ->
    Seq.equal cs sr /\ Seq.equal ss cr
  | TlsInFlight CS.ServerEndpoint raw _snap _sent ->
    Seq.equal cs (B.append sr raw) /\ Seq.equal ss cr
  | TlsInFlight CS.ClientEndpoint raw _snap _sent ->
    Seq.equal ss (B.append cr raw) /\ Seq.equal cs sr

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 2c-ii-C — the PROTECTED-CHANNEL readiness conjunct.

    For the single in-flight PROTECTED-handshake record (if any), carry exactly
    the facts a later stage needs to reconstruct the protected event-projection
    witness AT THE DELIVERY: the decode-glue precondition-conjunction
    (`peer_record_material_agrees`, seq alignment, the seal, and the roundtrip).

    The existential is GUARDED by BOTH endpoints being at the handshake record
    epoch and pre-application-data (guard `G` below).  The naive unguarded
    version is NON-INDUCTIVE: while a protected server record is in flight the
    recipient may still be at an `Initial` read epoch (it received ServerHello
    but has not yet installed its handshake read keys), and there the material
    facts are false.  Guarding by the recipient read epoch is harmless at the
    consumption site: at a protected-record delivery the recipient IS at the
    handshake read epoch and pre-application-data (it is about to open the
    record).
    ───────────────────────────────────────────────────────────────────────── **)

let recipient_state (s:tls_system_state) (r:CS.endpoint_role) : CS.connection_state =
  match r with
  | CS.ClientEndpoint -> s.client
  | CS.ServerEndpoint -> s.server

let protected_channel_ready (s:tls_system_state) : prop =
  match s.channel with
  | TlsQuiet -> True
  | TlsInFlight recipient raw snapshot sent ->
    let recip = recipient_state s recipient in
    let synth_sender : CS.connection_state =
      { recip with CS.cs_model = snapshot } in
    ( M.TlsHandshake? sent /\
      PC.pre_appdata_control snapshot.CS.model_control /\
      PC.pre_appdata_control recip.CS.cs_model.CS.model_control /\
      snapshot.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
      recip.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake )
    ==>
    ( CS.sent_single_protected_message_seal snapshot sent raw /\
      snapshot.CS.model_record.CS.record_write.R.seq ==
        recip.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
      (match recipient with
       | CS.ClientEndpoint ->
         CS.peer_record_material_agrees
           (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) recip synth_sender
       | CS.ServerEndpoint ->
         CS.peer_record_material_agrees
           (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) synth_sender recip) /\
      (let (ct, frag) = W.serialize_tls_message sent in
       W.parse_tls_message ct frag == Some sent) )


(** ─────────────────────────────────────────────────────────────────────────
    STAGE 1 — the forward LENGTH invariant.

    PHASE-1 clean16 removal: the length predicates client_len_ok / server_len_ok
    / client_appdata_len_ok were pure counting artifacts (event-log length pinned
    to the structural progress count / the 16-floor appdata bound).  They are
    dropped from tls_system_inv; their sole consumer was the clean16 length==16
    boundary now routed through the tracked Phase-1 gap.  The progress DEFINITIONS
    (PC.client_progress / server_progress) are retained — they are pinned by
    tls_sys_step's *_advances guards and by Temporal.
    ───────────────────────────────────────────────────────────────────────── **)

(** STAGE 2A — key-schedule prefix on each endpoint: an application traffic
    secret implies the master secret, and the master secret implies the shared
    secret.  Used to pin the client's late-obligation rank at send-CF. **)
let client_ksp (s:tls_system_state) : prop = PC.model_ksp s.client.CS.cs_model
let server_ksp (s:tls_system_state) : prop = PC.model_ksp s.server.CS.cs_model

(** STAGE 2B — the client end-to-end invariant, as a system-level conjunct.  This
    is a genuine per-endpoint inductive property (preserved by `lemma_client_step_e2e`).
    Its presence lets the byte machinery discharge the control-based coupling below. **)
let client_e2e (s:tls_system_state) : prop =
  CTy2.client_end_to_end_invariant s.client

(** STAGE 2B (server) — the server end-to-end invariant, guarded by server-config
    validity so it is establishable at the initial state WITHOUT strengthening the
    entry precondition (a server whose config lacks a valid credential can never
    reach application data, so the guard is vacuously discharged there and the
    guard is forced true by `server_state_core_correct` once the server is ready).
    The guard is a property of the IMMUTABLE connection config, hence stable across
    every step. **)
let server_config_valid_e2e (st:CS.connection_state) : prop =
  Some? st.CS.cs_model.CS.model_config.CS.config_server /\
  (match st.CS.cs_model.CS.model_config.CS.config_server with
   | Some cfg ->
     B.length cfg.CS.server_certificate_chain <= Bounds.max_server_certificate_chain_len
   | None -> False)

let server_e2e (s:tls_system_state) : prop =
  server_config_valid_e2e s.server ==> ST.server_end_to_end_invariant s.server

let client_ready (s:tls_system_state) : prop =
  CD.client_driver_application_ready s.client

let server_ready (s:tls_system_state) : prop =
  SD.server_driver_application_ready s.server

(** FACT 4 — protected event-projection witnesses once BOTH endpoints are ready
    (at ControlApplicationData with application record keys installed).  This is
    the Phase-4 redefinition: it is established at the server-verify instant and
    preserved across all six transitions, so `tls_system_inv s` implies it.

    Marked `opaque_to_smt` so that unfolding `tls_system_inv` does not drag the
    inner existential (`P.paired_…pair_witnesses`) into every VC that merely
    carries the invariant as a hypothesis; the few lemmas that actually reason
    about it `reveal_opaque` it explicitly. **)
[@@ "opaque_to_smt"]
let protected_witnesses_ok (s:tls_system_state) : prop =
  (client_ready s /\ server_ready s) ==>
    P.paired_protected_handshake_event_projection_pair_witnesses s.client s.server

(** STAGE 1B — application-data tail length bound (client_appdata_len_ok) REMOVED
    (Phase-1 clean16 removal): pure counting artifact, dropped from tls_system_inv. **)

(** Client control at application data (weaker than `client_ready`). **)
let client_at_appdata (s:tls_system_state) : prop =
  ctrl s.client == CS.ControlApplicationData

(** Server control at or after receipt of the client's Finished. **)
let server_post_cf (s:tls_system_state) : prop =
  match ctrl s.server with
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData
  | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> True
  | _ -> False

let client_clean (s:tls_system_state) : prop =
  (client_ready s /\ TlsQuiet? s.channel ==> server_post_cf s)

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 3a — the incremental per-message replay witnesses.

    Two coupled conjuncts.  (1) `inflight_protected_sender_ok` is the SENDER-side
    BRIDGE: for the single in-flight PROTECTED handshake record it records that
    the sender's frozen snapshot is at a handshake write epoch and pre-application
    data, and that the sending endpoint has actually STORED that message in its
    handshake state.  It is established at the (≤2) protected sends and vacuous at
    every other transition (post-state channel is quiet).  (2)
    `incremental_protected_witnesses` carries, PER protected handshake message, a
    frozen `protected_handshake_event_projection_pair` witness keyed on the
    RECEIVER's stored copy (with the sender's copy baked in via `Some _, None ->
    False`, which encodes the causal coupling used to transport the clause across
    the sender's fresh-store step).  Each clause becomes newly true exactly at
    that message's protected DELIVERY.
    ───────────────────────────────────────────────────────────────────────── **)

(** The system endpoint OPPOSITE the in-flight recipient (i.e. the sender). **)
let ipso_sender_endpoint (s:tls_system_state) (recipient:CS.endpoint_role)
  : CS.connection_state =
  match recipient with
  | CS.ClientEndpoint -> s.server
  | CS.ServerEndpoint -> s.client

let inflight_protected_sender_ok (s:tls_system_state) : prop =
  match s.channel with
  | TlsQuiet -> True
  | TlsInFlight recipient raw snapshot sent ->
    (match sent with
     | M.TlsHandshake (M.EncryptedExtensions ee) ->
         PC.pre_appdata_control snapshot.CS.model_control /\
         snapshot.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         (hsf (ipso_sender_endpoint s recipient)).CS.hs_encrypted_extensions == Some ee
     | M.TlsHandshake (M.Certificate c) ->
         PC.pre_appdata_control snapshot.CS.model_control /\
         snapshot.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         (hsf (ipso_sender_endpoint s recipient)).CS.hs_certificate == Some c
     | M.TlsHandshake (M.CertificateVerify cv) ->
         PC.pre_appdata_control snapshot.CS.model_control /\
         snapshot.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         (hsf (ipso_sender_endpoint s recipient)).CS.hs_certificate_verify == Some cv
     | M.TlsHandshake (M.Finished f) ->
         PC.pre_appdata_control snapshot.CS.model_control /\
         snapshot.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
         (match recipient with
          | CS.ClientEndpoint -> (hsf s.server).CS.hs_server_finished == Some f
          | CS.ServerEndpoint -> (hsf s.client).CS.hs_client_finished == Some f)
     | _ -> True)

[@@ "opaque_to_smt"]
let incremental_protected_witnesses (s:tls_system_state) : prop =
  (* server EncryptedExtensions : sender = server, receiver = client *)
  (match (hsf s.client).CS.hs_encrypted_extensions,
         (hsf s.server).CS.hs_encrypted_extensions with
   | Some client_ee, Some server_ee ->
       (exists (r:PWB.protected_message_replay).
          PWB.protected_handshake_event_projection_pair r
            (M.EncryptedExtensions server_ee) (M.EncryptedExtensions client_ee))
   | Some _, None -> False
   | None, _ -> True) /\
  (* server Certificate : sender = server, receiver = client *)
  (match (hsf s.client).CS.hs_certificate,
         (hsf s.server).CS.hs_certificate with
   | Some client_cert, Some server_cert ->
       (exists (r:PWB.protected_message_replay).
          PWB.protected_handshake_event_projection_pair r
            (M.Certificate server_cert) (M.Certificate client_cert))
   | Some _, None -> False
   | None, _ -> True) /\
  (* server CertificateVerify : sender = server, receiver = client *)
  (match (hsf s.client).CS.hs_certificate_verify,
         (hsf s.server).CS.hs_certificate_verify with
   | Some client_cv, Some server_cv ->
       (exists (r:PWB.protected_message_replay).
          PWB.protected_handshake_event_projection_pair r
            (M.CertificateVerify server_cv) (M.CertificateVerify client_cv))
   | Some _, None -> False
   | None, _ -> True) /\
  (* server Finished : sender = server, receiver = client *)
  (match (hsf s.client).CS.hs_server_finished,
         (hsf s.server).CS.hs_server_finished with
   | Some client_sf, Some server_sf ->
       (exists (r:PWB.protected_message_replay).
          PWB.protected_handshake_event_projection_pair r
            (M.Finished server_sf) (M.Finished client_sf))
   | Some _, None -> False
   | None, _ -> True) /\
  (* client Finished : sender = CLIENT, receiver = SERVER (polarity mirrored) *)
  (match (hsf s.server).CS.hs_client_finished,
         (hsf s.client).CS.hs_client_finished with
   | Some server_cf, Some client_cf ->
       (exists (r:PWB.protected_message_replay).
          PWB.protected_handshake_event_projection_pair r
            (M.Finished client_cf) (M.Finished server_cf))
   | Some _, None -> False
   | None, _ -> True)

(** STAGE 3a (wire faithfulness) — the SINGLE in-flight record's raw is the SEAL
    of the channel-label message `sent` under the SENDER's frozen snapshot write
    keys.  UNGUARDED (needed to break the guard-circularity in
    protected_channel_ready at a delivery).  Carries FAITHFULNESS ONLY, NOT
    material agreement (that stays guarded in protected_channel_ready).  For a
    cleartext hello `sent` the seal projection is True (network_message_is_cleartext),
    so this conjunct is a no-op there.  Frozen while in-flight => inductive:
    established at each SEND from the transition's seal projection, vacuous at
    deliveries (post channel TlsQuiet) and locals (channel frozen). **)
let inflight_wire_faithful (s:tls_system_state) : prop =
  match s.channel with
  | TlsQuiet -> True
  | TlsInFlight recipient raw snapshot sent ->
    CS.sent_event_nonempty_seal_projection snapshot (CS.sent_tls_event sent) raw /\
    (CS.network_message_is_cleartext CL.Sent sent ==>
       CS.cleartext_tls_message_raw sent raw)

(** STAGE 3a (sender coupling) — the ghost in-flight `(snapshot, sent)` is COUPLED
    to the real sender: stepping the sender's frozen snapshot by the send event of
    `sent` reproduces the SENDER endpoint's post-send model.  The sender is the
    endpoint OPPOSITE the recipient.  This is the structural fact that lets a
    delivery derive `M.TlsHandshake? sent` (the guard of protected_channel_ready)
    from the real sender's stored handshake state.  Established at each SEND from
    the transition's `legal_connection_delta` (its `step_model` conjunct), vacuous
    at deliveries (post channel TlsQuiet) and locals (channel frozen while quiet).

    Marked `opaque_to_smt` so that unfolding `tls_system_inv` in unrelated lemmas
    does NOT drag the recursive `CS.step_model` term into every VC that merely
    carries the invariant as a hypothesis; the few lemmas that reason about it
    `reveal_opaque` it explicitly. **)
[@@ "opaque_to_smt"]
let inflight_sender_coupling (s:tls_system_state) : prop =
  match s.channel with
  | TlsQuiet -> True
  | TlsInFlight recipient raw snapshot sent ->
    CS.step_model snapshot (CS.sent_tls_event sent)
      == Some (ipso_sender_endpoint s recipient).CS.cs_model

(** The inductive structural invariant. **)
let tls_system_inv (s:tls_system_state) : prop =
  client_stage_ok s.client /\
  server_stage_ok s.server /\
  CS.connection_state_consistent s.client /\
  CS.connection_state_consistent s.server /\
  WFL.supported_client_config_wire_profile s.client.CS.cs_model.CS.model_config /\
  WStep.hellos_shape s.client.CS.cs_model /\
  WStep.hellos_shape s.server.CS.cs_model /\
  s.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  s.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  client_start_ok s /\
  hello_coupling s /\
  ch_wire_equiv s /\
  sh_wire_equiv s /\
  hello_key_shares_ok s /\
  client_byte_reachable s /\
  server_byte_reachable s /\
  byte_pairing s /\
  channel_consistent s /\
  tls_no_rekeying s /\
  // PHASE-1 clean16 removal: client_len_ok / client_appdata_len_ok / server_len_ok
  // dropped from the invariant.  They were pure counting artifacts (event-log
  // length == structural progress count) whose only role was to feed the clean16
  // length==16 boundary consumed by lemma_pw_establish; that consumption is now
  // routed through the tracked Phase-1 gap and will be discharged by the
  // counting-free C3 witnesses in Phase 2.  The progress DEFINITIONS remain
  // (pinned by tls_sys_step's *_advances guards and Temporal).
  client_ksp s /\
  server_ksp s /\
  client_e2e s /\
  server_e2e s /\
  client_clean s /\
  protected_witnesses_ok s /\
  PC.client_micro_shape s.client.CS.cs_model /\
  PC.server_micro_shape s.server.CS.cs_model /\
  SCB.seq_count_ok_pair s.client s.server /\
  protected_channel_ready s /\
  inflight_wire_faithful s /\
  inflight_sender_coupling s /\
  inflight_protected_sender_ok s /\
  incremental_protected_witnesses s

(** ─────────────────────────────────────────────────────────────────────────
    The six transition shapes.  Each advances exactly one endpoint by exactly one
    step of the official canonical relation, VERBATIM (no wrapper, no pin).  Sends
    require a quiet channel and emit a single record; a LocalEvent that emits a
    record is a "send", one that emits nothing is a "local".  Deliveries consume
    the matching in-flight raw and return the channel to quiet.  The shapes do NOT
    restrict rekeying: a raw canonical step is taken VERBATIM (the no-rekeying
    discipline is folded into the flagship theorem's antecedent and re-established
    on reachable states via the combined invariant below, not pinned per-step).
    ───────────────────────────────────────────────────────────────────────── **)

(** TODO (strict-progress / pure-canonical `tls_sys_step`).  The four
    `*_advances` and two `*_local_advances` side conditions below are the LAST
    residue keeping `tls_sys_step` from being the LITERAL canonical product
    (`client_step`/`server_step` + channel plumbing only).  We investigated
    folding them into the flagship theorem's antecedent (the way the no-rekeying
    guard was folded) and found it UNSOUND without new machinery: both guards
    encode a strict-progress lower bound ("each pre-application-data step raises
    progress by exactly one") that the codebase only ever POSTULATES via these
    guards — `TLS13.System.ProgressCount` proves only the `<= +1` UPPER bound.
    Two distinct stutters block the fold:
      * the send/deliver `*_advances` guards also exclude a stray
        `TlsChangeCipherSpec` at `ControlHandshaking`, whose no-progress step
        combines with the `ControlFailed` progress-collapse to break backward
        monotonicity of any progress-based state predicate; and
      * the local `*_local_advances` guards additionally exclude a redundant
        idempotent key re-install, whose "stutter" status is STATE-dependent (it
        depends on whether the target cache slot was already `Some`) and hence is
        NOT a log-syntactic predicate — so no clean fold exists.
    These guards exclude ONLY degenerate stutters that an honest implementation
    never performs, so keeping them here does not affect the honest run
    (non-vacuity) nor the Pulse-refinement/reachability argument.  Future work to
    make `tls_sys_step` the pure canonical product is EITHER (a) prove the
    intrinsic strict-progress theorem (a rank lower-bound over all `step_model`
    transitions, comparable in size to the existing rank/inversion stack), OR
    (b) move these guards into the OFFICIAL transition functions
    (`client_step`/`server_step`) so `tls_sys_step` inherits them for free.

    The strict-progress SIDE CONDITION (STAGE 1).  A pre-application-data
    transition must strictly raise the acting endpoint's progress count; once the
    endpoint has left the pre-application-data region (application data / close)
    the condition is vacuously satisfied.  This forbids exactly the two model
    no-op self-loops (a redundant idempotent key re-install and a stray
    ChangeCipherSpec record), both of which keep the control state — hence the
    progress count — fixed inside the handshake.  The canonical step relations
    `client_step`/`server_step` are still invoked VERBATIM; this is only an extra
    conjunct restricting which of their steps the SYSTEM takes.  Every honest
    canonical handshake event advances progress by exactly one, so the honest run
    to a ready state is untouched (non-vacuous). **)
let client_advances (before after:CS.connection_state) : prop =
  PC.client_progress after.CS.cs_model > PC.client_progress before.CS.cs_model \/
  ~(PC.pre_appdata_control after.CS.cs_model.CS.model_control)

let server_advances (before after:CS.connection_state) : prop =
  PC.server_progress after.CS.cs_model > PC.server_progress before.CS.cs_model \/
  ~(PC.pre_appdata_control after.CS.cs_model.CS.model_control)

(** The STRICTER side condition for the two internal, no-wire-output LOCAL
    transitions.  A local step must EITHER strictly raise the acting endpoint's
    progress count OR change its control state.  Unlike the send/deliver guards,
    this rules out ALSO the internal application-data self-loop
    (`LocalDeliverApplicationData` at `ControlApplicationData`: control unchanged
    AND progress not increasing).  Every honest handshake LOCAL event either
    advances progress (pre-application-data handshake locals) or changes control,
    so the honest run to a ready+quiescent state is untouched — NON-VACUITY: the
    honest run performs only progress-increasing handshake locals and
    control-changing steps and never an internal app-read before it is ready.
    TODO: see the strict-progress note above `client_advances` — these two guards
    are not soundly foldable into a state predicate (the redundant-install stutter
    is state-dependent, not log-syntactic); revisit via the strict-progress
    theorem or by moving them into the official `client_step`/`server_step`. **)
let client_local_advances (before after:CS.connection_state) : prop =
  PC.client_progress after.CS.cs_model > PC.client_progress before.CS.cs_model \/
  ~(after.CS.cs_model.CS.model_control == before.CS.cs_model.CS.model_control)

let server_local_advances (before after:CS.connection_state) : prop =
  PC.server_progress after.CS.cs_model > PC.server_progress before.CS.cs_model \/
  ~(after.CS.cs_model.CS.model_control == before.CS.cs_model.CS.model_control)

let tls_step_client_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.client_local_event) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
          (sent:M.tls_message).
     CCP.client_step a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [w] /\
     client_advances a.client c' /\
     c'.CS.cs_event_log == a.client.CS.cs_event_log @ [CS.sent_tls_event sent] /\
     b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent })

let tls_step_server_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.server_local_event) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
          (sent:M.tls_message).
     SCP.server_step a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [w] /\
     server_advances a.server s' /\
     s'.CS.cs_event_log == a.server.CS.cs_event_log @ [CS.sent_tls_event sent] /\
     b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent })

let tls_step_deliver_to_server (a b:tls_system_state) : prop =
  (exists (wire:CW.wire_message) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
          (snap:CS.connection_model) (sent:M.tls_message).
     a.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
     Seq.equal (CW.wire_serialize wire) raw /\
     SCP.server_step a.server (SM.WireEvent wire) s' out /\
     server_advances a.server s' /\
     b == { a with server = s'; channel = TlsQuiet })

let tls_step_deliver_to_client (a b:tls_system_state) : prop =
  (exists (wire:CW.wire_message) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
          (snap:CS.connection_model) (sent:M.tls_message).
     a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
     Seq.equal (CW.wire_serialize wire) raw /\
     CCP.client_step a.client (SM.WireEvent wire) c' out /\
     client_advances a.client c' /\
     b == { a with client = c'; channel = TlsQuiet })

let tls_step_client_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.client_local_event) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output).
     CCP.client_step a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [] /\
     client_local_advances a.client c' /\
     b == { a with client = c' })

let tls_step_server_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.server_local_event) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output).
     SCP.server_step a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [] /\
     server_local_advances a.server s' /\
     b == { a with server = s' })

(** A single honest system transition. **)
let tls_sys_step (a b:tls_system_state) : prop =
  tls_step_client_send a b \/
  tls_step_server_send a b \/
  tls_step_deliver_to_client a b \/
  tls_step_deliver_to_server a b \/
  tls_step_client_local a b \/
  tls_step_server_local a b

(** Reflexive step used by the temporal layer. **)
let tls_sys_step_stutter (a b:tls_system_state) : prop = tls_sys_step a b \/ a == b

(** ─────────────────────────────────────────────────────────────────────────
    Inductiveness.
    ───────────────────────────────────────────────────────────────────────── **)

(** An official client step preserves consistency and the (client) config. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_step_pres
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CS.connection_state_consistent st0 /\ CCP.client_step st0 e st1 out)
      (ensures
        CS.connection_state_consistent st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      CS.connection_state_consistent st1 /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _pf.
      (CSL.lemma_legal_connection_delta_consistent st0 d st1;
       CSL.lemma_step_model_preserves_config st0.CS.cs_model d.CS.delta_event st1.CS.cs_model)
#pop-options

(** An official server step preserves consistency and the config. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_server_step_pres
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CS.connection_state_consistent st0 /\ SCP.server_step st0 e st1 out)
      (ensures
        CS.connection_state_consistent st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      CS.connection_state_consistent st1 /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _pf.
      (CSL.lemma_legal_connection_delta_consistent st0 d st1;
       CSL.lemma_step_model_preserves_config st0.CS.cs_model d.CS.delta_event st1.CS.cs_model)
#pop-options


(** A single legal model step preserves the client's start/config agreement.
    The only step installing `hs_start` is `LocalStartHandshake`, whose legality
    (`legal_local_event`) supplies `start_matches_config config start`; config is
    preserved by every step, and every other step leaves `hs_start` unchanged. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_step_client_start
  (m0:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m0 ev /\ CS.step_model m0 ev == Some m1 /\ start_ok_model m0)
      (ensures start_ok_model m1)
  = CSL.lemma_step_model_preserves_config m0 ev m1
#pop-options

(** A client step preserves the hello shape, hello-field values, config and the
    client's start/config agreement. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_step_shape
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        CCP.client_step st0 e st1 out /\
        WStep.hellos_shape st0.CS.cs_model /\
        start_ok_model st0.CS.cs_model)
      (ensures
        WStep.hellos_shape st1.CS.cs_model /\
        WStep.hs_hellos_stable st0.CS.cs_model st1.CS.cs_model /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
        start_ok_model st1.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      WStep.hellos_shape st1.CS.cs_model /\
      WStep.hs_hellos_stable st0.CS.cs_model st1.CS.cs_model /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config /\
      start_ok_model st1.CS.cs_model
    with _pf.
      (WStep.lemma_step_model_preserves_hellos st0.CS.cs_model d.CS.delta_event st1.CS.cs_model;
       CSL.lemma_step_model_preserves_config st0.CS.cs_model d.CS.delta_event st1.CS.cs_model;
       lemma_step_client_start st0.CS.cs_model d.CS.delta_event st1.CS.cs_model)
#pop-options

(** A server step preserves the hello shape, hello-field values and config. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_server_step_shape
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step st0 e st1 out /\
        WStep.hellos_shape st0.CS.cs_model)
      (ensures
        WStep.hellos_shape st1.CS.cs_model /\
        WStep.hs_hellos_stable st0.CS.cs_model st1.CS.cs_model /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      WStep.hellos_shape st1.CS.cs_model /\
      WStep.hs_hellos_stable st0.CS.cs_model st1.CS.cs_model /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _pf.
      (WStep.lemma_step_model_preserves_hellos st0.CS.cs_model d.CS.delta_event st1.CS.cs_model;
       CSL.lemma_step_model_preserves_config st0.CS.cs_model d.CS.delta_event st1.CS.cs_model)
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 1 — per-step length + micro-shape preservation.

    A client step advancing progress (the strict-progress guard) by at most one
    (the progress-bound lemma) keeps the event-log length pinned to the progress
    count throughout the pre-application-data region, and preserves the
    region-entry shape fact.  The server analogue is symmetric.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80 --split_queries always"
let lemma_client_step_len_micro
  (a c':CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        CCP.client_step a e c' out /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        client_advances a c' /\
        PC.client_micro_shape a.CS.cs_model)
      (ensures
        PC.client_micro_shape c'.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d c');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d c'
    returns
      PC.client_micro_shape c'.CS.cs_model
    with _pf.
      PC.lemma_client_micro_shape_step a.CS.cs_model d.CS.delta_event c'.CS.cs_model
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80 --split_queries always"
#restart-solver
let lemma_server_step_len_micro
  (a s':CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step a e s' out /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_advances a s' /\
        PC.server_micro_shape a.CS.cs_model)
      (ensures
        PC.server_micro_shape s'.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d s');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d s'
    returns
      PC.server_micro_shape s'.CS.cs_model
    with _pf.
      PC.lemma_server_micro_shape_step a.CS.cs_model d.CS.delta_event s'.CS.cs_model
#pop-options

(** STAGE 2A — `model_ksp` preservation for a client / server step. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_step_ksp
  (a c':CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CCP.client_step a e c' out /\ PC.model_ksp a.CS.cs_model)
      (ensures PC.model_ksp c'.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d c');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d c'
    returns PC.model_ksp c'.CS.cs_model
    with _pf.
      PC.lemma_ksp_step a.CS.cs_model d.CS.delta_event c'.CS.cs_model
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_server_step_ksp
  (a s':CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires SCP.server_step a e s' out /\ PC.model_ksp a.CS.cs_model)
      (ensures PC.model_ksp s'.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d s');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d s'
    returns PC.model_ksp s'.CS.cs_model
    with _pf.
      PC.lemma_ksp_step a.CS.cs_model d.CS.delta_event s'.CS.cs_model
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Hello-field NON-INSTALL lemmas for LOCAL steps.

    `hs_hellos_stable` only gives *monotone* preservation (`Some x` stays `Some
    x`); for a LOCAL step we additionally need `None` to stay `None` on the field
    the coupling does NOT protect (the client's ServerHello, the server's
    ClientHello).  The model-level facts below observe that `hs_server_hello` is
    installed ONLY by a ServerHello handshake message, and `hs_client_hello` ONLY
    by a ClientHello message (the `LocalSelectServerParameters` re-assignment is a
    legality-forced no-op).  A LOCAL event carries neither message on the relevant
    endpoint, so the field is unchanged. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_step_preserves_server_hello
  (m0:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        CS.step_model m0 ev == Some m1 /\
        (forall (dir:CS.direction) (sh:GSH.serverHello).
           ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh) })))
      (ensures
        m1.CS.model_handshake.CS.hs_server_hello ==
        m0.CS.model_handshake.CS.hs_server_hello)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_step_preserves_client_hello_legal
  (m0:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m0 ev /\
        CS.step_model m0 ev == Some m1 /\
        (forall (dir:CS.direction) (ch:GCH.clientHello).
           ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                     CL.message_value = M.TlsHandshake (M.ClientHello ch) })))
      (ensures
        m1.CS.model_handshake.CS.hs_client_hello ==
        m0.CS.model_handshake.CS.hs_client_hello)
  = ()
#pop-options

(** A client LOCAL step leaves `hs_server_hello` unchanged: unpacking
    `client_step`'s LocalEvent branch, the underlying `conn_ev` is one of the
    client-originated events (send CH/Finished/appdata/alert/keyupdate, or a
    ConnLocalEvent) — never a ServerHello — so the model lemma applies. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_client_local_preserves_server_hello
  (st0 st1:CS.connection_state)
  (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CCP.client_step st0 (SM.LocalEvent local) st1 out)
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello)
  = let api = CTy.client_local_event_api local in
    eliminate exists conn_ev raw_sent.
      CCP.client_api_event_matches st0 api conn_ev /\
      CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta st0
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } st1 /\
      CS.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
      CS.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty
    returns
      st1.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello
    with _pf.
      (assert (forall (dir:CS.direction) (sh:GSH.serverHello).
         conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh) }));
       lemma_step_preserves_server_hello st0.CS.cs_model conn_ev st1.CS.cs_model)
#pop-options

(** A server LOCAL step leaves `hs_client_hello` unchanged: the underlying
    `conn_ev` is a server-originated event (send SH/EE/Cert/CV/SF/appdata/alert,
    or a ConnLocalEvent) — never a ClientHello — so the (legal) model lemma
    applies. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_server_local_preserves_client_hello
  (st0 st1:CS.connection_state)
  (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires SCP.server_step st0 (SM.LocalEvent local) st1 out)
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello)
  = let api = CTy.server_local_event_api local in
    eliminate exists conn_ev raw_sent.
      SCP.server_api_event_matches api conn_ev /\
      SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta st0
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } st1 /\
      CS.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
      CS.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty
    returns
      st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello
    with _pf.
      (assert (forall (dir:CS.direction) (ch:GCH.clientHello).
         conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                     CL.message_value = M.TlsHandshake (M.ClientHello ch) }));
       lemma_step_preserves_client_hello_legal st0.CS.cs_model conn_ev st1.CS.cs_model)
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    INITIAL STATE.  Both endpoints start at record epoch Initial, seq 0, with
    empty wire logs (appdata count 0), so `seq_count_ok` holds.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_seq_count_ok_initial (cfg_c cfg_s:CS.connection_config)
  : Lemma (SCB.seq_count_ok_pair (initial_tls_system cfg_c cfg_s).client (initial_tls_system cfg_c cfg_s).server)
  = WStep.lemma_raw_appdata_count_empty ()
#pop-options

let lemma_initial_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c)
      (ensures tls_system_inv (initial_tls_system cfg_c cfg_s))
  = lemma_seq_count_ok_initial cfg_c cfg_s;
    assert (CS.connection_state_evolves (CS.initial cfg_c) (CS.initial cfg_c));
    assert (CS.connection_state_evolves (CS.initial cfg_s) (CS.initial cfg_s));
    assert (WStep.hellos_shape (CS.initial cfg_c).CS.cs_model);
    assert (WStep.hellos_shape (CS.initial cfg_s).CS.cs_model);
    WStep.lemma_client_reachable_initial cfg_c;
    WStep.lemma_server_reachable_initial cfg_s;
    CTy2.lemma_initial_client_end_to_end_invariant cfg_c;
    // server_e2e: guarded by config validity; establish e2e when the guard holds.
    (if server_config_valid_e2e (CS.initial cfg_s)
     then ST.lemma_initial_server_end_to_end_invariant cfg_s
     else ());
    // protected_witnesses_ok is vacuous at the initial state (client not ready).
    reveal_opaque (`%protected_witnesses_ok)
      (protected_witnesses_ok (initial_tls_system cfg_c cfg_s));
    assert (~(client_ready (initial_tls_system cfg_c cfg_s)));
    assert (TlsQuiet? (initial_tls_system cfg_c cfg_s).channel);
    // Stage 3a: bridge is vacuous (quiet channel); witnesses are vacuous (all
    // handshake fields None at the initial state).
    reveal_opaque (`%inflight_sender_coupling)
      (inflight_sender_coupling (initial_tls_system cfg_c cfg_s));
    reveal_opaque (`%incremental_protected_witnesses)
      (incremental_protected_witnesses (initial_tls_system cfg_c cfg_s))

(** ─────────────────────────────────────────────────────────────────────────
    Wire / projection FACT preservation.

    The five wire/projection FACTS (ch_wire_equiv = FACT 1, sh_wire_equiv =
    FACT 2, hello_key_shares_ok = FACT 3, protected_witnesses_ok = FACT 4,
    channel_consistent = FACT 5) are preserved across each transition.  For the
    SEND and DELIVER transitions establishing them requires ConnectionState-level
    *step inversion* — handshake-field stability across a step, the
    cleartext/received raw facts carried by `event_raw_delta_legal`, the
    config→profile derivation (`start_matches_config`) at CH-send, and the
    SH-parse roundtrip at SH-deliver — none of which is exposed by the existing
    `.fsti` interfaces.  For the LOCAL and DELIVER transitions channel_consistent
    is discharged directly below (the channel is quiet in the post-state), so the
    admitted helpers cover only the four handshake-field FACTS there.

    Each helper is stated over the *shape* predicate so it can be reused, and is
    named for exactly the obligation it discharges.  See the Stage-B report for
    the concrete discharge path of every one.
    ───────────────────────────────────────────────────────────────────────── **)

(** channel_consistent at a client SEND.  The in-flight raw is the emitted record.
    If the client sent its CH the raw is a cleartext CH and the (just-installed)
    `hs_client_hello` supplies the consequent (profile via
    `lemma_ch_profile_from_start_config`); otherwise the raw is a PROTECTED
    ApplicationData record, whose `parse_record_wire` is ApplicationData-typed, so
    the "received cleartext ClientHello" antecedent (which forces a Handshake
    record) is FALSE and the clause is vacuous. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_cc_client_send
  (a:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\ TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        channel_consistent
          ({ a with client = c';
                    channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent }))
  = let b = { a with client = c';
                     channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent } in
    lemma_serialize_all_single w;
    let api = CTy.client_local_event_api local in
    eliminate exists conn_ev raw_sent.
      CCP.client_api_event_matches a.client api conn_ev /\
      CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta a.client
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } c' /\
      CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
      CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty
    returns channel_consistent b
    with _pf. (
      Seq.lemma_eq_elim (emitted_raw out) raw_sent;
      let raw = emitted_raw out in
      introduce
        (exists server_ch.
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw)
        ==>
        (match c'.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
         | Some client_ch ->
           WFL.supported_client_hello_wire_profile client_ch /\
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw
         | None -> False)
      with _pa. (
        match conn_ev with
        | CS.ConnLocalEvent _ ->
          // raw is empty; the antecedent's parse would need consumed 0 > 0 — impossible.
          eliminate exists server_ch.
            CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw
          returns _
          with _pw.
            (eliminate exists fragment.
               W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
               W.parse_tls_message T.Handshake fragment ==
                 Some (M.TlsHandshake (M.ClientHello server_ch))
             returns _
             with _pf2.
               W.lemma_parse_record_wire_some_consumed_positive raw T.Handshake fragment (B.length raw))
        | CS.ConnNetworkEvent nmsg ->
          (match nmsg.CL.message_value with
           | M.TlsHandshake (M.ClientHello ch) ->
             // CH case: prove the consequent directly.
             assert (c'.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch);
             assert (CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) raw_sent);
             (match a.client.CS.cs_model.CS.model_handshake.CS.hs_start with
              | Some start ->
                WStep.lemma_ch_profile_from_start_config
                  a.client.CS.cs_model.CS.model_config start ch
              | None -> ())
           | _ ->
             // protected case: the raw is an ApplicationData record, not a CH.
             assert (nmsg.CL.message_direction == CL.Sent);
             assert (CS.network_message_is_cleartext CL.Sent nmsg.CL.message_value == false);
             CSL.lemma_legal_connection_delta_protected_parse_prefix a.client
               { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
                 CS.delta_raw_received = B.empty } c';
             W.lemma_parse_record_implies_parse_record_wire raw_sent;
             eliminate exists server_ch.
               CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw
             returns _
             with _pw.
               (eliminate exists fragment.
                  W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
                  W.parse_tls_message T.Handshake fragment ==
                    Some (M.TlsHandshake (M.ClientHello server_ch))
                returns _
                with _pf3. ()))))
#pop-options

(** FACTS 1–5 across a client SEND (client emits one record; needs field
    stability + config→profile at CH-send + carried cleartext for the channel). **)
val lemma_wire_facts_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   channel_consistent b /\ hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_wire_facts_client_send a b =
  eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                   (sent:M.tls_message).
    CCP.client_step a.client (SM.LocalEvent local) c' out /\
    out.SM.so_wire_outputs == [w] /\
    b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
          channel_consistent b /\ hello_coupling b
  with _pf. (
    lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
    lemma_client_local_preserves_server_hello a.client c' local out;
    lemma_cc_client_send a local c' out w sent;
    assert (c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
            a.client.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    assert (ch_wire_equiv b);
    assert (sh_wire_equiv b);
    assert (hello_key_shares_ok b);
    assert (hello_coupling b))
#pop-options

(** channel_consistent at a server SEND.  Symmetric to `lemma_cc_client_send`:
    a ServerHello send makes the raw a cleartext SH pinned by the (just-installed)
    `hs_server_hello`; every other server send is PROTECTED (the server never sends
    a cleartext CCS in this model), so the raw is an ApplicationData record and the
    "received cleartext ServerHello" antecedent (a Handshake record) is FALSE. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_cc_server_send
  (a:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\ TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        channel_consistent
          ({ a with server = s';
                    channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent }))
  = let b = { a with server = s';
                     channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent } in
    lemma_serialize_all_single w;
    let api = CTy.server_local_event_api local in
    eliminate exists conn_ev raw_sent.
      SCP.server_api_event_matches api conn_ev /\
      SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta a.server
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } s' /\
      CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
      CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty
    returns channel_consistent b
    with _pf. (
      Seq.lemma_eq_elim (emitted_raw out) raw_sent;
      let raw = emitted_raw out in
      introduce
        (exists frag server_sh.
           W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw) /\
           W.parse_tls_message T.Handshake frag ==
             Some (M.TlsHandshake (M.ServerHello server_sh)))
        ==>
        (match s'.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some server_sh ->
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw
         | None -> False)
      with _pa. (
        match conn_ev with
        | CS.ConnLocalEvent _ ->
          eliminate exists frag server_sh.
            W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw) /\
            W.parse_tls_message T.Handshake frag ==
              Some (M.TlsHandshake (M.ServerHello server_sh))
          returns _
          with _pw.
            W.lemma_parse_record_wire_some_consumed_positive raw T.Handshake frag (B.length raw)
        | CS.ConnNetworkEvent nmsg ->
          (match nmsg.CL.message_value with
           | M.TlsHandshake (M.ServerHello sh) ->
             assert (s'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh);
             assert (CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello sh)) raw_sent)
           | _ ->
             assert (nmsg.CL.message_direction == CL.Sent);
             assert (CS.network_message_is_cleartext CL.Sent nmsg.CL.message_value == false);
             CSL.lemma_legal_connection_delta_protected_parse_prefix a.server
               { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
                 CS.delta_raw_received = B.empty } s';
             W.lemma_parse_record_implies_parse_record_wire raw_sent;
             eliminate exists frag server_sh.
               W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw) /\
               W.parse_tls_message T.Handshake frag ==
                 Some (M.TlsHandshake (M.ServerHello server_sh))
             returns _
             with _pw. ())))
#pop-options

(** FACTS 1–5 across a server SEND (server emits one record; needs field
    stability + carried cleartext for the channel at SH-send). **)
val lemma_wire_facts_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_send a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   channel_consistent b /\ hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_wire_facts_server_send a b =
  eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                   (sent:M.tls_message).
    SCP.server_step a.server (SM.LocalEvent local) s' out /\
    out.SM.so_wire_outputs == [w] /\
    b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
          channel_consistent b /\ hello_coupling b
  with _pf. (
    lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
    lemma_server_local_preserves_client_hello a.server s' local out;
    lemma_cc_server_send a local s' out w sent;
    assert (s'.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
            a.server.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    assert (ch_wire_equiv b);
    assert (sh_wire_equiv b);
    assert (hello_key_shares_ok b);
    assert (hello_coupling b))
#pop-options

(** FACTS 1–4 across a delivery to the server (server receives the in-flight raw;
    needs the CH-received parse + channel_consistent a to establish ch_wire_equiv,
    and field stability elsewhere). channel_consistent b is proven inline. **)
val lemma_wire_facts_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_wire_facts_deliver_to_server a b =
  eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
                   (snap:CS.connection_model) (sent:M.tls_message).
    a.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
    Seq.equal (CW.wire_serialize wire) raw /\
    SCP.server_step a.server (SM.WireEvent wire) s' out /\
    b == { a with server = s'; channel = TlsQuiet }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
  with _pd. (
    lemma_server_step_shape a.server s' (SM.WireEvent wire) out;
    Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
    eliminate exists (msg:M.tls_message).
      (let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
       CS.legal_connection_delta a.server
         { CS.delta_event = conn_ev;
           CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire } s' /\
       CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
    with _ps. (
      assert (WStep.hs_hellos_stable a.server.CS.cs_model s'.CS.cs_model);
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      (match msg with
       | M.TlsHandshake (M.ClientHello server_ch) ->
         // server receives CH: the raw is a received cleartext CH, which fires
         // channel_consistent a to supply the client's stored CH + profile + cleartext.
         assert (CS.received_cleartext_tls_message_raw
                   (M.TlsHandshake (M.ClientHello server_ch)) raw);
         assert (s'.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch);
         assert (channel_consistent a);
         assert (ch_wire_equiv b);
         assert (hello_coupling b)
       | _ ->
         // non-CH receive: hs_client_hello is unchanged, so FACT 1 transfers from a.
         assert (forall (dir:CS.direction) (ch:GCH.clientHello).
           conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch) }));
         lemma_step_preserves_client_hello_legal a.server.CS.cs_model conn_ev s'.CS.cs_model;
         assert (ch_wire_equiv b);
         assert (hello_coupling b));
      assert (sh_wire_equiv b);
      assert (hello_key_shares_ok b)))
#pop-options

(** RECEIVED-ServerHello wire bridge — the SINGLE Stage-A gap besides FACT 4.

    When the client receives its ServerHello over the wire, the in-flight raw must
    (i) pin the server's stored ServerHello — i.e. supply `channel_consistent a`'s
    parse-form antecedent so it fires and yields the server's SH bytes — and
    (ii) prove the received SH's key share pairs with the server's canonical SH
    (`hello_key_shares_ok`, FACT 3).  Both are wire serialize/parse ROUNDTRIP facts
    on the RECEIVED ServerHello body: the received SH carries a verbatim `body`, so
    byte replay alone does not constrain its `key_share` (see the WFL note on
    `paired_cleartext_hello_key_shares`), and turning the client's decoder
    projection into the record parse-form requires the ConnectionState decoder
    bridge (`network_input_message_projection` → `parse_record_wire`).  This is the
    `client_sh` roundtrip flagged in the Stage-A brief and is deferred to Stage B.
    Every OTHER delivery-to-client fact (ch_wire_equiv, and all facts on a non-SH
    receive) is proven with no admit below. **)
val lemma_deliver_to_client_sh_bridge
  (a b:tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  (client_sh:GSH.serverHello)
  (content_type:U8.t) (fragment:B.bytes)
  : Lemma
      (requires
        tls_system_inv a /\
        a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        CCP.client_step a.client (SM.WireEvent wire) c' out /\
        c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        c'.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
          a.client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh)) raw /\
        CTy2.network_input_message_projection a.client content_type fragment
          (M.TlsHandshake (M.ServerHello client_sh)) raw /\
        b == { a with client = c'; channel = TlsQuiet })
      (ensures sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_deliver_to_client_sh_bridge a b wire c' out raw snap sent client_sh content_type fragment =
  assert (channel_consistent a);
  assert (CS.connection_state_consistent a.server);
  // c' (the stepped client) is consistent, so its stored ServerHello satisfies the
  // single-record wire bound (client-receive legality carries it) — supplying the
  // hypothesis the parse-record lemma now needs on the unbounded generated SH type.
  lemma_client_step_pres a.client c' (SM.WireEvent wire) out;
  assert (CS.connection_state_consistent c');
  WStep.lemma_consistent_server_hello_wire_bound c';
  assert (B.length (W.serialize_handshake (M.ServerHello client_sh)) <= 16640);
  // received cleartext for client_sh is a plain cleartext (SH is not HRR).
  assert (CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw);
  WStep.lemma_cleartext_server_hello_parse_record client_sh raw;
  // parse_record_wire raw == Some (Handshake, serialize_handshake (SH client_sh), |raw|)
  // Extract the client decoder projection pieces.
  assert (CTy2.decoder_fragment_relation a.client content_type fragment raw);
  assert (CTy2.wire_parse_success content_type fragment
            (M.TlsHandshake (M.ServerHello client_sh)));
  eliminate exists (outer_ct:T.content_type) (outer_fragment:B.bytes).
    W.parse_record_wire raw == Some (outer_ct, outer_fragment, B.length raw) /\
    (if outer_ct = T.Application_data
     then CTy2.protected_decoder_fragment_relation a.client content_type fragment raw
     else
       TM.content_type_matches content_type outer_ct /\
       Seq.equal fragment outer_fragment)
  returns sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
  with _dfr. (
    // parse_record_wire raw is functional: outer_ct = Handshake,
    // outer_fragment = serialize_handshake (SH client_sh).
    assert (outer_ct == T.Handshake);
    Seq.lemma_eq_elim outer_fragment (W.serialize_handshake (M.ServerHello client_sh));
    assert (TM.content_type_matches content_type T.Handshake);
    Seq.lemma_eq_elim fragment outer_fragment;
    // fragment == serialize_handshake (SH client_sh)
    eliminate exists (ct:T.content_type).
      TM.content_type_matches content_type ct /\
      W.parse_tls_message ct fragment ==
        Some (M.TlsHandshake (M.ServerHello client_sh))
    returns sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
    with _wps. (
      // content_type_matches is functional in ct, so ct == Handshake.
      assert (ct == T.Handshake);
      assert (W.parse_tls_message T.Handshake fragment ==
                Some (M.TlsHandshake (M.ServerHello client_sh)));
      // Fire channel_consistent a's ClientEndpoint branch.
      assert (exists frag server_sh.
        W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw) /\
        W.parse_tls_message T.Handshake frag ==
          Some (M.TlsHandshake (M.ServerHello server_sh)));
      assert (Some? (hsf a.server).CS.hs_server_hello);
      let server_sh : GSH.serverHello = Some?.v (hsf a.server).CS.hs_server_hello in
      assert (CS.cleartext_tls_message_raw
                (M.TlsHandshake (M.ServerHello server_sh)) raw);
      // FACT 2: sh_wire_equiv b (witness raw).
      assert ((hsf b.server).CS.hs_server_hello == Some server_sh);
      assert ((hsf b.client).CS.hs_server_hello == Some client_sh);
      assert (sh_wire_equiv b);
      // hello_coupling b.
      assert (hello_coupling a);
      assert (hello_coupling b);
      // FACT 3: hello_key_shares_ok b — prove the guarded implication.
      introduce
        (Some? (hsf b.client).CS.hs_client_hello /\ Some? (hsf b.server).CS.hs_client_hello /\
         Some? (hsf b.client).CS.hs_server_hello /\ Some? (hsf b.server).CS.hs_server_hello)
        ==>
        WFL.paired_cleartext_hello_key_shares b.client b.server
      with _guard. (
        let client_ch : GCH.clientHello = Some?.v (hsf b.client).CS.hs_client_hello in
        let server_ch : GCH.clientHello = Some?.v (hsf b.server).CS.hs_client_hello in
        // client_ch is a.client's CH (stability), server_ch is a.server's CH.
        assert ((hsf a.client).CS.hs_client_hello == Some client_ch);
        assert ((hsf a.server).CS.hs_client_hello == Some server_ch);
        // (3a) CH raw witness via ch_wire_equiv a (also yields the CH wire profile).
        assert (ch_wire_equiv a);
        eliminate exists (raw':B.bytes).
          CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw' /\
          CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw'
        returns WFL.paired_cleartext_hello_key_shares b.client b.server
        with _che. (
          // (3b) The server's canonical SH is a sent cleartext on the in-flight raw.
          assert (CS.cleartext_tls_message_raw
                    (M.TlsHandshake (M.ServerHello server_sh)) raw);
          // With the injective generated codec, raw replay on BOTH hellos forces
          // record equality (client_ch==server_ch, client_sh==server_sh), so the
          // key-share pairing follows directly.  CH raws coincide (raw'), SH raws
          // coincide (raw).
          WFL.lemma_paired_cleartext_hello_key_shares_from_cleartext_raw_and_supported_server_hello_parse
            b.client b.server
            client_ch server_ch client_sh server_sh
            raw' raw' raw raw;
          assert (WFL.paired_cleartext_hello_key_shares b.client b.server)
        )
      )
    )
  )
#pop-options

(** FACTS 1–4 across a delivery to the client (client receives the in-flight raw;
    the ServerHello case uses the received-SH wire bridge above, every non-SH
    receive is a pure field-stability transfer). channel_consistent b is trivial
    (the post-state channel is quiet). **)
val lemma_wire_facts_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_wire_facts_deliver_to_client a b =
  eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
                   (snap:CS.connection_model) (sent:M.tls_message).
    a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
    Seq.equal (CW.wire_serialize wire) raw /\
    CCP.client_step a.client (SM.WireEvent wire) c' out /\
    b == { a with client = c'; channel = TlsQuiet }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
  with _pd. (
    lemma_client_step_shape a.client c' (SM.WireEvent wire) out;
    Seq.lemma_eq_elim (CW.wire_serialize wire) raw;
    eliminate exists (msg:M.tls_message).
      (let conn_ev = CS.ConnNetworkEvent
          { CL.message_direction = CL.Received; CL.message_value = msg } in
       CS.legal_connection_delta a.client
         { CS.delta_event = conn_ev;
           CS.delta_raw_sent = WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
           CS.delta_raw_received = CW.wire_serialize wire } c' /\
       CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       (exists content_type fragment.
          CTy2.network_input_message_projection a.client content_type fragment msg
            (CW.wire_serialize wire)) /\
       CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
    with _ps. (
      assert (WStep.hs_hellos_stable a.client.CS.cs_model c'.CS.cs_model);
      let conn_ev = CS.ConnNetworkEvent
        { CL.message_direction = CL.Received; CL.message_value = msg } in
      (match msg with
       | M.TlsHandshake (M.ServerHello client_sh) ->
         // ServerHello receive: hs_server_hello is installed; hs_client_hello is
         // unchanged (SH is not a CH), so FACT 1 transfers.  The SH wire bridge
         // supplies FACTS 2/3 and the coupling.
         assert (forall (dir:CS.direction) (ch:GCH.clientHello).
           conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch) }));
         lemma_step_preserves_client_hello_legal a.client.CS.cs_model conn_ev c'.CS.cs_model;
         assert (ch_wire_equiv b);
         assert (CS.received_cleartext_tls_message_raw
                   (M.TlsHandshake (M.ServerHello client_sh)) raw);
         assert (c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh);
         eliminate exists (content_type:U8.t) (fragment:B.bytes).
           CTy2.network_input_message_projection a.client content_type fragment msg
             (CW.wire_serialize wire)
         returns sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
         with _pj. (
           assert (CTy2.network_input_message_projection a.client content_type fragment
                     (M.TlsHandshake (M.ServerHello client_sh)) raw);
           lemma_deliver_to_client_sh_bridge a b wire c' out raw snap sent client_sh content_type fragment
         )
       | M.TlsHandshake (M.ClientHello _) ->
         // A client (role ClientEndpoint) cannot legally RECEIVE a ClientHello.
         assert (a.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
         assert (CS.legal_event a.client.CS.cs_model conn_ev)
       | _ ->
         // non-hello receive: both hello fields unchanged, so FACTS 1–3 + coupling
         // transfer from a.
         assert (forall (dir:CS.direction) (sh:GSH.serverHello).
           conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh) }));
         lemma_step_preserves_server_hello a.client.CS.cs_model conn_ev c'.CS.cs_model;
         assert (forall (dir:CS.direction) (ch:GCH.clientHello).
           conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                       CL.message_value = M.TlsHandshake (M.ClientHello ch) }));
         lemma_step_preserves_client_hello_legal a.client.CS.cs_model conn_ev c'.CS.cs_model;
         assert (ch_wire_equiv b);
         assert (sh_wire_equiv b);
         assert (hello_key_shares_ok b);
         assert (hello_coupling b))))
#pop-options

(** FACTS 1–3 + hello_coupling across a client LOCAL step (no record emitted;
    needs handshake-field stability across the local step). channel_consistent b
    is proven inline (post-state channel is quiet). **)
val lemma_wire_facts_client_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_local a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   hello_coupling b)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_wire_facts_client_local a b =
  eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output).
    CCP.client_step a.client (SM.LocalEvent local) c' out /\
    out.SM.so_wire_outputs == [] /\
    b == { a with client = c' }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
  with _pf. (
    lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
    lemma_client_local_preserves_server_hello a.client c' local out;
    assert (WStep.hs_hellos_stable a.client.CS.cs_model c'.CS.cs_model);
    assert (c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
            a.client.CS.cs_model.CS.model_handshake.CS.hs_server_hello);
    assert (ch_wire_equiv a /\ sh_wire_equiv a /\ hello_key_shares_ok a /\ hello_coupling a);
    assert (ch_wire_equiv b);
    assert (sh_wire_equiv b);
    assert (hello_key_shares_ok b);
    assert (hello_coupling b))
#pop-options

(** FACTS 1–3 + hello_coupling across a server LOCAL step (no record emitted;
    needs handshake-field stability across the local step). channel_consistent b
    is proven inline (post-state channel is quiet). **)
val lemma_wire_facts_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_local a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   hello_coupling b)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_wire_facts_server_local a b =
  eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output).
    SCP.server_step a.server (SM.LocalEvent local) s' out /\
    out.SM.so_wire_outputs == [] /\
    b == { a with server = s' }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b
  with _pf. (
    lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
    lemma_server_local_preserves_client_hello a.server s' local out;
    assert (WStep.hs_hellos_stable a.server.CS.cs_model s'.CS.cs_model);
    assert (s'.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
            a.server.CS.cs_model.CS.model_handshake.CS.hs_client_hello);
    assert (ch_wire_equiv a /\ sh_wire_equiv a /\ hello_key_shares_ok a /\ hello_coupling a);
    assert (ch_wire_equiv b);
    assert (sh_wire_equiv b);
    assert (hello_key_shares_ok b);
    assert (hello_coupling b))
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE B — byte-level invariant preservation.

    FACT 4 (`protected_witnesses_ok`) is no longer maintained inductively; it is
    established on demand at the ready+quiescent state.  The two byte-level
    families it is derived from are preserved here:
      * REACHABILITY of the stepping endpoint (config stable across a step);
      * the channel-aware BYTE PAIRING, using the one-step raw-log deltas.
    ───────────────────────────────────────────────────────────────────────── **)

(** Reachability preservation for a client step (config is stable). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_client_reach_pres
  (a:tls_system_state) (c':CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        client_byte_reachable a /\ CCP.client_step a.client ev c' out /\
        c'.CS.cs_model.CS.model_config == a.client.CS.cs_model.CS.model_config)
      (ensures
        WStep.client_reachable (CS.initial c'.CS.cs_model.CS.model_config) c')
  = WStep.lemma_client_reachable_step
      (CS.initial a.client.CS.cs_model.CS.model_config) a.client c' ev out
#pop-options

(** Reachability preservation for a server step (config is stable). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_server_reach_pres
  (a:tls_system_state) (s':CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        server_byte_reachable a /\ SCP.server_step a.server ev s' out /\
        s'.CS.cs_model.CS.model_config == a.server.CS.cs_model.CS.model_config)
      (ensures
        WStep.server_reachable (CS.initial s'.CS.cs_model.CS.model_config) s')
  = WStep.lemma_server_reachable_step
      (CS.initial a.server.CS.cs_model.CS.model_config) a.server s' ev out
#pop-options

(** STAGE 2B — a client step preserves the client end-to-end invariant (e2e).
    e2e is a genuine per-endpoint inductive property (`CTy2.client_end_to_end_invariant`
    = client_state_correct /\ raw_to_message_replay_consistent).  A `CCP.client_step`
    supplies a legal connection delta together with the sent/received non-empty
    projection witnesses; the `CSL` delta lemmas then carry each replay-consistency
    component across the step, and the client-side raw-to-message bridge recovers the
    final conjunct.  Having e2e in the invariant lets the byte machinery discharge the
    control-based coupling (`client_at_appdata /\ quiet ==> server_post_cf`) exactly as
    it discharges the ready-based one. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_step_e2e
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        CCP.client_step st0 e st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CTy2.client_end_to_end_invariant st0)
      (ensures CTy2.client_end_to_end_invariant st1)
  = assert (exists (d:CS.connection_delta).
        CS.legal_connection_delta st0 d st1 /\
        CS.sent_event_nonempty_seal_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received);
    eliminate exists (d:CS.connection_delta).
        CS.legal_connection_delta st0 d st1 /\
        CS.sent_event_nonempty_seal_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
        CS.received_event_nonempty_decode_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received
    returns CTy2.client_end_to_end_invariant st1
    with _pf.
      (CSL.lemma_step_model_preserves_config st0.CS.cs_model d.CS.delta_event st1.CS.cs_model;
       CSL.lemma_legal_connection_delta_consistent st0 d st1;
       CSL.lemma_legal_connection_delta_full_log_consistent st0 d st1;
       CSL.lemma_legal_connection_delta_sent_seal_replay_consistent st0 d st1;
       CSL.lemma_connection_state_sent_seal_key_schedule_replay st1;
       CSL.lemma_legal_connection_delta_received_decode_replay_consistent st0 d st1;
       CSL.lemma_connection_state_received_decode_key_schedule_replay st1;
       CTy2.lemma_client_state_correct_raw_to_message_replay st1)
#pop-options

(** STAGE 2B (server) — a server step preserves the guarded server end-to-end
    invariant.  Mirrors `lemma_client_step_e2e`: a `SCP.server_step` supplies a
    legal connection delta with the sent/received non-empty projection witnesses,
    the `CSL` delta lemmas carry each replay-consistency component across the step,
    and config immutability transports the validity guard.  Because the guard is on
    the immutable config, the real work only fires when the pre-state is already
    valid; otherwise the post-guard is false and the obligation is vacuous. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_server_step_e2e
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step st0 e st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (server_config_valid_e2e st0 ==> ST.server_end_to_end_invariant st0))
      (ensures
        (server_config_valid_e2e st1 ==> ST.server_end_to_end_invariant st1))
  = introduce server_config_valid_e2e st1 ==> ST.server_end_to_end_invariant st1
    with _guard1.
    (
      assert (exists (d:CS.connection_delta).
          CS.legal_connection_delta st0 d st1 /\
          CS.sent_event_nonempty_seal_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
          CS.received_event_nonempty_decode_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received);
      eliminate exists (d:CS.connection_delta).
          CS.legal_connection_delta st0 d st1 /\
          CS.sent_event_nonempty_seal_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
          CS.received_event_nonempty_decode_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received
      returns ST.server_end_to_end_invariant st1
      with _pf.
        (CSL.lemma_step_model_preserves_config
           st0.CS.cs_model d.CS.delta_event st1.CS.cs_model;
         // config immutability transports the validity guard backward to st0.
         assert (server_config_valid_e2e st0);
         assert (ST.server_end_to_end_invariant st0);
         CSL.lemma_legal_connection_delta_consistent st0 d st1;
         CSL.lemma_legal_connection_delta_full_log_consistent_for_role
           CS.ServerEndpoint st0 d st1;
         CSL.lemma_legal_connection_delta_sent_seal_replay_consistent st0 d st1;
         CSL.lemma_legal_connection_delta_received_decode_replay_consistent st0 d st1;
         CSL.lemma_legal_connection_delta_raw_event_replay_consistent st0 d st1;
         CSL.lemma_connection_state_protected_raw_segmented_replay st1)
    )
#pop-options

(** Byte-pairing preservation — client SEND (Quiet -> InFlight to server). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_bp_client_send
  (a:tls_system_state) (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\ TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        byte_pairing
          ({ a with client = c';
                    channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent }))
  = PNTWL.lemma_client_step_wire_log_delta a.client (SM.LocalEvent local) c' out;
    Seq.lemma_eq_elim
      a.client.CS.cs_wire_log.CL.raw_sent
      a.server.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim
      a.server.CS.cs_wire_log.CL.raw_sent
      a.client.CS.cs_wire_log.CL.raw_received
#pop-options

(** Byte-pairing preservation — server SEND (Quiet -> InFlight to client). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_bp_server_send
  (a:tls_system_state) (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\ TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        byte_pairing
          ({ a with server = s';
                    channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent }))
  = PNTWL.lemma_server_step_wire_log_delta a.server (SM.LocalEvent local) s' out;
    Seq.lemma_eq_elim
      a.client.CS.cs_wire_log.CL.raw_sent
      a.server.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim
      a.server.CS.cs_wire_log.CL.raw_sent
      a.client.CS.cs_wire_log.CL.raw_received
#pop-options

(** Byte-pairing preservation — deliver to SERVER (InFlight to server -> Quiet). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_bp_deliver_to_server
  (a:tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\
        a.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        SCP.server_step a.server (SM.WireEvent wire) s' out)
      (ensures byte_pairing ({ a with server = s'; channel = TlsQuiet }))
  = PNTWL.lemma_server_step_wire_log_delta a.server (SM.WireEvent wire) s' out;
    WStep.lemma_server_wire_event_no_output a.server s' wire out;
    WStep.lemma_serialize_all_single_wire wire;
    Seq.lemma_eq_elim
      a.server.CS.cs_wire_log.CL.raw_sent
      a.client.CS.cs_wire_log.CL.raw_received
#pop-options

(** Byte-pairing preservation — deliver to CLIENT (InFlight to client -> Quiet). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_bp_deliver_to_client
  (a:tls_system_state) (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\
        a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        CCP.client_step a.client (SM.WireEvent wire) c' out)
      (ensures byte_pairing ({ a with client = c'; channel = TlsQuiet }))
  = PNTWL.lemma_client_step_wire_log_delta a.client (SM.WireEvent wire) c' out;
    WStep.lemma_client_wire_event_no_output a.client c' wire out;
    WStep.lemma_serialize_all_single_wire wire;
    Seq.lemma_eq_elim
      a.client.CS.cs_wire_log.CL.raw_sent
      a.server.CS.cs_wire_log.CL.raw_received
#pop-options

(** Byte-pairing preservation — client LOCAL (Quiet -> Quiet, no wire output). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_bp_client_local
  (a:tls_system_state) (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        byte_pairing a /\ TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [])
      (ensures byte_pairing ({ a with client = c' }))
  = PNTWL.lemma_client_step_wire_log_delta a.client (SM.LocalEvent local) c' out;
    Seq.lemma_eq_elim
      a.client.CS.cs_wire_log.CL.raw_sent
      a.server.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim
      a.server.CS.cs_wire_log.CL.raw_sent
      a.client.CS.cs_wire_log.CL.raw_received
#pop-options

(** Byte-pairing preservation — server LOCAL (Quiet -> Quiet, no wire output). **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_bp_server_local
  (a:tls_system_state) (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        byte_pairing a /\ TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [])
      (ensures byte_pairing ({ a with server = s' }))
  = PNTWL.lemma_server_step_wire_log_delta a.server (SM.LocalEvent local) s' out;
    Seq.lemma_eq_elim
      a.client.CS.cs_wire_log.CL.raw_sent
      a.server.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim
      a.server.CS.cs_wire_log.CL.raw_sent
      a.client.CS.cs_wire_log.CL.raw_received
#pop-options

(** Bridge: driver readiness entails `ControlApplicationData`.  Needed to relate
    the (control-based) coupling clause to the (readiness-based) length clauses.
    Discharged by unfolding `CD.client_driver_application_ready`. **)
let lemma_client_ready_implies_appdata (s:tls_system_state)
  : Lemma (ensures client_ready s ==> client_at_appdata s)
  = ()

(** Reachability wrapper: a consistent client at `ControlApplicationData` has
    installed both application-traffic secrets.  The predicate
    `PC.client_appdata_appkeys` is single-step stable (`PC.lemma_..._delta`) and
    holds at the initial state (control `ControlNew`), so it propagates along the
    reachability closure that defines `connection_state_consistent`. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_appdata_appkeys_reachable (st:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
  = let p = PC.client_appdata_appkeys_st in
    let stable : squash (forall (x y:CS.connection_state).
        {:pattern (p y); (CS.connection_state_single_step x y)}
        p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _.
        (eliminate exists (d:CS.connection_delta). CS.legal_connection_delta x d y
         returns p y
         with _pd. PC.lemma_client_appdata_appkeys_delta x y d) in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** Keys bridge: a consistent client carrying `client_at_appdata` has both
    application-traffic secrets installed.  Wraps the reachability lemma behind a
    guard so the call site only needs consistency + the client role. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_surface_client_appkeys (s:tls_system_state)
  : Lemma
      (requires
        CS.connection_state_consistent s.client /\
        s.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        client_at_appdata s ==>
          (Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
           Some? s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic))
  = if CS.ControlApplicationData? (s.client.CS.cs_model.CS.model_control)
    then lemma_client_appdata_appkeys_reachable s.client
    else ()
#pop-options

(** A trace with no key-update ending in `ev` has `ev` itself not a key-update. **)
let rec lemma_no_key_update_last (l:list CS.conn_event) (ev:CS.conn_event)
  : Lemma
      (requires CS.conn_events_no_key_update (FStar.List.Tot.append l [ev]) == true)
      (ensures CS.conn_event_is_key_update ev == false)
      (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> lemma_no_key_update_last rest ev

(** A trace whose extension by one event has no key-update also has no key-update
    on its prefix (backward monotonicity of the no-rekeying predicate). **)
let rec lemma_no_key_update_prefix (l:list CS.conn_event) (ev:CS.conn_event)
  : Lemma
      (requires CS.conn_events_no_key_update (FStar.List.Tot.append l [ev]) == true)
      (ensures CS.conn_events_no_key_update l == true)
      (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> lemma_no_key_update_prefix rest ev

(** Backward no-rekeying across a single legal delta: if the post-state has no
    key-update in its event log, neither does the pre-state (the pre-log is a
    prefix of the post-log, which is the pre-log extended by the delta event). **)
let lemma_delta_no_key_update_backward (st0 st1:CS.connection_state)
  : Lemma
      (requires (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1) /\
                CS.connection_state_no_key_update_trace st1)
      (ensures CS.connection_state_no_key_update_trace st0)
  = eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns CS.connection_state_no_key_update_trace st0
    with _pf.
      (lemma_no_key_update_prefix st0.CS.cs_event_log d.CS.delta_event)

(** Backward no-rekeying across an official client step. **)
let lemma_client_step_no_ku_backward
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CCP.client_step st0 e st1 out /\
                CS.connection_state_no_key_update_trace st1)
      (ensures CS.connection_state_no_key_update_trace st0)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    lemma_delta_no_key_update_backward st0 st1

(** Backward no-rekeying across an official server step. **)
let lemma_server_step_no_ku_backward
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires SCP.server_step st0 e st1 out /\
                CS.connection_state_no_key_update_trace st1)
      (ensures CS.connection_state_no_key_update_trace st0)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    lemma_delta_no_key_update_backward st0 st1

(** `advance_direction_records` is iterated `next_seq`, which rewrites only the
    sequence number; it never touches the record key or static IV. **)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec lemma_advance_preserves_key_iv (st:R.direction_state) (n:nat)
  : Lemma
      (ensures
        (CS.advance_direction_records st n).R.key == st.R.key /\
        (CS.advance_direction_records st n).R.static_iv == st.R.static_iv)
      (decreases n)
  = if n = 0 then () else lemma_advance_preserves_key_iv st (n - 1)
#pop-options

(** Backward preservation of application-record-key installation across a single
    application-data step.  `traffic_material_matches_record_direction` inspects
    ONLY `.key`/`.static_iv` (never `.seq`/`.epoch`); an application-data
    send/receive performs `next_seq`/`advance_direction_records` and never
    rewrites the record key or IV, and the no-key-update guard excludes the only
    event (KeyUpdate) that would.  So if the post-state has the application record
    keys installed, so does the pre-state.  This lets a ready POST client certify a
    ready PRE client across an application-data send at `ControlApplicationData`. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_appdata_installed_backward
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        CS.connection_state_no_key_update_trace st1 /\
        CS.application_record_keys_installed_for_role CS.ClientEndpoint st1.CS.cs_model)
      (ensures
        CS.application_record_keys_installed_for_role CS.ClientEndpoint st0.CS.cs_model)
  = lemma_no_key_update_last st0.CS.cs_event_log d.CS.delta_event;
    match d.CS.delta_event with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsApplicationData bytes ->
         lemma_advance_preserves_key_iv
           st0.CS.cs_model.CS.model_record.CS.record_write
           (S.application_data_record_count bytes)
       | _ -> ())
    | CS.ConnLocalEvent _ -> ()
#pop-options

(** PHASE 1 — the internal LOCAL guard implies the send/deliver guard.

    The two internal-local transitions are guarded by the STRICTER
    `client_local_advances`/`server_local_advances` (progress↑ ∨ control-changed)
    rather than `client_advances`/`server_advances` (progress↑ ∨ ¬pre-appdata).
    For a genuinely local step (empty wire output), the two guards coincide on the
    outcome we need for the forward LENGTH invariant: whenever the acting endpoint
    stays pre-application-data, a control change forces a strict progress increase
    (`PC.lemma_{client,server}_control_change_progress`), so `local_advances`
    re-establishes `advances`.  This lets every downstream preservation helper
    (which was proved against the `advances` guard) apply unchanged. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_local_advances_to_advances
  (a c':CS.connection_state)
  (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        CCP.client_step a (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [] /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        PC.client_micro_shape a.CS.cs_model /\
        client_local_advances a c')
      (ensures client_advances a c')
  = if PC.client_progress c'.CS.cs_model > PC.client_progress a.CS.cs_model
    then ()
    else if not (PC.pre_appdata_control c'.CS.cs_model.CS.model_control)
    then ()
    else begin
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CCP.client_api_event_matches a api conn_ev /\
         CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta a
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty } c' /\
         CS.sent_event_nonempty_seal_projection a.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection a.CS.cs_model conn_ev B.empty)
      returns client_advances a c'
      with _pf.
      (
        // pre_appdata a follows from pre_appdata c' by post-appdata stability.
        FStar.Classical.move_requires_3
          PC.lemma_step_post_appdata_stable a.CS.cs_model conn_ev c'.CS.cs_model;
        PC.lemma_client_control_change_progress a.CS.cs_model conn_ev c'.CS.cs_model
      )
    end
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_local_advances_to_advances
  (a s':CS.connection_state)
  (local:CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step a (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [] /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        PC.server_micro_shape a.CS.cs_model /\
        server_local_advances a s')
      (ensures server_advances a s')
  = if PC.server_progress s'.CS.cs_model > PC.server_progress a.CS.cs_model
    then ()
    else if not (PC.pre_appdata_control s'.CS.cs_model.CS.model_control)
    then ()
    else begin
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (SCP.server_api_event_matches api conn_ev /\
         SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta a
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty } s' /\
         CS.sent_event_nonempty_seal_projection a.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection a.CS.cs_model conn_ev B.empty)
      returns server_advances a s'
      with _pf.
      (
        // raw_sent is empty (out.so_wire_outputs == []), so the raw byte delta is
        // empty on both sides — this rules out the window Sent/deliver control
        // changes, leaving exactly the internal local control change.
        assert (Seq.equal raw_sent (WF.serialize_all CW.tls_record_wire_format []));
        Seq.lemma_eq_elim raw_sent B.empty;
        FStar.Classical.move_requires_3
          PC.lemma_step_post_appdata_stable a.CS.cs_model conn_ev s'.CS.cs_model;
        PC.lemma_server_control_change_progress a.CS.cs_model conn_ev s'.CS.cs_model
      )
    end
#pop-options

(* PHASE-1 clean16 removal: the three lemma_client_appdata_len_pres_{send,
   deliver,local} lemmas (which proved the dropped client_appdata_len_ok
   conjunct) were removed along with that conjunct. *)

(** ─────────────────────────────────────────────────────────────────────────
    FACT 4 (protected_witnesses_ok) preservation — Phase 4.

    ROUTE A engine: at `ControlApplicationData` no legal step sets any of the five
    write-once protected handshake fields (every `step_model` case that assigns one
    is guarded by a `ControlHandshaking` control), so the ten fields on which the
    projection-pair witnesses depend are invariant across the step.  This transports
    the existential witnesses unchanged (`lemma_pw_transport`).
    ───────────────────────────────────────────────────────────────────────── **)

(** Core model fact: a legal step from `ControlApplicationData` leaves the five
    protected handshake fields fixed. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_step_appdata_preserves_protected_fields
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires m.CS.model_control == CS.ControlApplicationData /\
                CS.step_model m ev == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_encrypted_extensions
          == m.CS.model_handshake.CS.hs_encrypted_extensions /\
        m'.CS.model_handshake.CS.hs_certificate
          == m.CS.model_handshake.CS.hs_certificate /\
        m'.CS.model_handshake.CS.hs_certificate_verify
          == m.CS.model_handshake.CS.hs_certificate_verify /\
        m'.CS.model_handshake.CS.hs_server_finished
          == m.CS.model_handshake.CS.hs_server_finished /\
        m'.CS.model_handshake.CS.hs_client_finished
          == m.CS.model_handshake.CS.hs_client_finished)
  = ()
#pop-options

(** Client-step lift of the field-stability fact. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_step_appdata_preserves_protected_fields
  (a c':CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CCP.client_step a e c' out /\
                a.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        (hsf c').CS.hs_encrypted_extensions == (hsf a).CS.hs_encrypted_extensions /\
        (hsf c').CS.hs_certificate == (hsf a).CS.hs_certificate /\
        (hsf c').CS.hs_certificate_verify == (hsf a).CS.hs_certificate_verify /\
        (hsf c').CS.hs_server_finished == (hsf a).CS.hs_server_finished /\
        (hsf c').CS.hs_client_finished == (hsf a).CS.hs_client_finished)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d c');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d c'
    returns
        (hsf c').CS.hs_encrypted_extensions == (hsf a).CS.hs_encrypted_extensions /\
        (hsf c').CS.hs_certificate == (hsf a).CS.hs_certificate /\
        (hsf c').CS.hs_certificate_verify == (hsf a).CS.hs_certificate_verify /\
        (hsf c').CS.hs_server_finished == (hsf a).CS.hs_server_finished /\
        (hsf c').CS.hs_client_finished == (hsf a).CS.hs_client_finished
    with _pf.
      lemma_step_appdata_preserves_protected_fields
        a.CS.cs_model d.CS.delta_event c'.CS.cs_model
#pop-options

(** Server-step lift of the field-stability fact. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_step_appdata_preserves_protected_fields
  (a s':CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires SCP.server_step a e s' out /\
                a.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        (hsf s').CS.hs_encrypted_extensions == (hsf a).CS.hs_encrypted_extensions /\
        (hsf s').CS.hs_certificate == (hsf a).CS.hs_certificate /\
        (hsf s').CS.hs_certificate_verify == (hsf a).CS.hs_certificate_verify /\
        (hsf s').CS.hs_server_finished == (hsf a).CS.hs_server_finished /\
        (hsf s').CS.hs_client_finished == (hsf a).CS.hs_client_finished)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d s');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d s'
    returns
        (hsf s').CS.hs_encrypted_extensions == (hsf a).CS.hs_encrypted_extensions /\
        (hsf s').CS.hs_certificate == (hsf a).CS.hs_certificate /\
        (hsf s').CS.hs_certificate_verify == (hsf a).CS.hs_certificate_verify /\
        (hsf s').CS.hs_server_finished == (hsf a).CS.hs_server_finished /\
        (hsf s').CS.hs_client_finished == (hsf a).CS.hs_client_finished
    with _pf.
      lemma_step_appdata_preserves_protected_fields
        a.CS.cs_model d.CS.delta_event s'.CS.cs_model
#pop-options

(** Transport: the projection-pair witnesses depend only on the ten write-once
    protected handshake fields, so if those fields agree between (ac,as) and
    (bc,bs) the witnesses carry over. **)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_pw_transport (ac ase bc bs:CS.connection_state)
  : Lemma
      (requires
        (hsf bc).CS.hs_encrypted_extensions == (hsf ac).CS.hs_encrypted_extensions /\
        (hsf bc).CS.hs_certificate == (hsf ac).CS.hs_certificate /\
        (hsf bc).CS.hs_certificate_verify == (hsf ac).CS.hs_certificate_verify /\
        (hsf bc).CS.hs_server_finished == (hsf ac).CS.hs_server_finished /\
        (hsf bc).CS.hs_client_finished == (hsf ac).CS.hs_client_finished /\
        (hsf bs).CS.hs_encrypted_extensions == (hsf ase).CS.hs_encrypted_extensions /\
        (hsf bs).CS.hs_certificate == (hsf ase).CS.hs_certificate /\
        (hsf bs).CS.hs_certificate_verify == (hsf ase).CS.hs_certificate_verify /\
        (hsf bs).CS.hs_server_finished == (hsf ase).CS.hs_server_finished /\
        (hsf bs).CS.hs_client_finished == (hsf ase).CS.hs_client_finished /\
        P.paired_protected_handshake_event_projection_pair_witnesses ac ase)
      (ensures P.paired_protected_handshake_event_projection_pair_witnesses bc bs)
  = eliminate exists ee cert cv sf cf.
      PWL.paired_protected_handshake_event_projection_pairs ac ase ee cert cv sf cf
    returns P.paired_protected_handshake_event_projection_pair_witnesses bc bs
    with _pf.
      assert (PWL.paired_protected_handshake_event_projection_pairs bc bs ee cert cv sf cf)
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    ENTRY-SHAPE model lemmas — WHICH transition can move an endpoint INTO
    `ControlApplicationData`, and the pre-state it must have come from.  These are
    pure `connection_model` facts (verified at fuel 2 / ifuel 5) used to case-split
    the FACT-4 preservation obligation.
    ───────────────────────────────────────────────────────────────────────── **)

(** SERVER: the routes into application data.  Under the atomic-delivery model
    (Realization 1A) there are now TWO:
      * the off-honest-path LocalVerifyClientFinished verify, at
        `HsClientFinishedReceived`, with app record keys already installed
        (a genuine `ConnLocalEvent`); and
      * the atomic client-Finished DELIVERY, at `HsServerFinishedSent`, which is a
        `Received` network event that installs the client-app read keys and lands
        directly at application data. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_server_into_appdata_is_verify
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(m.CS.model_control == CS.ControlApplicationData) /\
        m'.CS.model_control == CS.ControlApplicationData)
      (ensures
        (m.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
         CS.application_record_keys_installed_for_role CS.ServerEndpoint m /\
         CS.ConnLocalEvent? ev)
        \/
        (m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
         CS.ConnNetworkEvent? ev /\
         (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Received))
  = ()
#pop-options

(** CLIENT: the only route into application data is SENDING the protected Finished,
    at `HsServerFinishedVerified` (a network `Sent` event). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_client_into_appdata_is_send_finished
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        ~(m.CS.model_control == CS.ControlApplicationData) /\
        m'.CS.model_control == CS.ControlApplicationData)
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = ()
#pop-options

(* PHASE-1 clean16 removal: lemma_server_recv_not_into_appdata and
   lemma_server_wire_recv_not_into_appdata REMOVED — under Realization 1A a
   Received (atomic client-Finished) delivery DOES enter application data, so
   these are no longer true; the deliver-to-server establishment now handles
   that route directly. *)

(** A server LOCAL-event API only ever matches a `ConnLocalEvent` or a `Sent`
    network event — never a `Received` delivery.  This lets the SEND/LOCAL
    into-appdata callers discard the (new) Received disjunct of
    `lemma_server_into_appdata_is_verify`. **)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 40"
let lemma_server_api_event_not_received
  (api:CTy.server_api_event) (ev:CS.conn_event)
  : Lemma (requires SCP.server_api_event_matches api ev)
          (ensures ~(CS.ConnNetworkEvent? ev /\
                     (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Received))
  = ()
#pop-options

(** SERVER step-level: a SEND (nonempty wire output) never enters application data. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_send_not_into_appdata
  (st0:CS.connection_state) (local:CTy.server_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message CTy.local_output)
  (w:CW.wire_message)
  : Lemma
      (requires
        SCP.server_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        out.SM.so_wire_outputs == [w] /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
  = if st0.CS.cs_model.CS.model_control = CS.ControlApplicationData then ()
    else begin
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (SCP.server_api_event_matches api conn_ev /\
         SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         CS.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
      returns st0.CS.cs_model.CS.model_control == CS.ControlApplicationData
      with _.
      (
        lemma_server_api_event_not_received api conn_ev;
        lemma_server_into_appdata_is_verify st0.CS.cs_model conn_ev st1.CS.cs_model;
        Seq.lemma_eq_elim raw_sent B.empty;
        WStep.lemma_serialize_all_single_wire w;
        WStep.lemma_wire_serialize_nonempty w
      )
    end
#pop-options

(** SERVER step-level: the shape of a no-output LOCAL step that enters application
    data — pre-control `HsClientFinishedReceived` with the record keys installed. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_local_into_appdata_shape
  (st0:CS.connection_state) (local:CTy.server_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        out.SM.so_wire_outputs == [] /\
        ~(st0.CS.cs_model.CS.model_control == CS.ControlApplicationData) /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st0.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.application_record_keys_installed_for_role CS.ServerEndpoint st0.CS.cs_model)
  = let api = CTy.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (SCP.server_api_event_matches api conn_ev /\
       SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       CS.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns
      (st0.CS.cs_model.CS.model_control
         == CS.ControlHandshaking CS.HsClientFinishedReceived /\
       CS.application_record_keys_installed_for_role CS.ServerEndpoint st0.CS.cs_model)
    with _.
      (lemma_server_api_event_not_received api conn_ev;
       lemma_server_into_appdata_is_verify st0.CS.cs_model conn_ev st1.CS.cs_model)
#pop-options

(** CLIENT step-level: the shape of a SEND ([w]) that enters application data —
    the pre-control is `HsServerFinishedVerified`. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_client_into_appdata_shape
  (st0:CS.connection_state) (local:CTy.client_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message CTy.local_output)
  (w:CW.wire_message)
  : Lemma
      (requires
        CCP.client_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        out.SM.so_wire_outputs == [w] /\
        ~(st0.CS.cs_model.CS.model_control == CS.ControlApplicationData) /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st0.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CCP.client_api_event_matches st0 api conn_ev /\
       CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       CS.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns
      st0.CS.cs_model.CS.model_control
        == CS.ControlHandshaking CS.HsServerFinishedVerified
    with _.
      lemma_client_into_appdata_is_send_finished
        st0.CS.cs_model conn_ev st1.CS.cs_model
#pop-options

(* PHASE-1 clean16 removal: lemma_server_verify_pre_length REMOVED — the
   length==16 boundary it fed is gone; lemma_pw_establish no longer needs it. *)

(** Backward preservation of SERVER application-record-key installation across a
    single application-data step (mirrors `lemma_client_appdata_installed_backward`). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_appdata_installed_backward
  (st0:CS.connection_state) (d:CS.connection_delta) (st1:CS.connection_state)
  : Lemma
      (requires
        CS.legal_connection_delta st0 d st1 /\
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        CS.connection_state_no_key_update_trace st1 /\
        CS.application_record_keys_installed_for_role CS.ServerEndpoint st1.CS.cs_model)
      (ensures
        CS.application_record_keys_installed_for_role CS.ServerEndpoint st0.CS.cs_model)
  = lemma_no_key_update_last st0.CS.cs_event_log d.CS.delta_event;
    match d.CS.delta_event with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsApplicationData bytes ->
         lemma_advance_preserves_key_iv
           st0.CS.cs_model.CS.model_record.CS.record_write
           (S.application_data_record_count bytes)
       | _ -> ())
    | CS.ConnLocalEvent _ -> ()
#pop-options

(** FACT-4 ESTABLISHMENT producer (ROUTE B).  From a ready+quiescent BOTH-ready
    boundary-16 state with the byte-level reachability/pairing facts, the hello
    key-share agreement, and no rekeying, the `clean16` producer supplies the
    protected projection-pair witnesses.  This is exactly the middle block of
    `lemma_ready_quiescent_agrees`, factored out so it can be invoked at the
    server-verify instant. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pw_establish (s:tls_system_state)
  : Lemma
      (requires
        client_byte_reachable s /\
        server_byte_reachable s /\
        byte_pairing s /\
        TlsQuiet? s.channel /\
        WFL.supported_client_config_wire_profile s.client.CS.cs_model.CS.model_config /\
        hello_key_shares_ok s /\
        tls_no_rekeying s /\
        Some? (hsf s.client).CS.hs_client_hello /\
        Some? (hsf s.server).CS.hs_client_hello /\
        Some? (hsf s.client).CS.hs_server_hello /\
        Some? (hsf s.server).CS.hs_server_hello /\
        s.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        s.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        client_ready s /\
        server_ready s)
      (ensures
        P.paired_protected_handshake_event_projection_pair_witnesses s.client s.server)
  =
    // ═══════════════════════════════════════════════════════════════════════
    // TEMPORARY GAP (clean16 removal, Phase 1): to be discharged by the
    // counting-free C3 incremental-protected-witnesses proof in Phase 2.
    // Tracked in plan.md.  This is the SOLE admit in the retained build.
    //
    // The statement is the TRUE establishment obligation: from an honest,
    // byte-reachable, byte-paired BOTH-ready quiescent boundary (with the hello
    // key-share agreement and no rekeying), the protected projection-pair
    // witnesses hold.  Only the clean16 length==16 counting preconditions were
    // removed; every honest precondition (reachability, pairing, both-ready,
    // hellos-present, roles, supported profile, no-rekeying) is retained.
    // ═══════════════════════════════════════════════════════════════════════
    admit ()
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    FACT-4 (protected_witnesses_ok) preservation — the per-transition helpers.

    ROUTE A engine (transport): when the changed endpoint is at
    `ControlApplicationData` at BOTH the pre- and post-state, the ten protected
    handshake fields are unchanged, and the pre-state is BOTH-ready, so the
    witnesses carried by `protected_witnesses_ok a` transport unchanged.
    ───────────────────────────────────────────────────────────────────────── **)

(** ROUTE A — a CLIENT-changing step whose client is at application data. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_client_appdata_route_a
  (a b:tls_system_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        CCP.client_step a.client e c' out /\
        CS.connection_state_no_key_update_trace c' /\
        b.client == c' /\ b.server == a.server /\
        a.client.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        client_ready b /\ server_ready b)
      (ensures
        P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.client d c');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.client d c'
    returns P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _pd.
    (
      lemma_no_key_update_last a.client.CS.cs_event_log d.CS.delta_event;
      lemma_client_appdata_installed_backward a.client d c';
      // client_ready a: client_e2e a (inv) /\ appdata a /\ keys a (backward).
      assert (client_ready a);
      // server unchanged, so server_ready a == server_ready b.
      assert (server_ready a);
      reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok a);
      assert (P.paired_protected_handshake_event_projection_pair_witnesses a.client a.server);
      lemma_client_step_appdata_preserves_protected_fields a.client c' e out;
      lemma_pw_transport a.client a.server b.client b.server
    )
#pop-options

(** ROUTE A — a SERVER-changing step whose server is at application data. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_server_appdata_route_a
  (a b:tls_system_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        SCP.server_step a.server e s' out /\
        CS.connection_state_no_key_update_trace s' /\
        b.server == s' /\ b.client == a.client /\
        a.server.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        client_ready b /\ server_ready b)
      (ensures
        P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s'
    returns P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _pd.
    (
      CSL.lemma_step_model_preserves_config
        a.server.CS.cs_model d.CS.delta_event s'.CS.cs_model;
      // guard(s') from server_ready b (=e2e s'); transport to a.server by config eq.
      assert (ST.server_end_to_end_invariant s');
      assert (ST.server_state_core_correct s');
      assert (server_config_valid_e2e s');
      assert (a.server.CS.cs_model.CS.model_config == s'.CS.cs_model.CS.model_config);
      assert (server_config_valid_e2e a.server);
      // e2e a from the guarded server_e2e conjunct.
      assert (ST.server_end_to_end_invariant a.server);
      lemma_no_key_update_last a.server.CS.cs_event_log d.CS.delta_event;
      lemma_server_appdata_installed_backward a.server d s';
      assert (server_ready a);
      assert (client_ready a);
      reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok a);
      assert (P.paired_protected_handshake_event_projection_pair_witnesses a.client a.server);
      lemma_server_step_appdata_preserves_protected_fields a.server s' e out;
      lemma_pw_transport a.client a.server b.client b.server
    )
#pop-options

(** client LOCAL — a no-output local never enters application data, so a ready
    post-state forces a ready pre-state (ROUTE A). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_client_local
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [] /\
        CS.connection_state_no_key_update_trace c' /\
        b == { a with client = c' })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      if a.client.CS.cs_model.CS.model_control = CS.ControlApplicationData
      then lemma_pw_pres_client_appdata_route_a a b (SM.LocalEvent local) c' out
      else WStep.lemma_client_local_noout_not_into_appdata a.client local c' out
    )
#pop-options

(** deliver TO CLIENT — a receive never enters application data (ROUTE A). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_deliver_to_client
  (a b:tls_system_state)
  (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        CCP.client_step a.client (SM.WireEvent wire) c' out /\
        CS.connection_state_no_key_update_trace c' /\
        b == { a with client = c'; channel = TlsQuiet })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      WStep.lemma_client_wire_recv_not_into_appdata a.client wire c' out;
      lemma_pw_pres_client_appdata_route_a a b (SM.WireEvent wire) c' out
    )
#pop-options

(** server SEND — a nonempty-output send never enters application data (ROUTE A). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_server_send
  (a b:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        CS.connection_state_no_key_update_trace s' /\
        b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      lemma_server_send_not_into_appdata a.server local s' out w;
      lemma_pw_pres_server_appdata_route_a a b (SM.LocalEvent local) s' out
    )
#pop-options

(** At `ControlApplicationData` both stage predicates force all handshake fields
    Some; in particular both hellos.  Factored out at higher ifuel so the big
    stage-predicate match reliably reduces. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 20"
let lemma_server_appdata_hellos_some (st:CS.connection_state)
  : Lemma (requires server_stage_ok st /\ ctrl st == CS.ControlApplicationData)
          (ensures Some? (hsf st).CS.hs_client_hello /\
                   Some? (hsf st).CS.hs_server_hello)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 4 --z3rlimit 20"
let lemma_client_appdata_hellos_some (st:CS.connection_state)
  : Lemma (requires client_stage_ok st /\ ctrl st == CS.ControlApplicationData)
          (ensures Some? (hsf st).CS.hs_client_hello /\
                   Some? (hsf st).CS.hs_server_hello)
  = ()
#pop-options

(** deliver TO SERVER — under Realization 1A the atomic client-Finished DELIVERY
    is now a route INTO application data.  So either the server was already ready
    (ROUTE A transport) or this delivery NEWLY creates the both-ready boundary
    (ROUTE B ESTABLISHMENT), discharged through the tracked gap lemma_pw_establish.
    The b-structural facts (server reachability, byte-pairing, hello key-share
    agreement, no-rekeying) are threaded from the master lemma, which establishes
    them just before this call. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_deliver_to_server
  (a b:tls_system_state)
  (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        SCP.server_step a.server (SM.WireEvent wire) s' out /\
        CS.connection_state_no_key_update_trace s' /\
        server_stage_ok s' /\
        tls_no_rekeying b /\
        server_byte_reachable b /\
        byte_pairing b /\
        hello_key_shares_ok b /\
        b == { a with server = s'; channel = TlsQuiet })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      if a.server.CS.cs_model.CS.model_control = CS.ControlApplicationData
      then lemma_pw_pres_server_appdata_route_a a b (SM.WireEvent wire) s' out
      else begin
        // ROUTE B ESTABLISHMENT — the atomic client-Finished delivery newly enters
        // application data.  Supply the honest preconditions of lemma_pw_establish.
        assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s');
        eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s'
        returns
          P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
        with _pd.
        (
          CSL.lemma_step_model_preserves_config
            a.server.CS.cs_model d.CS.delta_event s'.CS.cs_model;
          // client unchanged (b.client == a.client): reachability, profile, role.
          assert (client_byte_reachable b);
          assert (WFL.supported_client_config_wire_profile
                    b.client.CS.cs_model.CS.model_config);
          assert (b.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert (b.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
          // both ready ⟹ both at application data ⟹ four hellos Some.
          assert (b.server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          lemma_server_appdata_hellos_some b.server;
          assert (b.client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          lemma_client_appdata_hellos_some b.client;
          lemma_pw_establish b
        )
      end
    )
#pop-options

(* PHASE-1 clean16 removal: lemma_pw_verify_client_len16 REMOVED — it computed the
   client length==16 boundary consumed by the old lemma_pw_establish; the gapped
   lemma_pw_establish no longer takes length preconditions. *)


(** server LOCAL — either the server was already ready (ROUTE A) or this is the
    off-honest-path LocalVerifyClientFinished verify step that NEWLY creates the
    both-ready boundary (ROUTE B ESTABLISHMENT).  Under Realization 1A the honest
    path no longer traverses this verify (the client-Finished delivery installs
    atomically), but the verify remains LEGAL; if taken and it creates both-ready,
    the witnesses are established through the tracked gap lemma_pw_establish (no
    length==16 counting preconditions are needed any more). **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_server_local
  (a b:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        server_stage_ok s' /\
        out.SM.so_wire_outputs == [] /\
        CS.connection_state_no_key_update_trace s' /\
          b == { a with server = s' })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      if a.server.CS.cs_model.CS.model_control = CS.ControlApplicationData
      then lemma_pw_pres_server_appdata_route_a a b (SM.LocalEvent local) s' out
      else begin
        // ROUTE B — the (off-honest-path) verify step.
        lemma_server_local_into_appdata_shape a.server local s' out;
        // ── b-structural facts. ──
        lemma_bp_server_local a local s' out;
        lemma_wire_facts_server_local a b;
        // ── reachability + config (via the underlying legal delta). ──
        assert (client_ready a);
        assert (client_byte_reachable b);
        assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s');
        eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s'
        returns
          P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
        with _pd.
        (
          CSL.lemma_step_model_preserves_config
            a.server.CS.cs_model d.CS.delta_event s'.CS.cs_model;
          lemma_server_reach_pres a s' (SM.LocalEvent local) out;
          // ── roles preserved. ──
          assert (b.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert (b.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
          // ── four hellos Some on both sides (from stage_ok at appdata). ──
          assert (b.server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          lemma_server_appdata_hellos_some b.server;
          assert (b.client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          lemma_client_appdata_hellos_some b.client;
          lemma_pw_establish b
        )
      end
    )
#pop-options

(** client SEND — either the client was already ready (ROUTE A) or the send is the
    send-Finished that NEWLY enters application data.  In the latter case the
    pre-state client is at `HsServerFinishedVerified` (has sent NO ApplicationData
    record yet), yet `server_ready a` forces the server to have RECEIVED the
    client Finished (an ApplicationData record); the quiescent byte-pairing then
    forces the client to have SENT it — a contradiction, so the case is vacuous. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_client_send
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        CS.connection_state_no_key_update_trace c' /\
        b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      if a.client.CS.cs_model.CS.model_control = CS.ControlApplicationData
      then lemma_pw_pres_client_appdata_route_a a b (SM.LocalEvent local) c' out
      else begin
        // ENTRY (contradiction).
        let cfg_c = a.client.CS.cs_model.CS.model_config in
        let cfg_s = a.server.CS.cs_model.CS.model_config in
        lemma_client_into_appdata_shape a.client local c' out w;
        // a.client at HsServerFinishedVerified => pre_appdata; no appdata record sent.
        WStep.lemma_client_preappdata_sent_no_appdata cfg_c a.client;
        // server_ready a (server unchanged) => a.server at appdata => received an appdata record.
        WStep.lemma_server_appdata_received_appdata cfg_s a.server;
        // quiescent byte-pairing transports the counts: 0 == sent(client) == received(server) >= 1.
        WStep.lemma_raw_appdata_count_seq_equal
          a.client.CS.cs_wire_log.CL.raw_sent a.server.CS.cs_wire_log.CL.raw_received
      end
    )
#pop-options


(** The six preservation lemmas.  Each proves the STRUCTURAL half of the
    invariant fully (both stage predicates, consistency of both endpoints via the
    official step-preservation lemmas, the client-config profile, and
    no-rekeying, all from the shape guards + `inv a`), and pulls the wire FACTS
    from the named helpers above (with channel_consistent discharged inline in the
    LOCAL/DELIVER cases, where the post-state channel is quiet). **)
(** ─────────────────────────────────────────────────────────────────────────
    Stage-predicate inductiveness.

    `client_stage_ok`/`server_stage_ok` pin the acting endpoint to a
    role-appropriate control state and record which paired handshake message
    fields must be populated at that stage.  They are INDUCTIVE under the raw
    canonical step: `step_model` reaches each control stage only via the same
    delta event that atomically sets that stage's write-once message field, and
    no legal step ever un-sets a message field.  Hence at the SYSTEM level the
    six per-transition `stage_ok` side conditions are redundant with the
    `tls_system_inv` conjuncts — they can be dropped from the shapes and
    re-established inductively by these two lemmas, faithfully mirroring the
    official `client_step`/`server_step`.
    ───────────────────────────────────────────────────────────────────────── **)

(** CLIENT.  `client_stage_ok` is inductive per-step from `client_stage_ok`
    alone: the client advances control by one field at a time (it never dwells
    at a wide multi-field stage — it goes directly `HsServerFinishedVerified` →
    `ControlApplicationData`), so each control-advancing step sets exactly the
    newly-required field and carries the lower ones.  A split on the event's top
    constructor keeps the query small. **)
#restart-solver
#push-options "--fuel 1 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_client_step_preserves_stage_ok
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires CCP.client_step st0 e st1 out /\ client_stage_ok st0)
      (ensures client_stage_ok st1)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns client_stage_ok st1
    with _pf.
      (match d.CS.delta_event with
       | CS.ConnLocalEvent _ -> ()
       | CS.ConnNetworkEvent _ -> ())
#pop-options

(** SERVER.  `server_stage_ok` alone is NOT inductive per-step: at the wide
    `HsServerEncryptedFlightSent` stage the server dwells while filling EE,
    Certificate, CertificateVerify and Finished, and the Finished-send legality
    exposes only `hs_certificate_verify_verified`, not the presence of the
    Certificate/CertificateVerify fields it needs at `HsServerFinishedSent`.
    That coupling is a REACHABILITY fact, supplied by the role-pinned
    `WStep.server_stage_shape` invariant lifted off `connection_state_consistent`
    (which `lemma_server_step_pres` re-establishes for the post-state). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60"
let lemma_server_step_preserves_stage_ok
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step st0 e st1 out /\
        CS.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures server_stage_ok st1)
  = lemma_server_step_pres st0 st1 e out;
    WStep.lemma_connection_state_consistent_server_stage_shape st1
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PER-TRANSITION HELPER : client SEND.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_scop_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures SCB.seq_count_ok_pair b.client b.server)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      client_advances a.client c' /\
      b == ({ a with client = c';
                         channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent })
    returns SCB.seq_count_ok_pair b.client b.server
    with _pf.
    (
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CCP.client_api_event_matches a.client api conn_ev /\
         CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta a.client
           ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
              CS.delta_raw_received = B.empty }) c' /\
         CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty)
      returns SCB.seq_count_ok_pair b.client b.server
      with _pf2.
      (
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        SCB.lemma_wire_serialize_nonempty w;
        WStep.lemma_serialize_all_single_wire w;
        Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
        WStep.lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
        assert (B.length raw_sent > 0);
        SCB.lemma_nonempty_sent_event a.client.CS.cs_model conn_ev raw_sent B.empty;
        eliminate exists (msg:M.tls_message). conn_ev == CS.sent_tls_event msg
        returns SCB.seq_count_ok_pair b.client b.server
        with _pf3.
        (
          SCB.lemma_pread_sent a.client d c' msg;
          ( if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then
              (
                WStep.lemma_client_reachable_raw_sent_parses
                  a.client.CS.cs_model.CS.model_config a.client;
                eliminate exists (msgs:list CW.wire_message).
                  WF.parses_as CW.tls_record_wire_format
                    a.client.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
                returns SCB.pwrite_ok c'
                with _pf4.
                (
                  SCB.lemma_pre_appdata_back a.client d c';
                  assert (WStep.client_start_shape a.client.CS.cs_model);
                  WStep.lemma_client_step_sent_zero
                    a.client (SM.LocalEvent local) c' out;
                  WStep.lemma_raw_appdata_count_serialize_all out.SM.so_wire_outputs;
                  WStep.lemma_raw_appdata_count_seq_equal
                    raw_sent (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs);
                  SCB.lemma_consistent_record_key_epoch_coupling a.client;
                  SCB.lemma_sent_write_model_facts
                    a.client.CS.cs_model msg c'.CS.cs_model raw_sent B.empty;
                  WStep.lemma_raw_appdata_count_append
                    a.client.CS.cs_wire_log.CL.raw_sent raw_sent msgs;
                  Seq.lemma_eq_elim c'.CS.cs_wire_log.CL.raw_sent
                    (B.append a.client.CS.cs_wire_log.CL.raw_sent raw_sent);
                  SCB.lemma_pwrite_algebra a.client d c' msgs
                )
              )
            else () );
          assert (SCB.pwrite_ok b.server);
          assert (SCB.pread_ok b.server)
        )
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PER-TRANSITION HELPER : deliver to CLIENT (client RECEIVE).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_scop_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures SCB.seq_count_ok_pair b.client b.server)
  = eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output)
                     (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      CCP.client_step a.client (SM.WireEvent wire) c' out /\
      client_advances a.client c' /\
      b == ({ a with client = c'; channel = TlsQuiet })
    returns SCB.seq_count_ok_pair b.client b.server
    with _pf.
    (
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent
             ({ CL.message_direction = CL.Received; CL.message_value = msg }) in
         CS.legal_connection_delta a.client
           ({ CS.delta_event = conn_ev;
              CS.delta_raw_sent =
                WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
              CS.delta_raw_received = CW.wire_serialize wire }) c' /\
         CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev
           (CW.wire_serialize wire))
      returns SCB.seq_count_ok_pair b.client b.server
      with _pf2.
      (
        WStep.lemma_client_wire_event_no_output a.client c' wire out;
        let d : CS.connection_delta =
          { CS.delta_event = CS.received_tls_event msg;
            CS.delta_raw_sent =
              WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
            CS.delta_raw_received = CW.wire_serialize wire } in
        // WRITE side untouched.
        SCB.lemma_pwrite_received a.client d c' msg;
        // READ side.
        ( if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then
            (
              WStep.lemma_client_reachable_raw_received_parses
                a.client.CS.cs_model.CS.model_config a.client;
              eliminate exists (msgs:list CW.wire_message).
                WF.parses_as CW.tls_record_wire_format
                  a.client.CS.cs_wire_log.CL.raw_received msgs Seq.empty
              returns SCB.pread_ok c'
              with _pf4.
              (
                SCB.lemma_pre_appdata_back a.client d c';
                SCB.lemma_consistent_record_key_epoch_coupling a.client;
                WStep.lemma_consistent_server_hello_wire_bound a.client;
                WStep.lemma_step_model_server_hello_wire_bound_reachable_shape
                  a.client.CS.cs_model (CS.received_tls_event msg) c'.CS.cs_model;
                assert (CS.step_model a.client.CS.cs_model (CS.received_tls_event msg)
                          == Some c'.CS.cs_model);
                introduce (M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) ==>
                          B.length (W.serialize_handshake
                            (M.ServerHello (M.ServerHello?._0 (M.TlsHandshake?._0 msg)))) <= 16640
                with _hyp.
                (
                  assert (c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
                          Some (M.ServerHello?._0 (M.TlsHandshake?._0 msg)))
                );
                SCB.lemma_recv_read_model_facts
                  a.client.CS.cs_model msg c'.CS.cs_model
                  (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
                  (CW.wire_serialize wire);
                WStep.lemma_raw_appdata_count_append
                  a.client.CS.cs_wire_log.CL.raw_received (CW.wire_serialize wire) msgs;
                Seq.lemma_eq_elim c'.CS.cs_wire_log.CL.raw_received
                  (B.append a.client.CS.cs_wire_log.CL.raw_received (CW.wire_serialize wire));
                SCB.lemma_pread_algebra a.client d c' msgs
              )
            )
          else () );
        assert (SCB.pwrite_ok b.server);
        assert (SCB.pread_ok b.server)
      )
    )
#pop-options

#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_scop_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_send a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures SCB.seq_count_ok_pair b.client b.server)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      SCP.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      server_advances a.server s' /\
      b == ({ a with server = s';
                         channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent })
    returns SCB.seq_count_ok_pair b.client b.server
    with _pf.
    (
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (SCP.server_api_event_matches api conn_ev /\
         SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta a.server
           ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
              CS.delta_raw_received = B.empty }) s' /\
         CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty)
      returns SCB.seq_count_ok_pair b.client b.server
      with _pf2.
      (
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        SCB.lemma_wire_serialize_nonempty w;
        WStep.lemma_serialize_all_single_wire w;
        Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
        WStep.lemma_raw_appdata_count_seq_equal
          (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) raw_sent;
        assert (B.length raw_sent > 0);
        SCB.lemma_nonempty_sent_event a.server.CS.cs_model conn_ev raw_sent B.empty;
        eliminate exists (msg:M.tls_message). conn_ev == CS.sent_tls_event msg
        returns SCB.seq_count_ok_pair b.client b.server
        with _pf3.
        (
          // READ side untouched.
          SCB.lemma_pread_sent a.server d s' msg;
          // WRITE side.
          ( if PC.pre_appdata_control s'.CS.cs_model.CS.model_control then
              (
                SCB.lemma_server_reachable_raw_sent_parses
                  a.server.CS.cs_model.CS.model_config a.server;
                eliminate exists (msgs:list CW.wire_message).
                  WF.parses_as CW.tls_record_wire_format
                    a.server.CS.cs_wire_log.CL.raw_sent msgs Seq.empty
                returns SCB.pwrite_ok s'
                with _pf4.
                (
                  SCB.lemma_pre_appdata_back a.server d s';
                  SCB.lemma_consistent_record_key_epoch_coupling a.server;
                  // ServerHello bound (reachable-shape lifted across the step).
                  WStep.lemma_consistent_server_hello_wire_bound a.server;
                  WStep.lemma_step_model_server_hello_wire_bound_reachable_shape
                    a.server.CS.cs_model (CS.sent_tls_event msg) s'.CS.cs_model;
                  assert (CS.step_model a.server.CS.cs_model (CS.sent_tls_event msg)
                            == Some s'.CS.cs_model);
                  // ServerHello send ==> count(raw_sent)==0.
                  introduce (M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) ==>
                            WStep.raw_appdata_count raw_sent == 0
                  with _hyp.
                  (
                    SCB.lemma_sent_server_hello_stored
                      a.server.CS.cs_model msg s'.CS.cs_model;
                    WStep.lemma_cleartext_raw_count_zero msg raw_sent
                  );
                  // ClientHello send is impossible for a server (stage_ok excludes HsStarted).
                  introduce (M.TlsHandshake? msg /\ M.ClientHello? (M.TlsHandshake?._0 msg)) ==>
                            WStep.raw_appdata_count raw_sent == 0
                  with _hyp.
                  (
                    SCB.lemma_sent_client_hello_forces_hsstarted
                      a.server.CS.cs_model msg s'.CS.cs_model
                  );
                  SCB.lemma_sent_write_model_facts
                    a.server.CS.cs_model msg s'.CS.cs_model raw_sent B.empty;
                  WStep.lemma_raw_appdata_count_append
                    a.server.CS.cs_wire_log.CL.raw_sent raw_sent msgs;
                  Seq.lemma_eq_elim s'.CS.cs_wire_log.CL.raw_sent
                    (B.append a.server.CS.cs_wire_log.CL.raw_sent raw_sent);
                  SCB.lemma_pwrite_algebra a.server d s' msgs
                )
              )
            else () );
          assert (SCB.pwrite_ok b.client);
          assert (SCB.pread_ok b.client)
        )
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PER-TRANSITION HELPER : deliver to SERVER (server RECEIVE).
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 60 --split_queries always"
let lemma_scop_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures SCB.seq_count_ok_pair b.client b.server)
  = eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output)
                     (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      SCP.server_step a.server (SM.WireEvent wire) s' out /\
      server_advances a.server s' /\
      b == ({ a with server = s'; channel = TlsQuiet })
    returns SCB.seq_count_ok_pair b.client b.server
    with _pf.
    (
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent
             ({ CL.message_direction = CL.Received; CL.message_value = msg }) in
         CS.legal_connection_delta a.server
           ({ CS.delta_event = conn_ev;
              CS.delta_raw_sent =
                WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
              CS.delta_raw_received = CW.wire_serialize wire }) s' /\
         CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev
           (CW.wire_serialize wire))
      returns SCB.seq_count_ok_pair b.client b.server
      with _pf2.
      (
        WStep.lemma_server_wire_event_no_output a.server s' wire out;
        let d : CS.connection_delta =
          { CS.delta_event = CS.received_tls_event msg;
            CS.delta_raw_sent =
              WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
            CS.delta_raw_received = CW.wire_serialize wire } in
        // WRITE side untouched.
        SCB.lemma_pwrite_received a.server d s' msg;
        // READ side.
        ( if PC.pre_appdata_control s'.CS.cs_model.CS.model_control then
            (
              SCB.lemma_server_reachable_raw_received_parses
                a.server.CS.cs_model.CS.model_config a.server;
              eliminate exists (msgs:list CW.wire_message).
                WF.parses_as CW.tls_record_wire_format
                  a.server.CS.cs_wire_log.CL.raw_received msgs Seq.empty
              returns SCB.pread_ok s'
              with _pf4.
              (
                SCB.lemma_pre_appdata_back a.server d s';
                SCB.lemma_consistent_record_key_epoch_coupling a.server;
                WStep.lemma_consistent_server_hello_wire_bound a.server;
                WStep.lemma_step_model_server_hello_wire_bound_reachable_shape
                  a.server.CS.cs_model (CS.received_tls_event msg) s'.CS.cs_model;
                assert (CS.step_model a.server.CS.cs_model (CS.received_tls_event msg)
                          == Some s'.CS.cs_model);
                introduce (M.TlsHandshake? msg /\ M.ServerHello? (M.TlsHandshake?._0 msg)) ==>
                          B.length (W.serialize_handshake
                            (M.ServerHello (M.ServerHello?._0 (M.TlsHandshake?._0 msg)))) <= 16640
                with _hyp.
                (
                  SCB.lemma_recv_server_hello_stored
                    a.server.CS.cs_model msg s'.CS.cs_model
                );
                SCB.lemma_recv_read_model_facts
                  a.server.CS.cs_model msg s'.CS.cs_model
                  (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
                  (CW.wire_serialize wire);
                WStep.lemma_raw_appdata_count_append
                  a.server.CS.cs_wire_log.CL.raw_received (CW.wire_serialize wire) msgs;
                Seq.lemma_eq_elim s'.CS.cs_wire_log.CL.raw_received
                  (B.append a.server.CS.cs_wire_log.CL.raw_received (CW.wire_serialize wire));
                SCB.lemma_pread_algebra a.server d s' msgs
              )
            )
          else () );
        assert (SCB.pwrite_ok b.client);
        assert (SCB.pread_ok b.client)
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PER-TRANSITION HELPER : client LOCAL.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_scop_client_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_local a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures SCB.seq_count_ok_pair b.client b.server)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      client_local_advances a.client c' /\
      b == ({ a with client = c' })
    returns SCB.seq_count_ok_pair b.client b.server
    with _pf.
    (
      let api = CTy.client_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CCP.client_api_event_matches a.client api conn_ev /\
         CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta a.client
           ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
              CS.delta_raw_received = B.empty }) c' /\
         CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty)
      returns SCB.seq_count_ok_pair b.client b.server
      with _pf2.
      (
        WStep.lemma_serialize_all_nil_wire ();
        Seq.lemma_eq_elim raw_sent B.empty;
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        SCB.lemma_consistent_record_schedule_coupling a.client;
        SCB.lemma_consistent_record_app_epoch_coupling a.client;
        SCB.lemma_consistent_app_slots_none_shape a.client;
        SCB.lemma_client_local_pwrite a.client d c';
        SCB.lemma_client_local_pread a.client d c';
        assert (SCB.pwrite_ok b.client);
        assert (SCB.pread_ok b.client);
        assert (SCB.pwrite_ok b.server);
        assert (SCB.pread_ok b.server)
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    PER-TRANSITION HELPER : server LOCAL.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 60 --split_queries always"
let lemma_scop_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_local a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures SCB.seq_count_ok_pair b.client b.server)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      SCP.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      server_local_advances a.server s' /\
      b == ({ a with server = s' })
    returns SCB.seq_count_ok_pair b.client b.server
    with _pf.
    (
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (SCP.server_api_event_matches api conn_ev /\
         SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta a.server
           ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
              CS.delta_raw_received = B.empty }) s' /\
         CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
         CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty)
      returns SCB.seq_count_ok_pair b.client b.server
      with _pf2.
      (
        WStep.lemma_serialize_all_nil_wire ();
        Seq.lemma_eq_elim raw_sent B.empty;
        let d : CS.connection_delta =
          { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty } in
        SCB.lemma_consistent_record_schedule_coupling a.server;
        SCB.lemma_consistent_record_app_epoch_coupling a.server;
        SCB.lemma_consistent_app_slots_none_shape a.server;
        SCB.lemma_server_local_pwrite a.server d s';
        SCB.lemma_server_local_pread a.server d s';
        assert (SCB.pwrite_ok b.server);
        assert (SCB.pread_ok b.server);
        assert (SCB.pwrite_ok b.client);
        assert (SCB.pread_ok b.client)
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    MAIN THEOREM : `seq_count_ok` is preserved by any single honest system
    transition.  `tls_sys_step` unfolds to the 6-way disjunction of
    `tls_step_*`; each disjunct is discharged by its per-transition helper via
    `FStar.Classical.move_requires_2`.
    ───────────────────────────────────────────────────────────────────────── **)
val lemma_seq_count_ok_preserved (a b : tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_sys_step a b /\ SCB.seq_count_ok_pair a.client a.server)
          (ensures  SCB.seq_count_ok_pair b.client b.server)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_seq_count_ok_preserved a b =
  FStar.Classical.move_requires_2 lemma_scop_client_send a b;
  FStar.Classical.move_requires_2 lemma_scop_server_send a b;
  FStar.Classical.move_requires_2 lemma_scop_deliver_to_client a b;
  FStar.Classical.move_requires_2 lemma_scop_deliver_to_server a b;
  FStar.Classical.move_requires_2 lemma_scop_client_local a b;
  FStar.Classical.move_requires_2 lemma_scop_server_local a b
#pop-options


(* ============ PCR-ESTABLISH HELPER LEMMAS (from Scratch, verified) ============ *)

(* Experiment: derive that a server at record_write.epoch == Handshake is not at
   HsClientHelloReceived (nor HsStarted). *)

let write_hs_stage_shape (m:CS.connection_model) : prop =
  (m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
   m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived) /\
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello) /\
     ~(m.CS.model_control == CS.ControlNew)) /\
  (m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
   m.CS.model_record.CS.record_write.R.epoch == R.Handshake ==>
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsStarted) /\
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent) /\
     ~(m.CS.model_control == CS.ControlNew))

let base_secret_shape (m:CS.connection_model) : prop =
  let keys = m.CS.model_handshake.CS.hs_keys in
  (Some? keys.CS.ks_client_handshake_traffic ==> Some? keys.CS.ks_handshake_secret) /\
  (Some? keys.CS.ks_server_handshake_traffic ==> Some? keys.CS.ks_handshake_secret)

#push-options "--fuel 4 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_step_base_secret_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        base_secret_shape m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures base_secret_shape m')
  = match ev with
    | CS.ConnNetworkEvent _ -> ()
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalInstallTrafficKeys install -> ()
       | CS.LocalInstallTrafficKeysForRole role_install -> ()
       | _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_step_write_hs_stage_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        write_hs_stage_shape m /\
        SCB.record_schedule_coupling m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures write_hs_stage_shape m')
  = ()
#pop-options

(* Round-trip shape: a sent handshake message, given the control is not at the
   ClientHello-send stage (HsStarted) nor the ServerHello-send stage
   (HsClientHelloReceived), must be EE/Cert/CV/Finished. *)
#push-options "--fuel 4 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_sent_handshake_round_trip
  (m m':CS.connection_model) (hs:M.handshake_msg)
  : Lemma
      (requires
        CS.step_model m (CS.sent_tls_event (M.TlsHandshake hs)) == Some m' /\
        ~(m.CS.model_control == CS.ControlHandshaking CS.HsStarted) /\
        ~(m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived))
      (ensures PWB.protected_handshake_wire_round_trip_message hs)
  = match hs with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ -> ()
    | M.ClientHello _ -> ()
    | M.ServerHello _ -> ()
    | M.HelloRetryRequest -> ()
#pop-options

let read_hs_stage_shape (m:CS.connection_model) : prop =
  (m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
   m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived) /\
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello) /\
     ~(m.CS.model_control == CS.ControlNew)) /\
  (m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
   m.CS.model_record.CS.record_read.R.epoch == R.Handshake ==>
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsStarted) /\
     ~(m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent) /\
     ~(m.CS.model_control == CS.ControlNew))

#push-options "--fuel 4 --ifuel 6 --z3rlimit 60 --split_queries always"
let lemma_step_read_hs_stage_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        read_hs_stage_shape m /\
        SCB.record_schedule_coupling m /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures read_hs_stage_shape m')
  = ()
#pop-options

(* RTC closure: consistency implies the write-epoch stage shape. *)
let combined_shape (st:CS.connection_state) : prop =
  write_hs_stage_shape st.CS.cs_model /\
  read_hs_stage_shape st.CS.cs_model /\
  base_secret_shape st.CS.cs_model /\
  SCB.record_schedule_coupling st.CS.cs_model

let lemma_delta_combined_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires combined_shape st0 /\ CS.connection_state_single_step st0 st1)
      (ensures combined_shape st1)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    SCB.lemma_step_record_schedule_coupling
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
    lemma_step_write_hs_stage_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
    lemma_step_read_hs_stage_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model;
    lemma_step_base_secret_shape
      st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_write_hs_stage_shape (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures write_hs_stage_shape st.CS.cs_model /\
               read_hs_stage_shape st.CS.cs_model /\
               base_secret_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = combined_shape st in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _. lemma_delta_combined_shape x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(* ═══════════════════════════════════════════════════════════════════════════
   STAGE 3a INFRASTRUCTURE — handshake-field monotonicity + value-stability.

   `mono_shape` records, for each stored handshake message field, that once the
   field is `Some` the control has advanced at-or-past that message's write
   point.  This is inductive (each write step advances the control past the
   write point, and no later step re-writes the field).  From it we derive
   `vstable`: across any legal step, a `Some` field keeps its exact value —
   the value-stability primitive used to TRANSPORT the replay-witness clauses.
   ═══════════════════════════════════════════════════════════════════════════ *)

let s_ge_eeflight (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let s_ge_finsent (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let s_ge_cfrecv (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsClientFinishedReceived
  | CS.ControlHandshaking CS.HsClientFinishedVerified
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let c_ge_eerecv (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
  | CS.ControlHandshaking CS.HsCertificateReceived
  | CS.ControlHandshaking CS.HsCertificateValidated
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified
  | CS.ControlHandshaking CS.HsServerFinishedReceived
  | CS.ControlHandshaking CS.HsServerFinishedVerified
  | CS.ControlHandshaking CS.HsClientFinishedSent
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let c_ge_certrecv (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsCertificateReceived
  | CS.ControlHandshaking CS.HsCertificateValidated
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified
  | CS.ControlHandshaking CS.HsServerFinishedReceived
  | CS.ControlHandshaking CS.HsServerFinishedVerified
  | CS.ControlHandshaking CS.HsClientFinishedSent
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let c_ge_cvrecv (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified
  | CS.ControlHandshaking CS.HsServerFinishedReceived
  | CS.ControlHandshaking CS.HsServerFinishedVerified
  | CS.ControlHandshaking CS.HsClientFinishedSent
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let c_ge_sfrecv (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlHandshaking CS.HsServerFinishedReceived
  | CS.ControlHandshaking CS.HsServerFinishedVerified
  | CS.ControlHandshaking CS.HsClientFinishedSent
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false
let c_ge_appdata (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlApplicationData | CS.ControlClosing | CS.ControlClosed | CS.ControlFailed _ -> true
  | _ -> false

let mono_shape (m:CS.connection_model) : prop =
  let hs = m.CS.model_handshake in
  let c = m.CS.model_control in
  (m.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
    (Some? hs.CS.hs_encrypted_extensions ==> s_ge_eeflight c) /\
    (Some? hs.CS.hs_certificate ==> s_ge_eeflight c) /\
    (Some? hs.CS.hs_certificate_verify ==> s_ge_eeflight c) /\
    (Some? hs.CS.hs_server_finished ==> s_ge_finsent c) /\
    (Some? hs.CS.hs_client_finished ==> s_ge_cfrecv c)) /\
  (m.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
    (Some? hs.CS.hs_encrypted_extensions ==> c_ge_eerecv c) /\
    (Some? hs.CS.hs_certificate ==> c_ge_certrecv c) /\
    (Some? hs.CS.hs_certificate_verify ==> c_ge_cvrecv c) /\
    (Some? hs.CS.hs_server_finished ==> c_ge_sfrecv c) /\
    (Some? hs.CS.hs_client_finished ==> c_ge_appdata c))

#push-options "--fuel 4 --ifuel 8 --z3rlimit 150 --split_queries always"
let lemma_step_mono_shape (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires mono_shape m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures mono_shape m')
  = ()
#pop-options

let vstable (m m':CS.connection_model) : prop =
  let h = m.CS.model_handshake in let h' = m'.CS.model_handshake in
  (Some? h.CS.hs_encrypted_extensions ==> h'.CS.hs_encrypted_extensions == h.CS.hs_encrypted_extensions) /\
  (Some? h.CS.hs_certificate ==> h'.CS.hs_certificate == h.CS.hs_certificate) /\
  (Some? h.CS.hs_certificate_verify ==> h'.CS.hs_certificate_verify == h.CS.hs_certificate_verify) /\
  (Some? h.CS.hs_server_finished ==> h'.CS.hs_server_finished == h.CS.hs_server_finished) /\
  (Some? h.CS.hs_client_finished ==> h'.CS.hs_client_finished == h.CS.hs_client_finished)

#push-options "--fuel 4 --ifuel 8 --z3rlimit 150 --split_queries always"
let lemma_step_vstable (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires mono_shape m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures vstable m m')
  = ()
#pop-options

let lemma_delta_mono_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires mono_shape st0.CS.cs_model /\ CS.connection_state_single_step st0 st1)
      (ensures mono_shape st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_mono_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_mono_shape (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures mono_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = mono_shape st.CS.cs_model in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _. lemma_delta_mono_shape x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(* Value-stability at a single consistent step: a `Some` handshake field keeps
   its value. *)
let lemma_consistent_step_vstable (st0 st1:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st0 /\ CS.connection_state_single_step st0 st1)
      (ensures vstable st0.CS.cs_model st1.CS.cs_model)
  = lemma_consistent_mono_shape st0;
    let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_vstable st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

(* Client write-epoch shape: a client in a handshaking (or New) control has a
   write epoch that is not Application.  Needed for the client-Finished send. *)
let client_write_hs_epoch_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  (CS.ControlHandshaking? m.CS.model_control \/ m.CS.model_control == CS.ControlNew) ==>
    m.CS.model_record.CS.record_write.R.epoch =!= R.Application

#push-options "--fuel 2 --ifuel 4 --z3rlimit 200 --split_queries always"
let lemma_step_client_write_hs_epoch_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires client_write_hs_epoch_shape m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures client_write_hs_epoch_shape m')
  = ()
#pop-options

let lemma_delta_client_write_hs_epoch_shape (st0 st1:CS.connection_state)
  : Lemma
      (requires client_write_hs_epoch_shape st0.CS.cs_model /\ CS.connection_state_single_step st0 st1)
      (ensures client_write_hs_epoch_shape st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_client_write_hs_epoch_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_client_write_hs_epoch_shape (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures client_write_hs_epoch_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = client_write_hs_epoch_shape st.CS.cs_model in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _. lemma_delta_client_write_hs_epoch_shape x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(* ── lemma_pcr_paired_x25519 : copy of Pairing.fst match body (486-527) ── *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_pcr_paired_x25519 (client server:CS.connection_state)
  : Lemma
      (requires
        CS.client_x25519_key_share_projection client /\
        CS.server_x25519_key_share_projection server /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures CS.paired_x25519_key_shares client server)
=
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_start,
    client_hs.CS.hs_client_hello,
    client_hs.CS.hs_server_hello,
    client_hs.CS.hs_keys.CS.ks_shared_secret,
    server_hs.CS.hs_server_selection,
    server_hs.CS.hs_client_hello,
    server_hs.CS.hs_server_hello,
    server_hs.CS.hs_keys.CS.ks_shared_secret
  with
  | Some start, Some client_ch, Some client_sh, Some client_shared,
    Some selection, Some server_ch, Some server_sh, Some server_shared ->
    (match
     start.CS.start_client_key_share_private,
     selection.CS.server_key_share_private
     with
     | Some client_sk, Some server_sk ->
      assert (WFL.paired_cleartext_hello_key_shares client server);
      assert (CS.client_hello_key_share client_ch ==
        CS.client_hello_key_share server_ch);
      assert (CS.server_hello_key_share client_sh ==
        CS.server_hello_key_share server_sh);
      (match
         CS.client_hello_key_share server_ch,
         CS.server_hello_key_share client_sh
       with
       | Some ch_ks, Some sh_ks ->
         assert (ch_ks == start.CS.start_client_key_share_public);
         assert (sh_ks == selection.CS.server_key_share_public);
         assert (C.x25519_public_from_private client_sk ==
           start.CS.start_client_key_share_public);
         assert (C.x25519_public_from_private server_sk ==
           selection.CS.server_key_share_public);
         assert (C.x25519_shared client_sk sh_ks == Some client_shared);
         assert (C.x25519_shared server_sk ch_ks == Some server_shared)
       | _, _ -> assert False)
     | _, _ ->
      assert False)
  | _, _, _, _, _, _, _, _ ->
    assert False
#pop-options

(* ── H_mat for server_send: peer_record_material_agrees ServerTraffic client server ── *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_pcr_hmat_server_send (client server:CS.connection_state)
    (client_ch server_ch:GCH.clientHello) (client_sh server_sh:GSH.serverHello)
  : Lemma
      (requires
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        PC.pre_appdata_control server.CS.cs_model.CS.model_control /\
        PC.pre_appdata_control client.CS.cs_model.CS.model_control /\
        server.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
        client.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        (exists raw.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw) /\
        (exists raw.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw) /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) client server)
=
  // shapes
  lemma_consistent_write_hs_stage_shape client;
  lemma_consistent_write_hs_stage_shape server;
  SCB.lemma_consistent_record_schedule_coupling client;
  SCB.lemma_consistent_record_schedule_coupling server;
  // Some? ks_handshake_secret both
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  // Some? ks_shared_secret both via lineage
  CSL.lemma_connection_state_consistent_handshake_key_schedule_lineage client;
  CSL.lemma_connection_state_consistent_handshake_key_schedule_lineage server;
  assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  // projections
  CSL.lemma_client_handshake_stable_x25519_key_share_projection client;
  assert (CS.client_x25519_key_share_projection client);
  assert (CS.ControlHandshaking? server.CS.cs_model.CS.model_control);
  assert (server.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsClientHelloReceived);
  CSL.lemma_server_handshake_stable_x25519_key_share_projection server;
  assert (CS.server_x25519_key_share_projection server);
  // paired x25519
  lemma_pcr_paired_x25519 client server;
  assert (CS.paired_x25519_key_shares client server);
  // checkpoint
  eliminate exists raw1.
    CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw1 /\
    CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw1
  returns CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server
  with _p1.
    eliminate exists raw2.
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
    returns CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server
    with _p2.
      WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
        client server client_ch server_ch client_sh server_sh raw1 raw1 raw2 raw2;
  assert (CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server);
  // peer_derived agrees
  CSL.lemma_handshake_peer_derived_key_material_agrees_from_paired_hellos
    CS.ServerTraffic client server;
  // final
  P.lemma_handshake_peer_record_material_server_to_client_agrees_from_hello_hsonly
    client server
#pop-options

(* ── H_mat MIRROR for client_send: peer_record_material_agrees ClientTraffic client server ── *)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 60 --split_queries always"
let lemma_pcr_hmat_client_send (client server:CS.connection_state)
    (client_ch server_ch:GCH.clientHello) (client_sh server_sh:GSH.serverHello)
  : Lemma
      (requires
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        PC.pre_appdata_control server.CS.cs_model.CS.model_control /\
        PC.pre_appdata_control client.CS.cs_model.CS.model_control /\
        client.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
        server.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        (exists raw.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw) /\
        (exists raw.
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw) /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) client server)
=
  // shapes
  lemma_consistent_write_hs_stage_shape client;
  lemma_consistent_write_hs_stage_shape server;
  SCB.lemma_consistent_record_schedule_coupling client;
  SCB.lemma_consistent_record_schedule_coupling server;
  // Some? ks_client_handshake_traffic both (client write / server read)
  assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
  assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
  // Some? ks_shared_secret both via lineage
  CSL.lemma_connection_state_consistent_handshake_key_schedule_lineage client;
  CSL.lemma_connection_state_consistent_handshake_key_schedule_lineage server;
  assert (Some? client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  // projections
  CSL.lemma_client_handshake_stable_x25519_key_share_projection client;
  assert (CS.client_x25519_key_share_projection client);
  assert (CS.ControlHandshaking? server.CS.cs_model.CS.model_control);
  assert (server.CS.cs_model.CS.model_control =!= CS.ControlHandshaking CS.HsClientHelloReceived);
  CSL.lemma_server_handshake_stable_x25519_key_share_projection server;
  assert (CS.server_x25519_key_share_projection server);
  // paired x25519
  lemma_pcr_paired_x25519 client server;
  assert (CS.paired_x25519_key_shares client server);
  // checkpoint
  eliminate exists raw1.
    CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw1 /\
    CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw1
  returns CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server
  with _p1.
    eliminate exists raw2.
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
    returns CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server
    with _p2.
      WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
        client server client_ch server_ch client_sh server_sh raw1 raw1 raw2 raw2;
  assert (CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server);
  // peer_derived agrees
  CSL.lemma_handshake_peer_derived_key_material_agrees_from_paired_hellos
    CS.ClientTraffic client server;
  // final
  P.lemma_handshake_peer_record_material_client_to_server_agrees_from_hello_hsonly
    client server
#pop-options

(* ── H_rt round-trip helpers for the server's protected handshake messages ──
   Each proves `parse_tls_message Handshake (serialize_handshake msg) == Some msg`
   from the message's wire representability, mirroring
   `WStep.lemma_ch_wire_parse_roundtrip`.  The recipient reconstructs the sent
   message at delivery through exactly this round-trip (the decode-glue). *)
#push-options "--fuel 8 --ifuel 8 --z3rlimit 40"
let lemma_ee_wire_parse_roundtrip (ee:GEE.encryptedExtensions)
  : Lemma
      (requires W.encryptedExtensions_representable ee)
      (ensures
        W.parse_tls_message T.Handshake (W.serialize_handshake (M.EncryptedExtensions ee)) ==
          Some (M.TlsHandshake (M.EncryptedExtensions ee)))
  = let fragment = W.serialize_handshake (M.EncryptedExtensions ee) in
    RVDH.lemma_serialize_handshake_encrypted_extensions ee;
    Seq.lemma_eq_elim fragment
      (LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions ee));
    LP.parse_serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions ee);
    RVDH.lemma_handshake_synth_encrypted_extensions ee;
    RVDH.lemma_ptm_handshake_some fragment (GHS.Body_encrypted_extensions ee)
      (M.EncryptedExtensions ee)
#pop-options

#push-options "--fuel 8 --ifuel 8 --z3rlimit 40"
let lemma_cv_wire_parse_roundtrip (cv:GCV.certificateVerify)
  : Lemma
      (requires W.certificateVerify_representable cv)
      (ensures
        W.parse_tls_message T.Handshake (W.serialize_handshake (M.CertificateVerify cv)) ==
          Some (M.TlsHandshake (M.CertificateVerify cv)))
  = let fragment = W.serialize_handshake (M.CertificateVerify cv) in
    RVDH.lemma_serialize_handshake_certificate_verify cv;
    Seq.lemma_eq_elim fragment
      (LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify cv));
    LP.parse_serialize GHS.handshake_serializer (GHS.Body_certificate_verify cv);
    RVDH.lemma_handshake_synth_certificate_verify cv;
    RVDH.lemma_ptm_handshake_some fragment (GHS.Body_certificate_verify cv)
      (M.CertificateVerify cv)
#pop-options

#push-options "--fuel 8 --ifuel 8 --z3rlimit 40"
let lemma_cert_wire_parse_roundtrip (cert:GCert.certificate)
  : Lemma
      (requires W.certificate_representable cert /\ GCert.certificate_bytesize cert <= 16777215)
      (ensures
        W.parse_tls_message T.Handshake (W.serialize_handshake (M.Certificate cert)) ==
          Some (M.TlsHandshake (M.Certificate cert)))
  = let fragment = W.serialize_handshake (M.Certificate cert) in
    RVDH.lemma_serialize_handshake_certificate cert;
    Seq.lemma_eq_elim fragment
      (LP.serialize GHS.handshake_serializer
        (GHS.Body_certificate (cert <: GHS.handshake_body_certificate)));
    LP.parse_serialize GHS.handshake_serializer
      (GHS.Body_certificate (cert <: GHS.handshake_body_certificate));
    RVDH.lemma_handshake_synth_certificate cert;
    RVDH.lemma_ptm_handshake_some fragment
      (GHS.Body_certificate (cert <: GHS.handshake_body_certificate)) (M.Certificate cert)
#pop-options

#push-options "--fuel 2 --ifuel 8 --z3rlimit 100 --split_queries always"
let lemma_pcr_establish_server_send
  (a b:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        server_advances a.server s' /\
        s'.CS.cs_event_log == a.server.CS.cs_event_log @ [CS.sent_tls_event sent] /\
        b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent })
      (ensures protected_channel_ready b)
  = let raw = emitted_raw out in
    WStep.lemma_serialize_all_single_wire w;
    SCB.lemma_wire_serialize_nonempty w;
    lemma_consistent_write_hs_stage_shape a.client;
    lemma_consistent_write_hs_stage_shape a.server;
    assert (CS.connection_state_consistent a.client);
    assert (CS.connection_state_consistent a.server);
    let api = CTy.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (SCP.server_api_event_matches api conn_ev /\
       SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta a.server
         ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty }) s' /\
       CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty)
    returns protected_channel_ready b
    with _pf2.
    (
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
      assert (Seq.equal raw_sent raw);
      Seq.lemma_eq_elim raw_sent raw;
      assert (B.length raw_sent > 0);
      FStar.List.Tot.Properties.lemma_append_last a.server.CS.cs_event_log [conn_ev];
      FStar.List.Tot.Properties.lemma_append_last a.server.CS.cs_event_log [CS.sent_tls_event sent];
      assert (conn_ev == CS.sent_tls_event sent);
      assert (CS.legal_event a.server.CS.cs_model (CS.sent_tls_event sent));
      assert (a.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
      assert (a.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
      assert (write_hs_stage_shape a.server.CS.cs_model);
      introduce
        ( M.TlsHandshake? sent /\
          PC.pre_appdata_control a.server.CS.cs_model.CS.model_control /\
          PC.pre_appdata_control a.client.CS.cs_model.CS.model_control /\
          a.server.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
          a.client.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake )
        ==>
        ( CS.sent_single_protected_message_seal a.server.CS.cs_model sent raw /\
          a.server.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
            a.client.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
          CS.peer_record_material_agrees
            (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic)
            a.client ({ a.client with CS.cs_model = a.server.CS.cs_model }) /\
          (let (ct, frag) = W.serialize_tls_message sent in
           W.parse_tls_message ct frag == Some sent) )
      with _g.
      (
        // H_seal : the sent handshake message is not cleartext, one protected record.
        assert (CS.network_message_is_cleartext CL.Sent sent == false);
        assert (CS.sent_single_protected_message_seal a.server.CS.cs_model sent raw);
        // H_seq : server (sender) write-seq == client (recipient) read-seq.
        SCB.lemma_hseq_from_counts a.server a.client;
        // H_mat : server (sender) -> client (recipient), ServerTraffic direction.
        assert (Some? (hsf a.client).CS.hs_client_hello);
        assert (Some? (hsf a.server).CS.hs_client_hello);
        assert (Some? (hsf a.client).CS.hs_server_hello);
        assert (Some? (hsf a.server).CS.hs_server_hello);
        assert (ch_wire_equiv a);
        assert (sh_wire_equiv a);
        assert (hello_key_shares_ok a);
        let client_ch = Some?.v (hsf a.client).CS.hs_client_hello in
        let server_ch = Some?.v (hsf a.server).CS.hs_client_hello in
        let client_sh = Some?.v (hsf a.client).CS.hs_server_hello in
        let server_sh = Some?.v (hsf a.server).CS.hs_server_hello in
        lemma_pcr_hmat_server_send a.client a.server client_ch server_ch client_sh server_sh;
        assert (CS.peer_record_material_agrees
                  (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic)
                  a.client ({ a.client with CS.cs_model = a.server.CS.cs_model }));
        // H_rt : per-message wire round-trip.  The server's four protected
        // handshake messages, each representable at the legal send.
        let hs = M.TlsHandshake?._0 sent in
        assert (sent == M.TlsHandshake hs);
        assert (CS.legal_handshake_message a.server.CS.cs_model CL.Sent hs);
        W.lemma_serialize_tls_message_handshake hs;
        match hs with
        | M.Finished fin ->
          RVDF.lemma_parse_finished_handshake fin
        | M.EncryptedExtensions ee ->
          // legal Sent-EE forces alpn == None ==> representable.
          W.lemma_encryptedExtensions_representable ee;
          lemma_ee_wire_parse_roundtrip ee
        | M.Certificate cert ->
          // legal Sent-Certificate forces certificate_representable /\ bytesize bound.
          lemma_cert_wire_parse_roundtrip cert
        | M.CertificateVerify cv ->
          // legal Sent-CV forces certificateVerify_representable.
          lemma_cv_wire_parse_roundtrip cv
        | M.ClientHello _ -> assert False
        | M.ServerHello _ -> assert False
        | M.HelloRetryRequest -> assert False
      )
    )
#pop-options

#push-options "--fuel 2 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_pcr_establish_client_send
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        client_advances a.client c' /\
        c'.CS.cs_event_log == a.client.CS.cs_event_log @ [CS.sent_tls_event sent] /\
        b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent })
      (ensures protected_channel_ready b)
  = let raw = emitted_raw out in
    WStep.lemma_serialize_all_single_wire w;
    SCB.lemma_wire_serialize_nonempty w;
    lemma_consistent_write_hs_stage_shape a.client;
    lemma_consistent_write_hs_stage_shape a.server;
    assert (CS.connection_state_consistent a.client);
    assert (CS.connection_state_consistent a.server);
    let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CCP.client_api_event_matches a.client api conn_ev /\
       CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta a.client
         ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty }) c' /\
       CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty)
    returns protected_channel_ready b
    with _pf2.
    (
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
      assert (Seq.equal raw_sent raw);
      Seq.lemma_eq_elim raw_sent raw;
      assert (B.length raw_sent > 0);
      FStar.List.Tot.Properties.lemma_append_last a.client.CS.cs_event_log [conn_ev];
      FStar.List.Tot.Properties.lemma_append_last a.client.CS.cs_event_log [CS.sent_tls_event sent];
      assert (conn_ev == CS.sent_tls_event sent);
      assert (CS.legal_event a.client.CS.cs_model (CS.sent_tls_event sent));
      assert (a.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
      assert (a.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
      assert (write_hs_stage_shape a.client.CS.cs_model);
      introduce
        ( M.TlsHandshake? sent /\
          PC.pre_appdata_control a.client.CS.cs_model.CS.model_control /\
          PC.pre_appdata_control a.server.CS.cs_model.CS.model_control /\
          a.client.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake /\
          a.server.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake )
        ==>
        ( CS.sent_single_protected_message_seal a.client.CS.cs_model sent raw /\
          a.client.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
            a.server.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
          CS.peer_record_material_agrees
            (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic)
            ({ a.server with CS.cs_model = a.client.CS.cs_model }) a.server /\
          (let (ct, frag) = W.serialize_tls_message sent in
           W.parse_tls_message ct frag == Some sent) )
      with _g.
      (
        let hs = M.TlsHandshake?._0 sent in
        assert (sent == M.TlsHandshake hs);
        match hs with
        | M.Finished fin ->
          // H_rt : Finished round-trips unconditionally.
          W.lemma_serialize_tls_message_handshake hs;
          RVDF.lemma_parse_finished_handshake fin;
          // H_seal : Finished is not a cleartext message, single protected record.
          assert (CS.network_message_is_cleartext CL.Sent sent == false);
          assert (CS.sent_single_protected_message_seal a.client.CS.cs_model sent raw);
          // H_seq
          SCB.lemma_hseq_from_counts a.client a.server;
          // H_mat : client (sender) -> server (recipient), ClientTraffic direction.
          assert (Some? (hsf a.client).CS.hs_client_hello);
          assert (Some? (hsf a.client).CS.hs_server_hello);
          assert (Some? (hsf a.server).CS.hs_client_hello);
          assert (Some? (hsf a.server).CS.hs_server_hello);
          assert (ch_wire_equiv a);
          assert (sh_wire_equiv a);
          assert (hello_key_shares_ok a);
          let client_ch = Some?.v (hsf a.client).CS.hs_client_hello in
          let server_ch = Some?.v (hsf a.server).CS.hs_client_hello in
          let client_sh = Some?.v (hsf a.client).CS.hs_server_hello in
          let server_sh = Some?.v (hsf a.server).CS.hs_server_hello in
          lemma_pcr_hmat_client_send a.client a.server client_ch server_ch client_sh server_sh;
          assert (CS.peer_record_material_agrees
                    (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic)
                    ({ a.server with CS.cs_model = a.client.CS.cs_model }) a.server)
        | M.ClientHello _ -> assert False
        | M.ServerHello _ -> assert False
        | M.EncryptedExtensions _ -> assert False
        | M.Certificate _ -> assert False
        | M.CertificateVerify _ -> assert False
        | M.HelloRetryRequest -> assert False
      )
    )
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 3a preservation helpers for the two SENDER-side bridges
    (`inflight_wire_faithful`, `inflight_protected_sender_ok`) and the incremental
    per-message replay witnesses (`incremental_protected_witnesses`) at the four
    NON-DELIVERY transitions (client/server send and local).

    First, two supporting pure lemmas.
    ───────────────────────────────────────────────────────────────────────── **)

(* SERVER write-epoch shape: a server at any pre-server-Finished-sent control
   (New / AwaitingCH / CHReceived / SHSent / ServerEncryptedFlightSent) has a
   write epoch that is not Application.  The server installs its application WRITE
   record keys via `LocalInstallTrafficKeysForRole`, legal ONLY at
   `HsServerFinishedSent`; every earlier control keeps the write epoch below
   Application.  Mirrors `client_write_hs_epoch_shape`. *)
let server_write_pre_finished_epoch (m:CS.connection_model) : prop =
  (m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
   (m.CS.model_control == CS.ControlNew \/
    m.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello \/
    m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived \/
    m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
    m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent)) ==>
    m.CS.model_record.CS.record_write.R.epoch =!= R.Application

#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_step_server_write_pre_finished_epoch
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires server_write_pre_finished_epoch m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
      (ensures server_write_pre_finished_epoch m')
  = ()
#pop-options

let lemma_delta_server_write_pre_finished_epoch (st0 st1:CS.connection_state)
  : Lemma
      (requires server_write_pre_finished_epoch st0.CS.cs_model /\ CS.connection_state_single_step st0 st1)
      (ensures server_write_pre_finished_epoch st1.CS.cs_model)
  = let delta_w =
      ID.indefinite_description_ghost
        CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_server_write_pre_finished_epoch st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_server_write_pre_finished_epoch (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures server_write_pre_finished_epoch st.CS.cs_model)
  = let p (st:CS.connection_state) = server_write_pre_finished_epoch st.CS.cs_model in
    let stable :
      squash (
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _. lemma_delta_server_write_pre_finished_epoch x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)

(* A NON-received event (a SEND or a LOCAL) does not create a handshake message
   field `None -> Some` except at the single control where the endpoint STORES
   that message.  The value-preserving locals (`LocalVerify*`) require the field
   already `Some` by their legality, so they never turn a `None` into `Some`. *)
#push-options "--fuel 4 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_nonrecv_field_none_stable
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Sent)))
      (ensures
        (let h  = m.CS.model_handshake in
         let h' = m'.CS.model_handshake in
         let c  = m.CS.model_control in
         (~(c == CS.ControlHandshaking CS.HsServerHelloSent) ==>
            (None? h.CS.hs_encrypted_extensions ==> None? h'.CS.hs_encrypted_extensions)) /\
         (~(c == CS.ControlHandshaking CS.HsServerEncryptedFlightSent) ==>
            (None? h.CS.hs_certificate ==> None? h'.CS.hs_certificate)) /\
         (~(c == CS.ControlHandshaking CS.HsServerEncryptedFlightSent) ==>
            (None? h.CS.hs_certificate_verify ==> None? h'.CS.hs_certificate_verify)) /\
         (~(c == CS.ControlHandshaking CS.HsServerEncryptedFlightSent) ==>
            (None? h.CS.hs_server_finished ==> None? h'.CS.hs_server_finished)) /\
         (~(c == CS.ControlHandshaking CS.HsServerFinishedVerified) ==>
            (None? h.CS.hs_client_finished ==> None? h'.CS.hs_client_finished))))
  = ()
#pop-options

(* A client / server LOCAL api-event matches only a `ConnLocalEvent` or a
   `Sent` network event (never a `Received` one): every non-`False` arm of
   `local_event_kind_matches` produces one of those two shapes.  Isolated so the
   ~16-arm case split runs in a small context. *)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 40"
let lemma_client_matches_local_or_sent
  (st0:CS.connection_state) (api:CTy.client_api_event) (conn_ev:CS.conn_event)
  : Lemma
      (requires CCP.client_api_event_matches st0 api conn_ev)
      (ensures
        CS.ConnLocalEvent? conn_ev \/
        (CS.ConnNetworkEvent? conn_ev /\
         (CS.ConnNetworkEvent?._0 conn_ev).CL.message_direction == CL.Sent))
  = ()

let lemma_server_matches_local_or_sent
  (api:CTy.server_api_event) (conn_ev:CS.conn_event)
  : Lemma
      (requires SCP.server_api_event_matches api conn_ev)
      (ensures
        CS.ConnLocalEvent? conn_ev \/
        (CS.ConnNetworkEvent? conn_ev /\
         (CS.ConnNetworkEvent?._0 conn_ev).CL.message_direction == CL.Sent))
  = ()
#pop-options

(* A sent Finished at a control other than HsServerEncryptedFlightSent is the
   client's Finished send at HsServerFinishedVerified: the step stores it in
   `hs_client_finished` (via the field-preserving `append_handshake_to_transcript`).
   Isolated so the step inversion runs in a small context. *)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 100 --split_queries always"
let lemma_step_sent_finished_stores_client
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent) /\
        m.CS.model_control =!= CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        CS.step_model m (CS.sent_tls_event sent) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        m'.CS.model_handshake.CS.hs_client_finished
          == Some (M.Finished?._0 (M.TlsHandshake?._0 sent)))
  = ()
#pop-options

(* Server sent-flight stores (isolated step inversions).  Each Sent handshake
   message has a unique originating control, so both the control and the stored
   field are recovered from the successful step. *)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 100 --split_queries always"
let lemma_step_sent_ee_stores_server
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? sent /\ M.EncryptedExtensions? (M.TlsHandshake?._0 sent) /\
        CS.step_model m (CS.sent_tls_event sent) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        m'.CS.model_handshake.CS.hs_encrypted_extensions
          == Some (M.EncryptedExtensions?._0 (M.TlsHandshake?._0 sent)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 100 --split_queries always"
let lemma_step_sent_cert_stores_server
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? sent /\ M.Certificate? (M.TlsHandshake?._0 sent) /\
        CS.step_model m (CS.sent_tls_event sent) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        m'.CS.model_handshake.CS.hs_certificate
          == Some (M.Certificate?._0 (M.TlsHandshake?._0 sent)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 100 --split_queries always"
let lemma_step_sent_cv_stores_server
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? sent /\ M.CertificateVerify? (M.TlsHandshake?._0 sent) /\
        CS.step_model m (CS.sent_tls_event sent) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        m'.CS.model_handshake.CS.hs_certificate_verify
          == Some (M.CertificateVerify?._0 (M.TlsHandshake?._0 sent)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 100 --split_queries always"
let lemma_step_sent_finished_stores_server
  (m m':CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? sent /\ M.Finished? (M.TlsHandshake?._0 sent) /\
        m.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.step_model m (CS.sent_tls_event sent) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        m'.CS.model_handshake.CS.hs_server_finished
          == Some (M.Finished?._0 (M.TlsHandshake?._0 sent)))
  = ()
#pop-options

(** (1) client SEND. **)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_ipw_pres_client_send
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        client_advances a.client c' /\
        c'.CS.cs_event_log == a.client.CS.cs_event_log @ [CS.sent_tls_event sent] /\
        b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent })
      (ensures
        inflight_wire_faithful b /\
        inflight_sender_coupling b /\
        inflight_protected_sender_ok b /\
        incremental_protected_witnesses b)
  = let raw = emitted_raw out in
    WStep.lemma_serialize_all_single_wire w;
    SCB.lemma_wire_serialize_nonempty w;
    lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
    let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CCP.client_api_event_matches a.client api conn_ev /\
       CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta a.client
         ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty }) c' /\
       CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty)
    returns
      (inflight_wire_faithful b /\
       inflight_sender_coupling b /\
       inflight_protected_sender_ok b /\
       incremental_protected_witnesses b)
    with _pf2.
    (
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
      assert (Seq.equal raw_sent raw);
      Seq.lemma_eq_elim raw_sent raw;
      assert (B.length raw_sent > 0);
      FStar.List.Tot.Properties.lemma_append_last a.client.CS.cs_event_log [conn_ev];
      FStar.List.Tot.Properties.lemma_append_last a.client.CS.cs_event_log [CS.sent_tls_event sent];
      assert (conn_ev == CS.sent_tls_event sent);
      let d : CS.connection_delta =
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } in
      assert (CS.legal_connection_delta a.client d c');
      introduce exists (delta:CS.connection_delta). CS.legal_connection_delta a.client delta c'
      with d and ();
      assert (CS.connection_state_single_step a.client c');
      lemma_consistent_step_vstable a.client c';
      lemma_consistent_mono_shape a.client;
      lemma_consistent_client_write_hs_epoch_shape a.client;
      SCB.lemma_consistent_record_key_epoch_coupling a.client;
      lemma_nonrecv_field_none_stable a.client.CS.cs_model c'.CS.cs_model conn_ev;
      assert (client_stage_ok a.client);
      assert (~(a.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent));
      assert (~(a.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
      // inflight_wire_faithful b
      assert (CS.sent_event_nonempty_seal_projection a.client.CS.cs_model (CS.sent_tls_event sent) raw);
      assert (CS.event_raw_delta_legal a.client.CS.cs_model conn_ev raw_sent B.empty);
      assert (CS.network_message_raw_delta_legal a.client.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      assert (inflight_wire_faithful b);
      // inflight_sender_coupling b: from legal_connection_delta a.client d c'
      // (step_model a.client.cs_model conn_ev == Some c'.cs_model, conn_ev == sent_tls_event sent;
      //  ipso_sender_endpoint b ServerEndpoint == b.client == c').
      reveal_opaque (`%inflight_sender_coupling) (inflight_sender_coupling b);
      assert (inflight_sender_coupling b);
      // incremental_protected_witnesses b
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses a);
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses b);
      assert (incremental_protected_witnesses b);
      // inflight_protected_sender_ok b (case-split on sent)
      let _ : squash (inflight_protected_sender_ok b) =
        (match sent with
         | M.TlsHandshake (M.Finished fin) ->
           lemma_step_sent_finished_stores_client a.client.CS.cs_model c'.CS.cs_model sent;
           assert (a.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
           assert (CS.sent_single_protected_message_seal a.client.CS.cs_model sent raw);
           assert (Some? a.client.CS.cs_model.CS.model_record.CS.record_write.R.key);
           assert (a.client.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake);
           assert ((hsf c').CS.hs_client_finished == Some fin)
         | M.TlsHandshake (M.EncryptedExtensions _)
         | M.TlsHandshake (M.Certificate _)
         | M.TlsHandshake (M.CertificateVerify _) ->
           assert False
         | _ -> ()) in
      ()
    )
#pop-options

(** (2) server SEND. **)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_ipw_pres_server_send
  (a b:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        server_advances a.server s' /\
        s'.CS.cs_event_log == a.server.CS.cs_event_log @ [CS.sent_tls_event sent] /\
        b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent })
      (ensures
        inflight_wire_faithful b /\
        inflight_sender_coupling b /\
        inflight_protected_sender_ok b /\
        incremental_protected_witnesses b)
  = let raw = emitted_raw out in
    WStep.lemma_serialize_all_single_wire w;
    SCB.lemma_wire_serialize_nonempty w;
    lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
    let api = CTy.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (SCP.server_api_event_matches api conn_ev /\
       SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta a.server
         ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty }) s' /\
       CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty)
    returns
      (inflight_wire_faithful b /\
       inflight_sender_coupling b /\
       inflight_protected_sender_ok b /\
       incremental_protected_witnesses b)
    with _pf2.
    (
      Seq.lemma_eq_elim (WF.serialize_all CW.tls_record_wire_format [w]) (CW.wire_serialize w);
      assert (Seq.equal raw_sent raw);
      Seq.lemma_eq_elim raw_sent raw;
      assert (B.length raw_sent > 0);
      FStar.List.Tot.Properties.lemma_append_last a.server.CS.cs_event_log [conn_ev];
      FStar.List.Tot.Properties.lemma_append_last a.server.CS.cs_event_log [CS.sent_tls_event sent];
      assert (conn_ev == CS.sent_tls_event sent);
      let d : CS.connection_delta =
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } in
      assert (CS.legal_connection_delta a.server d s');
      introduce exists (delta:CS.connection_delta). CS.legal_connection_delta a.server delta s'
      with d and ();
      assert (CS.connection_state_single_step a.server s');
      lemma_consistent_step_vstable a.server s';
      lemma_consistent_mono_shape a.server;
      lemma_consistent_server_write_pre_finished_epoch a.server;
      SCB.lemma_consistent_record_key_epoch_coupling a.server;
      lemma_nonrecv_field_none_stable a.server.CS.cs_model s'.CS.cs_model conn_ev;
      assert (server_stage_ok a.server);
      assert (~(a.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified));
      // inflight_wire_faithful b
      assert (CS.sent_event_nonempty_seal_projection a.server.CS.cs_model (CS.sent_tls_event sent) raw);
      assert (CS.event_raw_delta_legal a.server.CS.cs_model conn_ev raw_sent B.empty);
      assert (CS.network_message_raw_delta_legal a.server.CS.cs_model
                ({ CL.message_direction = CL.Sent; CL.message_value = sent }) raw_sent);
      assert (inflight_wire_faithful b);
      // inflight_sender_coupling b: from legal_connection_delta a.server d s'
      // (step_model a.server.cs_model conn_ev == Some s'.cs_model, conn_ev == sent_tls_event sent;
      //  ipso_sender_endpoint b ClientEndpoint == b.server == s').
      reveal_opaque (`%inflight_sender_coupling) (inflight_sender_coupling b);
      assert (inflight_sender_coupling b);
      // incremental_protected_witnesses b
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses a);
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses b);
      assert (incremental_protected_witnesses b);
      // inflight_protected_sender_ok b (case-split on sent)
      let _ : squash (inflight_protected_sender_ok b) =
        (match sent with
         | M.TlsHandshake (M.EncryptedExtensions ee) ->
           lemma_step_sent_ee_stores_server a.server.CS.cs_model s'.CS.cs_model sent;
           assert (a.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
           assert (CS.sent_single_protected_message_seal a.server.CS.cs_model sent raw);
           assert (Some? a.server.CS.cs_model.CS.model_record.CS.record_write.R.key);
           assert (a.server.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake);
           assert ((hsf s').CS.hs_encrypted_extensions == Some ee)
         | M.TlsHandshake (M.Certificate cert) ->
           lemma_step_sent_cert_stores_server a.server.CS.cs_model s'.CS.cs_model sent;
           assert (a.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
           assert (CS.sent_single_protected_message_seal a.server.CS.cs_model sent raw);
           assert (Some? a.server.CS.cs_model.CS.model_record.CS.record_write.R.key);
           assert (a.server.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake);
           assert ((hsf s').CS.hs_certificate == Some cert)
         | M.TlsHandshake (M.CertificateVerify cv) ->
           lemma_step_sent_cv_stores_server a.server.CS.cs_model s'.CS.cs_model sent;
           assert (a.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
           assert (CS.sent_single_protected_message_seal a.server.CS.cs_model sent raw);
           assert (Some? a.server.CS.cs_model.CS.model_record.CS.record_write.R.key);
           assert (a.server.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake);
           assert ((hsf s').CS.hs_certificate_verify == Some cv)
         | M.TlsHandshake (M.Finished fin) ->
           lemma_step_sent_finished_stores_server a.server.CS.cs_model s'.CS.cs_model sent;
           assert (a.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
           assert (CS.sent_single_protected_message_seal a.server.CS.cs_model sent raw);
           assert (Some? a.server.CS.cs_model.CS.model_record.CS.record_write.R.key);
           assert (a.server.CS.cs_model.CS.model_record.CS.record_write.R.epoch == R.Handshake);
           assert ((hsf s').CS.hs_server_finished == Some fin)
         | _ -> ()) in
      ()
    )
#pop-options

(** (3) client LOCAL. **)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_ipw_pres_client_local
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [] /\
        client_local_advances a.client c' /\
        b == { a with client = c' })
      (ensures
        inflight_wire_faithful b /\
        inflight_sender_coupling b /\
        inflight_protected_sender_ok b /\
        incremental_protected_witnesses b)
  = lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
    let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CCP.client_api_event_matches a.client api conn_ev /\
       CCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       CCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta a.client
         ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty }) c' /\
       CS.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty)
    returns
      (inflight_wire_faithful b /\
       inflight_sender_coupling b /\
       inflight_protected_sender_ok b /\
       incremental_protected_witnesses b)
    with _pf2.
    (
      WStep.lemma_serialize_all_nil_wire ();
      Seq.lemma_eq_elim raw_sent B.empty;
      let d : CS.connection_delta =
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } in
      assert (CS.legal_connection_delta a.client d c');
      assert (CS.event_raw_delta_legal a.client.CS.cs_model conn_ev raw_sent B.empty);
      lemma_client_matches_local_or_sent a.client api conn_ev;
      introduce exists (delta:CS.connection_delta). CS.legal_connection_delta a.client delta c'
      with d and ();
      assert (CS.connection_state_single_step a.client c');
      lemma_consistent_step_vstable a.client c';
      lemma_consistent_mono_shape a.client;
      lemma_nonrecv_field_none_stable a.client.CS.cs_model c'.CS.cs_model conn_ev;
      assert (client_stage_ok a.client);
      assert (~(a.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent));
      assert (~(a.client.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
      // channel frozen: b.channel == a.channel == TlsQuiet
      assert (inflight_wire_faithful a);
      assert (inflight_wire_faithful b);
      assert (TlsQuiet? b.channel);
      reveal_opaque (`%inflight_sender_coupling) (inflight_sender_coupling b);
      assert (inflight_sender_coupling b);
      assert (inflight_protected_sender_ok a);
      assert (inflight_protected_sender_ok b);
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses a);
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses b);
      assert (incremental_protected_witnesses b)
    )
#pop-options

(** (4) server LOCAL. **)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 80 --split_queries always"
let lemma_ipw_pres_server_local
  (a b:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [] /\
        server_local_advances a.server s' /\
        b == { a with server = s' })
      (ensures
        inflight_wire_faithful b /\
        inflight_sender_coupling b /\
        inflight_protected_sender_ok b /\
        incremental_protected_witnesses b)
  = lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
    let api = CTy.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (SCP.server_api_event_matches api conn_ev /\
       SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta a.server
         ({ CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
            CS.delta_raw_received = B.empty }) s' /\
       CS.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
       CS.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty)
    returns
      (inflight_wire_faithful b /\
       inflight_sender_coupling b /\
       inflight_protected_sender_ok b /\
       incremental_protected_witnesses b)
    with _pf2.
    (
      WStep.lemma_serialize_all_nil_wire ();
      Seq.lemma_eq_elim raw_sent B.empty;
      let d : CS.connection_delta =
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } in
      assert (CS.legal_connection_delta a.server d s');
      assert (CS.event_raw_delta_legal a.server.CS.cs_model conn_ev raw_sent B.empty);
      lemma_server_matches_local_or_sent api conn_ev;
      introduce exists (delta:CS.connection_delta). CS.legal_connection_delta a.server delta s'
      with d and ();
      assert (CS.connection_state_single_step a.server s');
      lemma_consistent_step_vstable a.server s';
      lemma_consistent_mono_shape a.server;
      lemma_nonrecv_field_none_stable a.server.CS.cs_model s'.CS.cs_model conn_ev;
      assert (server_stage_ok a.server);
      assert (~(a.server.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified));
      // channel frozen: b.channel == a.channel == TlsQuiet
      assert (inflight_wire_faithful a);
      assert (inflight_wire_faithful b);
      assert (TlsQuiet? b.channel);
      reveal_opaque (`%inflight_sender_coupling) (inflight_sender_coupling b);
      assert (inflight_sender_coupling b);
      assert (inflight_protected_sender_ok a);
      assert (inflight_protected_sender_ok b);
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses a);
      reveal_opaque (`%incremental_protected_witnesses) (incremental_protected_witnesses b);
      assert (incremental_protected_witnesses b)
    )
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      client_advances a.client c' /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [CS.sent_tls_event sent] /\
      b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) a.client.CS.cs_model sent }
    returns tls_system_inv b
    with _pf.
      (assert (CS.connection_state_no_key_update_trace c');
       lemma_client_step_preserves_stage_ok a.client c' (SM.LocalEvent local) out;
       lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_client_step_len_micro a.client c' (SM.LocalEvent local) out;
       lemma_client_step_ksp a.client c' (SM.LocalEvent local) out;
       lemma_client_step_e2e a.client c' (SM.LocalEvent local) out;
       lemma_bp_client_send a local c' out w sent;
       lemma_wire_facts_client_send a b;
       lemma_pw_pres_client_send a b local c' out w sent;
       lemma_scop_client_send a b;
       lemma_pcr_establish_client_send a b local c' out w sent;
       lemma_ipw_pres_client_send a b local c' out w sent)
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_send a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      SCP.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      server_advances a.server s' /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [CS.sent_tls_event sent] /\
      b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) a.server.CS.cs_model sent }
    returns tls_system_inv b
    with _pf.
      (assert (CS.connection_state_no_key_update_trace s');
       lemma_server_step_preserves_stage_ok a.server s' (SM.LocalEvent local) out;
       lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_server_step_len_micro a.server s' (SM.LocalEvent local) out;
       lemma_server_step_ksp a.server s' (SM.LocalEvent local) out;
       lemma_server_step_e2e a.server s' (SM.LocalEvent local) out;
       lemma_bp_server_send a local s' out w sent;
       lemma_wire_facts_server_send a b;
       lemma_pw_pres_server_send a b local s' out w sent;
       lemma_scop_server_send a b;
       lemma_pcr_establish_server_send a b local s' out w sent;
       lemma_ipw_pres_server_send a b local s' out w sent)
#pop-options

(** Ready-couple discharge — the single-endpoint reachability-inversion chain.
    A quiescent system with a ready client forces the server past client-Finished
    receipt: the ready client has SENT its protected (ApplicationData) Finished;
    the quiet byte-pairing transfers that record to the server's received log; and
    a server that received an ApplicationData record is at/after CF receipt.  This
    is packaged as a standalone lemma so the fragile monolithic preservation
    queries stay small and deterministic. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_ready_couple_post_cf (s:tls_system_state)
  : Lemma (requires
            client_byte_reachable s /\
            server_byte_reachable s /\
            byte_pairing s /\
            TlsQuiet? s.channel /\
            s.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
            s.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
            client_ready s)
          (ensures server_post_cf s)
  = WStep.lemma_client_ready_sent_has_appdata_record
      s.client.CS.cs_model.CS.model_config s.client;
    WStep.lemma_raw_has_appdata_record_seq_equal
      s.client.CS.cs_wire_log.CL.raw_sent
      s.server.CS.cs_wire_log.CL.raw_received;
    WStep.lemma_server_received_appdata_record_implies_post_cf
      s.server.CS.cs_model.CS.model_config s.server
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 3a — the two protected DELIVERY helpers.  Post-state channel is quiet,
    so `inflight_wire_faithful`, `inflight_sender_coupling`, and
    `inflight_protected_sender_ok` are vacuous; the real work is the fresh
    per-message replay witness in `incremental_protected_witnesses`.
    ───────────────────────────────────────────────────────────────────────── **)

(** ══════════ PORTED PURE HELPERS (verified in /tmp/scratch) ══════════ **)

(* Two decodes of the same raw record under the same model yield the same message. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries always"
let lemma_received_single_protected_message_decode_unique
  (model:CS.connection_model) (m1 m2:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        CS.received_single_protected_message_decode model m1 raw /\
        CS.received_single_protected_message_decode model m2 raw)
      (ensures m1 == m2)
  = ()
#pop-options

(* Receive-step inversions (client side). *)
#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_step_recv_ee_stores_client
  (m m':CS.connection_model) (received:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? received /\ M.EncryptedExtensions? (M.TlsHandshake?._0 received) /\
        CS.step_model m (CS.received_tls_event received) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        m'.CS.model_handshake.CS.hs_encrypted_extensions
          == Some (M.EncryptedExtensions?._0 (M.TlsHandshake?._0 received)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_step_recv_cert_stores_client
  (m m':CS.connection_model) (received:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? received /\ M.Certificate? (M.TlsHandshake?._0 received) /\
        CS.step_model m (CS.received_tls_event received) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
        m'.CS.model_handshake.CS.hs_certificate
          == Some (M.Certificate?._0 (M.TlsHandshake?._0 received)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_step_recv_cv_stores_client
  (m m':CS.connection_model) (received:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? received /\ M.CertificateVerify? (M.TlsHandshake?._0 received) /\
        CS.step_model m (CS.received_tls_event received) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated /\
        m'.CS.model_handshake.CS.hs_certificate_verify
          == Some (M.CertificateVerify?._0 (M.TlsHandshake?._0 received)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_step_recv_finished_stores_server_finished
  (m m':CS.connection_model) (received:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? received /\ M.Finished? (M.TlsHandshake?._0 received) /\
        m.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedSent /\
        CS.step_model m (CS.received_tls_event received) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
        m'.CS.model_handshake.CS.hs_server_finished
          == Some (M.Finished?._0 (M.TlsHandshake?._0 received)))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_step_recv_finished_stores_client_finished
  (m m':CS.connection_model) (received:M.tls_message)
  : Lemma
      (requires
        M.TlsHandshake? received /\ M.Finished? (M.TlsHandshake?._0 received) /\
        m.CS.model_control =!= CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
        CS.step_model m (CS.received_tls_event received) == Some m')
      (ensures
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        m'.CS.model_handshake.CS.hs_client_finished
          == Some (M.Finished?._0 (M.TlsHandshake?._0 received)))
  = ()
#pop-options

(* Field-map contrapositive lemmas. *)
#push-options "--fuel 3 --ifuel 8 --z3rlimit 200 --split_queries always"
let fm_client (m m':CS.connection_model) (received:M.tls_message)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsServerFinishedSent /\
                    CS.step_model m (CS.received_tls_event received) == Some m')
          (ensures (
        let h  = m.CS.model_handshake in
        let h' = m'.CS.model_handshake in
        (~(M.TlsHandshake? received /\ M.EncryptedExtensions? (M.TlsHandshake?._0 received)) ==>
           h'.CS.hs_encrypted_extensions == h.CS.hs_encrypted_extensions) /\
        (~(M.TlsHandshake? received /\ M.Certificate? (M.TlsHandshake?._0 received)) ==>
           h'.CS.hs_certificate == h.CS.hs_certificate) /\
        (~(M.TlsHandshake? received /\ M.CertificateVerify? (M.TlsHandshake?._0 received)) ==>
           h'.CS.hs_certificate_verify == h.CS.hs_certificate_verify) /\
        (~(M.TlsHandshake? received /\ M.Finished? (M.TlsHandshake?._0 received)) ==>
           h'.CS.hs_server_finished == h.CS.hs_server_finished) /\
        h'.CS.hs_client_finished == h.CS.hs_client_finished))
  = ()
#pop-options

#push-options "--fuel 3 --ifuel 8 --z3rlimit 200 --split_queries always"
let fm_server (m m':CS.connection_model) (received:M.tls_message)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsServerHelloReceived /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsCertificateReceived /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsCertificateValidated /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                    m.CS.model_control =!= CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
                    CS.step_model m (CS.received_tls_event received) == Some m')
          (ensures (
        let h  = m.CS.model_handshake in
        let h' = m'.CS.model_handshake in
        h'.CS.hs_encrypted_extensions == h.CS.hs_encrypted_extensions /\
        h'.CS.hs_certificate == h.CS.hs_certificate /\
        h'.CS.hs_certificate_verify == h.CS.hs_certificate_verify /\
        h'.CS.hs_server_finished == h.CS.hs_server_finished /\
        (~(M.TlsHandshake? received /\ M.Finished? (M.TlsHandshake?._0 received)) ==>
           h'.CS.hs_client_finished == h.CS.hs_client_finished)))
  = ()
#pop-options

(* Client read-epoch shape + RTC lift. *)
let client_read_pre_appdata_epoch_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  (m.CS.model_control == CS.ControlNew \/
   m.CS.model_control == CS.ControlHandshaking CS.HsStarted \/
   m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent \/
   m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived \/
   m.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived \/
   m.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived \/
   m.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated \/
   m.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived \/
   m.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified)
  ==> m.CS.model_record.CS.record_read.R.epoch =!= R.Application

#push-options "--fuel 2 --ifuel 4 --z3rlimit 200 --split_queries always"
let lemma_step_client_read_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires client_read_pre_appdata_epoch_shape m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
          (ensures client_read_pre_appdata_epoch_shape m')
  = ()
#pop-options

let lemma_delta_client_read_shape (st0 st1:CS.connection_state)
  : Lemma (requires client_read_pre_appdata_epoch_shape st0.CS.cs_model /\ CS.connection_state_single_step st0 st1)
          (ensures client_read_pre_appdata_epoch_shape st1.CS.cs_model)
  = let delta_w = ID.indefinite_description_ghost CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_client_read_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_client_read_shape (st:CS.connection_state)
  : Lemma (requires CS.connection_state_consistent st)
          (ensures client_read_pre_appdata_epoch_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = client_read_pre_appdata_epoch_shape st.CS.cs_model in
    let stable : squash (forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _. lemma_delta_client_read_shape x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_client_read_epoch_handshake
  (st:CS.connection_state) (msg:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        (st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived \/
         st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived \/
         st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated \/
         st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified) /\
        CS.received_single_protected_message_decode st.CS.cs_model msg raw)
      (ensures st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake)
  = lemma_consistent_client_read_shape st;
    SCB.lemma_consistent_record_key_epoch_coupling st;
    let rr = st.CS.cs_model.CS.model_record.CS.record_read in
    eliminate exists outer opened plaintext.
        W.parse_record_wire raw == Some (T.Application_data, outer, B.length raw) /\
        CS.received_record_opened st.CS.cs_model raw outer opened /\
        W.parse_plaintext opened == Some plaintext /\
        W.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg
    returns rr.R.epoch == R.Handshake
    with _pf.
    ( eliminate exists read_state'.
        R.open_record rr (CS.record_header_aad raw) outer == Some (opened, read_state')
      returns rr.R.epoch == R.Handshake
      with _pf2.
      ( assert (Some? rr.R.key) ) )
#pop-options

(* Server read-epoch shape + RTC lift. *)
let server_read_pre_appdata_epoch_shape (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  (m.CS.model_control == CS.ControlNew \/
   m.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello \/
   m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived \/
   m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
   m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
   m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
  ==> m.CS.model_record.CS.record_read.R.epoch =!= R.Application

#push-options "--fuel 2 --ifuel 4 --z3rlimit 200 --split_queries always"
let lemma_step_server_read_shape
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma (requires server_read_pre_appdata_epoch_shape m /\ CS.legal_event m ev /\ CS.step_model m ev == Some m')
          (ensures server_read_pre_appdata_epoch_shape m')
  = ()
#pop-options

let lemma_delta_server_read_shape (st0 st1:CS.connection_state)
  : Lemma (requires server_read_pre_appdata_epoch_shape st0.CS.cs_model /\ CS.connection_state_single_step st0 st1)
          (ensures server_read_pre_appdata_epoch_shape st1.CS.cs_model)
  = let delta_w = ID.indefinite_description_ghost CS.connection_delta
        (fun delta -> CS.legal_connection_delta st0 delta st1) in
    let delta : CS.connection_delta = delta_w in
    assert (CS.legal_connection_delta st0 delta st1);
    lemma_step_server_read_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_consistent_server_read_shape (st:CS.connection_state)
  : Lemma (requires CS.connection_state_consistent st)
          (ensures server_read_pre_appdata_epoch_shape st.CS.cs_model)
  = let p (st:CS.connection_state) = server_read_pre_appdata_epoch_shape st.CS.cs_model in
    let stable : squash (forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern (p y); (CS.connection_state_single_step x y)}
          p x /\ CS.connection_state_single_step x y ==> p y) =
      introduce forall (x:CS.connection_state) (y:CS.connection_state).
        p x /\ CS.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _. lemma_delta_server_read_shape x y in
    RTC.stable_on_closure CS.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
let lemma_server_read_epoch_handshake
  (st:CS.connection_state) (msg:M.tls_message) (raw:B.bytes)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        st.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        CS.received_single_protected_message_decode st.CS.cs_model msg raw)
      (ensures st.CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake)
  = lemma_consistent_server_read_shape st;
    SCB.lemma_consistent_record_key_epoch_coupling st;
    let rr = st.CS.cs_model.CS.model_record.CS.record_read in
    eliminate exists outer opened plaintext.
        W.parse_record_wire raw == Some (T.Application_data, outer, B.length raw) /\
        CS.received_record_opened st.CS.cs_model raw outer opened /\
        W.parse_plaintext opened == Some plaintext /\
        W.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg
    returns rr.R.epoch == R.Handshake
    with _pf.
    ( eliminate exists read_state'.
        R.open_record rr (CS.record_header_aad raw) outer == Some (opened, read_state')
      returns rr.R.epoch == R.Handshake
      with _pf2.
      ( assert (Some? rr.R.key) ) )
#pop-options

(** ══════════ END PORTED PURE HELPERS ══════════ **)

#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_ipw_pres_deliver_to_client
  (a b:tls_system_state)
  (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        CCP.client_step a.client (SM.WireEvent wire) c' out /\
        client_advances a.client c' /\
        b == { a with client = c'; channel = TlsQuiet })
      (ensures
        inflight_wire_faithful b /\
        inflight_sender_coupling b /\
        inflight_protected_sender_ok b /\
        incremental_protected_witnesses b)
  = // STOP-AND-REPORT (blocked obligation, per task HARD CONSTRAINTS 1 & 2).
    //
    // Post channel is TlsQuiet, so inflight_wire_faithful/inflight_sender_coupling/
    // inflight_protected_sender_ok(b) are vacuously True (dispatch as in the local
    // templates). The residual is `incremental_protected_witnesses b` in the BUILD
    // branch (the client freshly stores a protected handshake field F=Some v from
    // decoding the in-flight record `raw`). That clause is keyed (client F, server F);
    // to discharge it one must EXCLUDE the case where the ghost in-flight label
    // `sent` is a FATAL alert, i.e. prove the gateway `M.TlsHandshake? sent`.
    //
    // TRACTABLE sub-cases of the gateway (all closable from retained conjuncts):
    //   * sent a HANDSHAKE: a.server sits at a pre_appdata handshaking control, so
    //     protected_channel_ready's guard {TlsHandshake? sent; pre_appdata snap;
    //     pre_appdata client; snap.write.epoch=Handshake; client.read.epoch=Handshake}
    //     holds and yields snap.write.seq == a.client.read.seq + material + roundtrip;
    //     seal->decode + decode-uniqueness pin sent==msg and build the projection_pair.
    //   * sent CLEARTEXT (ClientHello/ServerHello/HRR/CCS): inflight_wire_faithful's
    //     cleartext clause forces `raw` to a Handshake/CCS content record, contradicting
    //     `raw` being an Application_data record (from the client's protected decode).
    //   * sent = AppData / KeyUpdate / IgnoredPostHandshake / Close_notify: legal (via
    //     step_model, from inflight_sender_coupling) only at ControlApplicationData, ruled
    //     out by byte_pairing counting (client at a build control sent 0 appdata => server
    //     received 0 => server not at ControlApplicationData); the Requested/Ignored sub
    //     cases give step_model == None, contradicting the coupling's == Some.
    //
    // BLOCKED sub-case: sent = FATAL alert (M.TlsAlert, not Close_notify). step_model snap
    // (Sent alert) == fail_model snap (ConnectionState.fst:1116/2100), preserving the record,
    // so a.server.write == snap.write and a.server is at ControlFailed. In the BUILD branch
    // the client decoded `raw` to a HANDSHAKE; the ONLY way to contradict that (for an alert
    // label) is the crypto identity open(seal)=pt (Record.Spec lemma_open_record_after_seal_
    // peer), which REQUIRES the seq alignment
    //     snap.write.seq == a.client.read.seq                                    (*)
    // Indeed if (*) held, crypto correctness would force the client's open to yield the ALERT
    // plaintext (content_type Alert), contradicting the BUILD premise (decode == handshake);
    // so the BUILD branch forces MISalignment. Retained conjuncts cannot resolve this:
    //   - protected_channel_ready carries snap.write.seq == recip.read.seq but GUARDED by
    //     `M.TlsHandshake? sent`, false for an alert (circular with the goal).
    //   - SCB.seq_count_ok_pair's pwrite_ok is GATED on pre_appdata_control; a.server at
    //     ControlFailed => vacuous, no write-seq/appdata-count relation for a.server.
    //   - inflight_protected_sender_ok's alert arm is `_ -> True`; inflight_wire_faithful pins
    //     raw as a seal at snap.write.seq but with no numeric value.
    //   - server_byte_reachable (RTC of the RAW legal_connection_delta, which DOES admit a
    //     wire-appending Sent(alert) as an Application_data record, ConnectionState.fst:3770)
    //     yields only the forward-inductive DISJUNCTION, at ControlFailed/handshake write
    //     epoch, write.seq == raw_appdata_count(raw_sent)  \/  == raw_appdata_count(raw_sent)-1
    //     (the `-1` = failed via a wire-appending protected Sent(alert); the plain `=` = failed
    //     via an empty-wire LocalFail or a receive). The fatal-alert FAIL-MODE is erased by
    //     fail_model (it drops the pre-fail control) and is NOT a function of the reachable
    //     STATE, so the disjunction is unresolvable; with byte_pairing (ss == cr ++ raw) the
    //     two branches give snap.write.seq == a.client.read.seq (aligned) resp. +1 (misaligned).
    // Under the forced-MISaligned BUILD branch, `raw` would have to be simultaneously the
    // client-decoded handshake record AND seal(snap.write, alert): refuting that needs a
    // seal/open injectivity-in-nonce axiom (a FORBIDDEN crypto strengthening; Crypto.Spec.fsti
    // exposes correctness ONLY, no authenticity/injectivity). Pinning (*) instead needs a
    // receiver-facing coupling conjunct in tls_system_inv (a FORBIDDEN 5th conjunct). No
    // forbidden-device-free discharge exists. Left admitted; reported to the project lead.
    admit ()
#pop-options

#push-options "--fuel 2 --ifuel 6 --z3rlimit 80 --split_queries always"
let lemma_ipw_pres_deliver_to_server
  (a b:tls_system_state)
  (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        a.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        SCP.server_step a.server (SM.WireEvent wire) s' out /\
        server_advances a.server s' /\
        b == { a with server = s'; channel = TlsQuiet })
      (ensures
        inflight_wire_faithful b /\
        inflight_sender_coupling b /\
        inflight_protected_sender_ok b /\
        incremental_protected_witnesses b)
  = // STOP-AND-REPORT (blocked obligation, symmetric to lemma_ipw_pres_deliver_to_client).
    //
    // Post channel is TlsQuiet, so the three inflight_* conjuncts of b are vacuous.
    // Residual: `incremental_protected_witnesses b`, BUILD branch = the client-Finished
    // clause (#5); the server freshly stores hs_client_finished from decoding `raw`. The
    // 4 server clauses transport. As on the client side, discharging the client-Finished
    // clause requires the gateway `M.TlsHandshake? sent` for the ghost in-flight label.
    //
    // Roles swapped: sender = client, receiver = server; a.channel == TlsInFlight
    // ServerEndpoint raw snap sent; protected_channel_ready's ServerEndpoint branch uses
    // ClientTraffic material; byte_pairing's ServerEndpoint branch is `cs == sr ++ raw`.
    // Tractable gateway sub-cases (handshake / cleartext / appdata-keyupdate-close) close
    // exactly as on the client side.
    //
    // BLOCKED sub-case identical in shape: sent = FATAL alert (M.TlsAlert, not Close_notify).
    // step_model snap (Sent alert) == fail_model snap, so a.client.write == snap.write and
    // a.client is at ControlFailed. In the BUILD branch the server decoded `raw` to a
    // HANDSHAKE (the client Finished); contradicting that for an alert label needs the crypto
    // identity open(seal)=pt (Record.Spec lemma_open_record_after_seal_peer), which REQUIRES
    //     snap.write.seq == a.server.read.seq                                    (*)
    // If (*) held, crypto correctness would force the server's open to yield the ALERT
    // plaintext, contradicting the BUILD premise (decode == handshake); so the BUILD branch
    // forces MISalignment. Retained conjuncts cannot resolve this:
    //   - protected_channel_ready's alignment is guarded by `M.TlsHandshake? sent` (circular);
    //   - SCB.seq_count_ok_pair's pwrite_ok is gated off at the sender's ControlFailed;
    //   - server_byte_reachable (RTC of the RAW legal_connection_delta, which DOES admit a
    //     wire-appending Sent(alert) as an Application_data record) yields only the forward-
    //     inductive DISJUNCTION, at ControlFailed/handshake write epoch, write.seq ==
    //     raw_appdata_count(raw_sent)  \/  == raw_appdata_count(raw_sent)-1 (the `-1` = failed
    //     via a wire-appending protected Sent(alert); the plain `=` = failed via empty-wire
    //     LocalFail or a receive). The fail-mode is erased by fail_model and is not a function
    //     of the reachable STATE, so the disjunction is unresolvable; with byte_pairing
    //     (cs == sr ++ raw) the branches give snap.write.seq == a.server.read.seq resp. +1.
    // Under the forced-MISaligned BUILD branch, `raw` would have to be simultaneously the
    // server-decoded handshake record AND seal(snap.write, alert): refuting that needs a
    // seal/open injectivity-in-nonce axiom (FORBIDDEN crypto strengthening); pinning (*) needs
    // a receiver-facing 5th conjunct in tls_system_inv (FORBIDDEN). No forbidden-device-free
    // discharge exists. Left admitted; reported to the project lead.
    admit ()
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pres_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      SCP.server_step a.server (SM.WireEvent wire) s' out /\
      server_advances a.server s' /\
      b == { a with server = s'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (assert (CS.connection_state_no_key_update_trace s');
       lemma_server_step_preserves_stage_ok a.server s' (SM.WireEvent wire) out;
       lemma_server_step_pres a.server s' (SM.WireEvent wire) out;
       lemma_server_step_shape a.server s' (SM.WireEvent wire) out;
       lemma_server_reach_pres a s' (SM.WireEvent wire) out;
       lemma_server_step_len_micro a.server s' (SM.WireEvent wire) out;
       lemma_server_step_ksp a.server s' (SM.WireEvent wire) out;
       lemma_server_step_e2e a.server s' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_server a wire s' out raw snap sent;
       lemma_wire_facts_deliver_to_server a b;
       lemma_pw_pres_deliver_to_server a b wire s' out;
       lemma_scop_deliver_to_server a b;
       lemma_ipw_pres_deliver_to_server a b wire s' out raw snap sent;
       assert (TlsQuiet? b.channel);
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pres_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                    (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
                    (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      CCP.client_step a.client (SM.WireEvent wire) c' out /\
      client_advances a.client c' /\
      b == { a with client = c'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (assert (CS.connection_state_no_key_update_trace c');
       lemma_client_step_preserves_stage_ok a.client c' (SM.WireEvent wire) out;
       lemma_client_step_pres a.client c' (SM.WireEvent wire) out;
       lemma_client_step_shape a.client c' (SM.WireEvent wire) out;
       lemma_client_reach_pres a c' (SM.WireEvent wire) out;
       lemma_client_step_len_micro a.client c' (SM.WireEvent wire) out;
       lemma_client_step_ksp a.client c' (SM.WireEvent wire) out;
       lemma_client_step_e2e a.client c' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_client a wire c' out raw snap sent;
       lemma_wire_facts_deliver_to_client a b;
       lemma_pw_pres_deliver_to_client a b wire c' out;
       lemma_scop_deliver_to_client a b;
       lemma_ipw_pres_deliver_to_client a b wire c' out raw snap sent;
       assert (TlsQuiet? b.channel);
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_local a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      client_local_advances a.client c' /\
      b == { a with client = c' }
    returns tls_system_inv b
    with _pf.
      (assert (CS.connection_state_no_key_update_trace c');
       lemma_client_step_preserves_stage_ok a.client c' (SM.LocalEvent local) out;
       lemma_client_local_advances_to_advances a.client c' local out;
       lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_client_step_len_micro a.client c' (SM.LocalEvent local) out;
       lemma_client_step_ksp a.client c' (SM.LocalEvent local) out;
       lemma_client_step_e2e a.client c' (SM.LocalEvent local) out;
       lemma_bp_client_local a local c' out;
       lemma_wire_facts_client_local a b;
       lemma_pw_pres_client_local a b local c' out;
       lemma_scop_client_local a b;
       lemma_ipw_pres_client_local a b local c' out;
       assert (TlsQuiet? b.channel);
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_local a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      SCP.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      server_local_advances a.server s' /\
      b == { a with server = s' }
    returns tls_system_inv b
    with _pf.
      (assert (CS.connection_state_no_key_update_trace s');
       lemma_server_step_preserves_stage_ok a.server s' (SM.LocalEvent local) out;
       lemma_server_local_advances_to_advances a.server s' local out;
       lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_server_step_len_micro a.server s' (SM.LocalEvent local) out;
       lemma_server_step_ksp a.server s' (SM.LocalEvent local) out;
       lemma_server_step_e2e a.server s' (SM.LocalEvent local) out;
       lemma_bp_server_local a local s' out;
       lemma_wire_facts_server_local a b;
       lemma_pw_pres_server_local a b local s' out;
       lemma_scop_server_local a b;
       lemma_ipw_pres_server_local a b local s' out;
       assert (TlsQuiet? b.channel);
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_no_ku_backward_client_send (x y:tls_system_state)
  : Lemma (requires tls_step_client_send x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      CCP.client_step x.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      client_advances x.client c' /\
      y == { x with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) x.client.CS.cs_model sent }
    returns tls_no_rekeying x
    with _pf. lemma_client_step_no_ku_backward x.client c' (SM.LocalEvent local) out

let lemma_no_ku_backward_server_send (x y:tls_system_state)
  : Lemma (requires tls_step_server_send x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      SCP.server_step x.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      server_advances x.server s' /\
      y == { x with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) x.server.CS.cs_model sent }
    returns tls_no_rekeying x
    with _pf. lemma_server_step_no_ku_backward x.server s' (SM.LocalEvent local) out

let lemma_no_ku_backward_deliver_to_client (x y:tls_system_state)
  : Lemma (requires tls_step_deliver_to_client x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      x.channel == TlsInFlight CS.ClientEndpoint raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      CCP.client_step x.client (SM.WireEvent wire) c' out /\
      client_advances x.client c' /\
      y == { x with client = c'; channel = TlsQuiet }
    returns tls_no_rekeying x
    with _pf. lemma_client_step_no_ku_backward x.client c' (SM.WireEvent wire) out

let lemma_no_ku_backward_deliver_to_server (x y:tls_system_state)
  : Lemma (requires tls_step_deliver_to_server x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      x.channel == TlsInFlight CS.ServerEndpoint raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      SCP.server_step x.server (SM.WireEvent wire) s' out /\
      server_advances x.server s' /\
      y == { x with server = s'; channel = TlsQuiet }
    returns tls_no_rekeying x
    with _pf. lemma_server_step_no_ku_backward x.server s' (SM.WireEvent wire) out

let lemma_no_ku_backward_client_local (x y:tls_system_state)
  : Lemma (requires tls_step_client_local x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      CCP.client_step x.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      client_local_advances x.client c' /\
      y == { x with client = c' }
    returns tls_no_rekeying x
    with _pf. lemma_client_step_no_ku_backward x.client c' (SM.LocalEvent local) out

let lemma_no_ku_backward_server_local (x y:tls_system_state)
  : Lemma (requires tls_step_server_local x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      SCP.server_step x.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      server_local_advances x.server s' /\
      y == { x with server = s' }
    returns tls_no_rekeying x
    with _pf. lemma_server_step_no_ku_backward x.server s' (SM.LocalEvent local) out

(** System-level backward monotonicity of no-rekeying: any single system step
    appends one event to the acting endpoint's log; if the post-state has no
    key-update, neither does the pre-state.  Case-split over the six transitions,
    each discharged by the per-transition backward lemma. **)
let lemma_no_key_update_backward (x y:tls_system_state)
  : Lemma (requires tls_sys_step x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = FStar.Classical.move_requires_2 lemma_no_ku_backward_client_send x y;
    FStar.Classical.move_requires_2 lemma_no_ku_backward_server_send x y;
    FStar.Classical.move_requires_2 lemma_no_ku_backward_deliver_to_client x y;
    FStar.Classical.move_requires_2 lemma_no_ku_backward_deliver_to_server x y;
    FStar.Classical.move_requires_2 lemma_no_ku_backward_client_local x y;
    FStar.Classical.move_requires_2 lemma_no_ku_backward_server_local x y
#pop-options

(** The combined invariant that IS inductive under the now-rekey-permitting step:
    if the state has not rekeyed, then it satisfies the structural invariant.
    Backward monotonicity of no-rekeying + guard recovery make this inductive. **)
let combined_inv (s:tls_system_state) : prop =
  tls_no_rekeying s ==> tls_system_inv s

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_inv_preserved (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_sys_step a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = FStar.Classical.move_requires_2 lemma_pres_client_send a b;
    FStar.Classical.move_requires_2 lemma_pres_server_send a b;
    FStar.Classical.move_requires_2 lemma_pres_deliver_to_client a b;
    FStar.Classical.move_requires_2 lemma_pres_deliver_to_server a b;
    FStar.Classical.move_requires_2 lemma_pres_client_local a b;
    FStar.Classical.move_requires_2 lemma_pres_server_local a b
#pop-options

(** The combined invariant is inductive: given `combined_inv x` and a step to `y`,
    if `y` has not rekeyed then (by backward monotonicity) neither has `x`, so
    `tls_system_inv x` holds; the recovered no-rekeying guard on `y` then feeds the
    existing guarded preservation lemma to conclude `tls_system_inv y`. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_combined_inv_preserved (x y:tls_system_state)
  : Lemma (requires combined_inv x /\ tls_sys_step x y)
          (ensures combined_inv y)
  = introduce tls_no_rekeying y ==> tls_system_inv y
    with _nr.
      (lemma_no_key_update_backward x y;
       lemma_inv_preserved x y)
#pop-options

(** At the initial state the structural invariant holds unconditionally, so the
    combined invariant holds too. **)
let lemma_initial_combined_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c)
      (ensures combined_inv (initial_tls_system cfg_c cfg_s))
  = lemma_initial_inv cfg_c cfg_s

(** Reachable states that have not rekeyed satisfy the invariant. **)
val lemma_reachable_inv (cfg_c cfg_s:CS.connection_config) (s:tls_system_state)
  : Lemma (requires cfg_c.CS.config_role == CS.ClientEndpoint /\
                    cfg_s.CS.config_role == CS.ServerEndpoint /\
                    WFL.supported_client_config_wire_profile cfg_c /\
                    tls_no_rekeying s /\
                    RTC.closure tls_sys_step (initial_tls_system cfg_c cfg_s) s)
          (ensures tls_system_inv s)
let lemma_reachable_inv cfg_c cfg_s s =
  lemma_initial_combined_inv cfg_c cfg_s;
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 lemma_combined_inv_preserved);
  RTC.stable_on_closure tls_sys_step combined_inv ()

(** ─────────────────────────────────────────────────────────────────────────
    The payoff at a completed, quiescent state.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
val lemma_ready_quiescent_agrees (s:tls_system_state)
  : Lemma (requires tls_system_inv s /\ tls_quiescent s /\ tls_application_ready s)
          (ensures CS.supported_profile_application_record_material_agrees s.client s.server)
let lemma_ready_quiescent_agrees s =
  let hc = hsf s.client in
  let hv = hsf s.server in
  // application_ready pins both controls to ControlApplicationData, so the stage
  // predicates force all seven paired fields present on both sides.
  assert (ctrl s.client == CS.ControlApplicationData);
  assert (ctrl s.server == CS.ControlApplicationData);
  assert (Some? hc.CS.hs_client_hello /\ Some? hc.CS.hs_server_hello);
  assert (Some? hv.CS.hs_client_hello /\ Some? hv.CS.hs_server_hello);
  // ── Read FACT 4 (protected-flight projection witnesses) from the invariant. ──
  // `tls_application_ready` gives `client_ready s /\ server_ready s`, and the
  // invariant conjunct `protected_witnesses_ok s` then yields the witnesses
  // directly — no on-demand clean16 byte-trace derivation is needed here (it was
  // discharged once, at the server-verify establishment instant, and preserved).
  reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok s);
  assert (client_ready s /\ server_ready s);
  assert (P.paired_protected_handshake_event_projection_pair_witnesses s.client s.server);
  match hc.CS.hs_client_hello, hv.CS.hs_client_hello,
        hc.CS.hs_server_hello, hv.CS.hs_server_hello with
  | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
    eliminate exists raw1.
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw1 /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw1
    returns CS.supported_profile_application_record_material_agrees s.client s.server
    with _p1.
      eliminate exists raw2.
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
      returns CS.supported_profile_application_record_material_agrees s.client s.server
      with _p2.
        P.lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_protected_event_projection_witnesses
          s.client s.server client_ch server_ch client_sh server_sh
          raw1 raw1 raw2 raw2
  | _ -> ()
#pop-options



(** VALIDATION — the conjunct yields the decode-glue precondition-conjunction.
    Under the full guard `G`, `protected_channel_ready` delivers a witness `msg`
    and a synthesized sender state (`cs_model == snapshot`) satisfying exactly the
    hypotheses of the Pairing decode-glue lemmas. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_protected_channel_ready_yields_decode_inputs (s:tls_system_state)
  : Lemma
      (requires
        protected_channel_ready s /\ TlsInFlight? s.channel /\
        M.TlsHandshake? (TlsInFlight?.sent s.channel) /\
        PC.pre_appdata_control (TlsInFlight?.sender_snapshot s.channel).CS.model_control /\
        PC.pre_appdata_control
          (recipient_state s (TlsInFlight?.recipient s.channel)).CS.cs_model.CS.model_control /\
        (TlsInFlight?.sender_snapshot s.channel).CS.model_record.CS.record_write.R.epoch == R.Handshake /\
        (recipient_state s (TlsInFlight?.recipient s.channel)).CS.cs_model.CS.model_record.CS.record_read.R.epoch == R.Handshake)
      (ensures
        (let recip = recipient_state s (TlsInFlight?.recipient s.channel) in
         let snapshot = TlsInFlight?.sender_snapshot s.channel in
         let raw = TlsInFlight?.raw s.channel in
         exists (msg:M.tls_message) (sender_st:CS.connection_state).
           sender_st.CS.cs_model == snapshot /\
           (match TlsInFlight?.recipient s.channel with
            | CS.ClientEndpoint ->
              CS.peer_record_material_agrees (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) recip sender_st /\
              sender_st.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
                recip.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
              CS.sent_single_protected_message_seal sender_st.CS.cs_model msg raw /\
              (let (ct, frag) = W.serialize_tls_message msg in W.parse_tls_message ct frag == Some msg)
            | CS.ServerEndpoint ->
              CS.peer_record_material_agrees (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) sender_st recip /\
              sender_st.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
                recip.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
              CS.sent_single_protected_message_seal sender_st.CS.cs_model msg raw /\
              (let (ct, frag) = W.serialize_tls_message msg in W.parse_tls_message ct frag == Some msg))))
  = let recipient = TlsInFlight?.recipient s.channel in
    let recip = recipient_state s recipient in
    let snapshot = TlsInFlight?.sender_snapshot s.channel in
    let raw = TlsInFlight?.raw s.channel in
    let sent = TlsInFlight?.sent s.channel in
    let synth_sender : CS.connection_state = { recip with CS.cs_model = snapshot } in
    // `protected_channel_ready s` unfolds (on the `TlsInFlight` branch) to the guarded
    // consequent for the concrete carried message `sent`; the guard (incl. `TlsHandshake? sent`)
    // is exactly `requires`, so the consequent fires.  Witness `msg = sent`, `sender_st = synth_sender`.
    introduce exists (msg:M.tls_message) (sender_st:CS.connection_state).
         sender_st.CS.cs_model == snapshot /\
         (match recipient with
          | CS.ClientEndpoint ->
            CS.peer_record_material_agrees (CS.traffic_id CS.TrafficHandshake CS.ServerTraffic) recip sender_st /\
            sender_st.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
              recip.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
            CS.sent_single_protected_message_seal sender_st.CS.cs_model msg raw /\
            (let (ct, frag) = W.serialize_tls_message msg in W.parse_tls_message ct frag == Some msg)
          | CS.ServerEndpoint ->
            CS.peer_record_material_agrees (CS.traffic_id CS.TrafficHandshake CS.ClientTraffic) sender_st recip /\
            sender_st.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
              recip.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
            CS.sent_single_protected_message_seal sender_st.CS.cs_model msg raw /\
            (let (ct, frag) = W.serialize_tls_message msg in W.parse_tls_message ct frag == Some msg))
    with sent synth_sender
    and ()
#pop-options
