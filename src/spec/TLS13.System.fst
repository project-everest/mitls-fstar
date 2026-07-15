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
module SBD  = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module WFSM = Common.WireFormatStateMachine
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module PNT  = TLS13.Impl.Driver.PairingNoTail
module PC   = TLS13.System.ProgressCount
module PWL  = TLS13.ConnectionState.ProtectedWireBase
module ST   = TLS13.Impl.Server.Types
module SWR  = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank
module Bounds = TLS13.Impl.ConnectionState.Bounds

open FStar.List.Tot

(** ─────────────────────────────────────────────────────────────────────────
    States
    ───────────────────────────────────────────────────────────────────────── **)

(** The in-flight raw-byte channel: at most one raw record in flight, tagged with
    the endpoint role that will receive it. **)
noeq
type tls_channel =
  | TlsQuiet    : tls_channel
  | TlsInFlight : recipient:CS.endpoint_role -> raw:B.bytes -> tls_channel

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
  | TlsInFlight CS.ServerEndpoint raw ->
    ((exists server_ch.
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw)
     ==>
     (match (hsf s.client).CS.hs_client_hello with
      | Some client_ch ->
        WFL.supported_client_hello_wire_profile client_ch /\
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw
      | None -> False))
  | TlsInFlight CS.ClientEndpoint raw ->
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
  | TlsInFlight CS.ServerEndpoint raw ->
    Seq.equal cs (B.append sr raw) /\ Seq.equal ss cr
  | TlsInFlight CS.ClientEndpoint raw ->
    Seq.equal ss (B.append cr raw) /\ Seq.equal cs sr

(** ─────────────────────────────────────────────────────────────────────────
    STAGE 1 — the forward LENGTH invariant.

    With the strict-progress guard forbidding the two model no-op self-loops
    (redundant idempotent installs, stray ChangeCipherSpec), the per-endpoint
    event-log length is pinned to the structural progress COUNT throughout the
    pre-application-data region.  (In the application-data / close tail the count
    is not tracked — app-data records lengthen the log freely.)  The two shape
    conjuncts `client_micro_shape`/`server_micro_shape` supply the region-entry
    freshness facts the progress-bound lemmas need.
    ───────────────────────────────────────────────────────────────────────── **)

let client_len_ok (s:tls_system_state) : prop =
  PC.pre_appdata_control (ctrl s.client) ==>
    FStar.List.Tot.length s.client.CS.cs_event_log ==
    PC.client_progress s.client.CS.cs_model

let server_len_ok (s:tls_system_state) : prop =
  PC.pre_appdata_control (ctrl s.server) ==>
    FStar.List.Tot.length s.server.CS.cs_event_log ==
    PC.server_progress s.server.CS.cs_model

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

(** STAGE 1B — application-data tail length bound for the client.  Once the client
    reaches the application-data control, its event-log length is pinned between a
    fixed floor (16, the handshake events already logged at entry) and a ceiling
    that grows only with the number of ApplicationData wire records the client has
    actually sent or received.  This is the application-data analogue of
    `client_len_ok` (which governs the pre-application-data region). **)
let client_appdata_len_ok (s:tls_system_state) : prop =
  client_ready s ==>
    ( 16 <= FStar.List.Tot.length s.client.CS.cs_event_log /\
      FStar.List.Tot.length s.client.CS.cs_event_log
        <= 11 + WStep.raw_appdata_count s.client.CS.cs_wire_log.CL.raw_sent
              + WStep.raw_appdata_count s.client.CS.cs_wire_log.CL.raw_received )

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
  client_len_ok s /\
  client_appdata_len_ok s /\
  server_len_ok s /\
  client_ksp s /\
  server_ksp s /\
  client_e2e s /\
  server_e2e s /\
  client_clean s /\
  protected_witnesses_ok s /\
  PC.client_micro_shape s.client.CS.cs_model /\
  PC.server_micro_shape s.server.CS.cs_model

(** ─────────────────────────────────────────────────────────────────────────
    The six transition shapes.  Each advances exactly one endpoint by exactly one
    step of the official canonical relation, VERBATIM (no wrapper, no pin).  Sends
    require a quiet channel and emit a single record; a LocalEvent that emits a
    record is a "send", one that emits nothing is a "local".  Deliveries consume
    the matching in-flight raw and return the channel to quiet.  Every shape
    guards the changed endpoint with `connection_state_no_key_update_trace`.
    ───────────────────────────────────────────────────────────────────────── **)

(** The strict-progress SIDE CONDITION (STAGE 1).  A pre-application-data
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
    control-changing steps and never an internal app-read before it is ready. **)
let client_local_advances (before after:CS.connection_state) : prop =
  PC.client_progress after.CS.cs_model > PC.client_progress before.CS.cs_model \/
  ~(after.CS.cs_model.CS.model_control == before.CS.cs_model.CS.model_control)

let server_local_advances (before after:CS.connection_state) : prop =
  PC.server_progress after.CS.cs_model > PC.server_progress before.CS.cs_model \/
  ~(after.CS.cs_model.CS.model_control == before.CS.cs_model.CS.model_control)

let tls_step_client_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.client_local_event) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
     CCP.client_step a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [w] /\
     CS.connection_state_no_key_update_trace c' /\
     client_advances a.client c' /\
     b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) })

let tls_step_server_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.server_local_event) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
     SCP.server_step a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [w] /\
     CS.connection_state_no_key_update_trace s' /\
     server_advances a.server s' /\
     b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) })

let tls_step_deliver_to_server (a b:tls_system_state) : prop =
  (exists (wire:CW.wire_message) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
     a.channel == TlsInFlight CS.ServerEndpoint raw /\
     Seq.equal (CW.wire_serialize wire) raw /\
     SCP.server_step a.server (SM.WireEvent wire) s' out /\
     CS.connection_state_no_key_update_trace s' /\
     server_advances a.server s' /\
     b == { a with server = s'; channel = TlsQuiet })

let tls_step_deliver_to_client (a b:tls_system_state) : prop =
  (exists (wire:CW.wire_message) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
     a.channel == TlsInFlight CS.ClientEndpoint raw /\
     Seq.equal (CW.wire_serialize wire) raw /\
     CCP.client_step a.client (SM.WireEvent wire) c' out /\
     CS.connection_state_no_key_update_trace c' /\
     client_advances a.client c' /\
     b == { a with client = c'; channel = TlsQuiet })

let tls_step_client_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.client_local_event) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output).
     CCP.client_step a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [] /\
     CS.connection_state_no_key_update_trace c' /\
     client_local_advances a.client c' /\
     b == { a with client = c' })

let tls_step_server_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.server_local_event) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output).
     SCP.server_step a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [] /\
     CS.connection_state_no_key_update_trace s' /\
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
        (PC.pre_appdata_control a.CS.cs_model.CS.model_control ==>
           FStar.List.Tot.length a.CS.cs_event_log == PC.client_progress a.CS.cs_model) /\
        PC.client_micro_shape a.CS.cs_model)
      (ensures
        (PC.pre_appdata_control c'.CS.cs_model.CS.model_control ==>
           FStar.List.Tot.length c'.CS.cs_event_log == PC.client_progress c'.CS.cs_model) /\
        PC.client_micro_shape c'.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d c');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d c'
    returns
      (PC.pre_appdata_control c'.CS.cs_model.CS.model_control ==>
         FStar.List.Tot.length c'.CS.cs_event_log == PC.client_progress c'.CS.cs_model) /\
      PC.client_micro_shape c'.CS.cs_model
    with _pf.
      (PC.lemma_delta_length a c' d;
       PC.lemma_client_micro_shape_step a.CS.cs_model d.CS.delta_event c'.CS.cs_model;
       if PC.pre_appdata_control c'.CS.cs_model.CS.model_control then begin
         (if not (PC.pre_appdata_control a.CS.cs_model.CS.model_control)
          then PC.lemma_step_post_appdata_stable a.CS.cs_model d.CS.delta_event c'.CS.cs_model);
         assert (PC.pre_appdata_control a.CS.cs_model.CS.model_control);
         PC.lemma_client_progress_step_bound a.CS.cs_model d.CS.delta_event c'.CS.cs_model;
         assert (PC.client_progress c'.CS.cs_model > PC.client_progress a.CS.cs_model);
         assert (FStar.List.Tot.length c'.CS.cs_event_log
                   == FStar.List.Tot.length a.CS.cs_event_log + 1);
         assert (FStar.List.Tot.length c'.CS.cs_event_log == PC.client_progress c'.CS.cs_model)
       end)
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80 --split_queries always"
let lemma_server_step_len_micro
  (a s':CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step a e s' out /\
        a.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        server_advances a s' /\
        (PC.pre_appdata_control a.CS.cs_model.CS.model_control ==>
           FStar.List.Tot.length a.CS.cs_event_log == PC.server_progress a.CS.cs_model) /\
        PC.server_micro_shape a.CS.cs_model)
      (ensures
        (PC.pre_appdata_control s'.CS.cs_model.CS.model_control ==>
           FStar.List.Tot.length s'.CS.cs_event_log == PC.server_progress s'.CS.cs_model) /\
        PC.server_micro_shape s'.CS.cs_model)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta a d s');
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a d s'
    returns
      (PC.pre_appdata_control s'.CS.cs_model.CS.model_control ==>
         FStar.List.Tot.length s'.CS.cs_event_log == PC.server_progress s'.CS.cs_model) /\
      PC.server_micro_shape s'.CS.cs_model
    with _pf.
      (PC.lemma_delta_length a s' d;
       PC.lemma_server_micro_shape_step a.CS.cs_model d.CS.delta_event s'.CS.cs_model;
       if PC.pre_appdata_control s'.CS.cs_model.CS.model_control then begin
         (if not (PC.pre_appdata_control a.CS.cs_model.CS.model_control)
          then PC.lemma_step_post_appdata_stable a.CS.cs_model d.CS.delta_event s'.CS.cs_model);
         assert (PC.pre_appdata_control a.CS.cs_model.CS.model_control);
         PC.lemma_server_progress_step_bound a.CS.cs_model d.CS.delta_event s'.CS.cs_model;
         assert (PC.server_progress s'.CS.cs_model > PC.server_progress a.CS.cs_model);
         assert (FStar.List.Tot.length s'.CS.cs_event_log
                   == FStar.List.Tot.length a.CS.cs_event_log + 1);
         assert (FStar.List.Tot.length s'.CS.cs_event_log == PC.server_progress s'.CS.cs_model)
       end)
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
        (forall (dir:CS.direction) (sh:M.server_hello).
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
        (forall (dir:CS.direction) (ch:M.client_hello).
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
      (assert (forall (dir:CS.direction) (sh:M.server_hello).
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
      (assert (forall (dir:CS.direction) (ch:M.client_hello).
         conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                     CL.message_value = M.TlsHandshake (M.ClientHello ch) }));
       lemma_step_preserves_client_hello_legal st0.CS.cs_model conn_ev st1.CS.cs_model)
#pop-options

let lemma_initial_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c)
      (ensures tls_system_inv (initial_tls_system cfg_c cfg_s))
  = assert (CS.connection_state_evolves (CS.initial cfg_c) (CS.initial cfg_c));
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
    assert (~(client_ready (initial_tls_system cfg_c cfg_s)))

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
  : Lemma
      (requires
        tls_system_inv a /\ TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        channel_consistent
          ({ a with client = c';
                    channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) }))
  = let b = { a with client = c';
                     channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) } in
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
                   (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
    CCP.client_step a.client (SM.LocalEvent local) c' out /\
    out.SM.so_wire_outputs == [w] /\
    CS.connection_state_no_key_update_trace c' /\
    b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
          channel_consistent b /\ hello_coupling b
  with _pf. (
    lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
    lemma_client_local_preserves_server_hello a.client c' local out;
    lemma_cc_client_send a local c' out w;
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
  : Lemma
      (requires
        tls_system_inv a /\ TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        channel_consistent
          ({ a with server = s';
                    channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) }))
  = let b = { a with server = s';
                     channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) } in
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
                   (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
    SCP.server_step a.server (SM.LocalEvent local) s' out /\
    out.SM.so_wire_outputs == [w] /\
    CS.connection_state_no_key_update_trace s' /\
    b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) }
  returns ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
          channel_consistent b /\ hello_coupling b
  with _pf. (
    lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
    lemma_server_local_preserves_client_hello a.server s' local out;
    lemma_cc_server_send a local s' out w;
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
                   (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
    a.channel == TlsInFlight CS.ServerEndpoint raw /\
    Seq.equal (CW.wire_serialize wire) raw /\
    SCP.server_step a.server (SM.WireEvent wire) s' out /\
    CS.connection_state_no_key_update_trace s' /\
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
         assert (forall (dir:CS.direction) (ch:M.client_hello).
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
  (client_sh:M.server_hello)
  (content_type:U8.t) (fragment:B.bytes)
  : Lemma
      (requires
        tls_system_inv a /\
        a.channel == TlsInFlight CS.ClientEndpoint raw /\
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
let lemma_deliver_to_client_sh_bridge a b wire c' out raw client_sh content_type fragment =
  assert (channel_consistent a);
  assert (CS.connection_state_consistent a.server);
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
    (if outer_ct = T.ApplicationData
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
      let server_sh : M.server_hello = Some?.v (hsf a.server).CS.hs_server_hello in
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
        let client_ch : M.client_hello = Some?.v (hsf b.client).CS.hs_client_hello in
        let server_ch : M.client_hello = Some?.v (hsf b.server).CS.hs_client_hello in
        // client_ch is a.client's CH (stability), server_ch is a.server's CH.
        assert ((hsf a.client).CS.hs_client_hello == Some client_ch);
        assert ((hsf a.server).CS.hs_client_hello == Some server_ch);
        // (3a) CH key share via ch_wire_equiv a.
        assert (ch_wire_equiv a);
        eliminate exists (raw':B.bytes).
          CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw' /\
          CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw'
        returns WFL.paired_cleartext_hello_key_shares b.client b.server
        with _che. (
          WFL.lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
            client_ch server_ch raw' raw';
          // client_hello_wire_equivalent: key_share equal + server_ch fields profile.
          Seq.lemma_eq_elim client_ch.M.key_share server_ch.M.key_share;
          assert (server_ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256]);
          // (3b) SH key share via server_sh body=0 + chacha + parse equality.
          WStep.lemma_consistent_server_hello_cipher_body a.server;
          assert (CS.cipher_suite_offered server_ch.M.cipher_suites server_sh.M.cipher_suite);
          assert (B.length (server_sh.M.body <: B.bytes) == 0);
          assert (CS.cipher_suite_offered [T.TLS_CHACHA20_POLY1305_SHA256]
                    server_sh.M.cipher_suite);
          WStep.lemma_cipher_suite_offered_singleton_chacha server_sh.M.cipher_suite;
          assert (server_sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256);
          // fragment == serialize_handshake (SH server_sh)
          WStep.lemma_cleartext_server_hello_parse_record server_sh raw;
          Seq.lemma_eq_elim fragment (W.serialize_handshake (M.ServerHello server_sh));
          assert (W.parse_tls_message T.Handshake
                    (W.serialize_handshake (M.ServerHello server_sh)) ==
                  Some (M.TlsHandshake (M.ServerHello client_sh)));
          SHPB.lemma_parse_tls_message_serialize_server_hello_key_share
            server_sh client_sh;
          Seq.lemma_eq_elim client_sh.M.key_share server_sh.M.key_share;
          assert (CS.server_hello_key_share client_sh == CS.server_hello_key_share server_sh);
          assert (CS.client_hello_key_share client_ch == CS.client_hello_key_share server_ch);
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
                   (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
    a.channel == TlsInFlight CS.ClientEndpoint raw /\
    Seq.equal (CW.wire_serialize wire) raw /\
    CCP.client_step a.client (SM.WireEvent wire) c' out /\
    CS.connection_state_no_key_update_trace c' /\
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
         assert (forall (dir:CS.direction) (ch:M.client_hello).
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
           lemma_deliver_to_client_sh_bridge a b wire c' out raw client_sh content_type fragment
         )
       | M.TlsHandshake (M.ClientHello _) ->
         // A client (role ClientEndpoint) cannot legally RECEIVE a ClientHello.
         assert (a.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
         assert (CS.legal_event a.client.CS.cs_model conn_ev)
       | _ ->
         // non-hello receive: both hello fields unchanged, so FACTS 1–3 + coupling
         // transfer from a.
         assert (forall (dir:CS.direction) (sh:M.server_hello).
           conn_ev =!= CS.ConnNetworkEvent ({ CL.message_direction = dir;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh) }));
         lemma_step_preserves_server_hello a.client.CS.cs_model conn_ev c'.CS.cs_model;
         assert (forall (dir:CS.direction) (ch:M.client_hello).
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
    CS.connection_state_no_key_update_trace c' /\
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
    CS.connection_state_no_key_update_trace s' /\
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
  : Lemma
      (requires
        byte_pairing a /\ TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        byte_pairing
          ({ a with client = c';
                    channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) }))
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
  : Lemma
      (requires
        byte_pairing a /\ TlsQuiet? a.channel /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        byte_pairing
          ({ a with server = s';
                    channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) }))
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
  : Lemma
      (requires
        byte_pairing a /\
        a.channel == TlsInFlight CS.ServerEndpoint raw /\
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
  : Lemma
      (requires
        byte_pairing a /\
        a.channel == TlsInFlight CS.ClientEndpoint raw /\
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

(** STAGE 1B — the application-data tail LENGTH bound is preserved by a client
    SEND.  A send appends exactly one event (length +1) and one wire record to the
    client's SENT log.  If the post-state is ready (application data), we split:

    * STAY (pre-state already at application data): the backward key-installation
      lemma certifies the pre-state was ALSO ready, so `client_appdata_len_ok a`
      supplies the pre-state bounds; the appended record is ApplicationData
      (`lemma_client_send_stay_appdata_count_ge1`), raising the SENT count by ≥1,
      which exactly absorbs the length +1 for the upper bound; the lower bound
      floor(16) rises to 17.
    * ENTRY (pre-state pre-application-data, the send of the protected Finished):
      `PC.lemma_client_send_cf_progress` + `client_len_ok a` pin the pre-length to
      15, hence post-length 16 (floor met exactly); the reachable post-state has
      ≥4 received + ≥1 sent ApplicationData records
      (`lemma_client_postappdata_recv_ge4_sent_ge1`), i.e. count ≥5, so
      16 ≤ 11 + 5 ≤ 11 + counts. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_appdata_len_pres_send
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message)
  : Lemma
      (requires
        tls_system_inv a /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        CS.connection_state_no_key_update_trace c' /\
        b == { a with client = c';
                      channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) } /\
        WStep.client_reachable (CS.initial c'.CS.cs_model.CS.model_config) c')
      (ensures client_appdata_len_ok b)
  = let cs_a = a.client.CS.cs_wire_log.CL.raw_sent in
    let cr_a = a.client.CS.cs_wire_log.CL.raw_received in
    let er = emitted_raw out in
    introduce client_ready b ==>
      ( 16 <= FStar.List.Tot.length b.client.CS.cs_event_log /\
        FStar.List.Tot.length b.client.CS.cs_event_log
          <= 11 + WStep.raw_appdata_count b.client.CS.cs_wire_log.CL.raw_sent
                + WStep.raw_appdata_count b.client.CS.cs_wire_log.CL.raw_received )
    with _ready_b.
    (
      // b.client == c' is at application data with app record keys installed.
      assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.client d c');
      eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.client d c'
      returns
        ( 16 <= FStar.List.Tot.length c'.CS.cs_event_log /\
          FStar.List.Tot.length c'.CS.cs_event_log
            <= 11 + WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_sent
                  + WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_received )
      with _pf_d.
      (
        PC.lemma_delta_length a.client c' d;
        lemma_no_key_update_last a.client.CS.cs_event_log d.CS.delta_event;
        CSL.lemma_step_model_preserves_config
          a.client.CS.cs_model d.CS.delta_event c'.CS.cs_model;
        if a.client.CS.cs_model.CS.model_control = CS.ControlApplicationData
        then begin
          // STAY: the pre-state was also ready.
          lemma_client_appdata_installed_backward a.client d c';
          assert (client_ready a);
          // the appended record is ApplicationData, so the SENT count rises by >=1.
          WStep.lemma_client_send_stay_appdata_count_ge1 a.client local c' out w;
          // count split on the SENT log; the RECEIVED log is unchanged.
          PNTWL.lemma_client_step_wire_log_delta
            a.client (SM.LocalEvent local) c' out;
          WStep.lemma_client_reachable_raw_sent_parses
            a.client.CS.cs_model.CS.model_config a.client;
          eliminate exists (msgs:list CW.wire_message).
            WF.parses_as CW.tls_record_wire_format cs_a msgs Seq.empty
          returns
            WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_sent
              == WStep.raw_appdata_count cs_a + WStep.raw_appdata_count er /\
            WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_received
              == WStep.raw_appdata_count cr_a
          with _pf_parse.
          (
            WStep.lemma_raw_appdata_count_append cs_a er msgs;
            Seq.lemma_eq_elim c'.CS.cs_wire_log.CL.raw_sent (B.append cs_a er);
            Seq.lemma_eq_elim c'.CS.cs_wire_log.CL.raw_received cr_a
          )
        end
        else begin
          // ENTRY: send of the protected Finished lands at application data.
          PC.lemma_client_send_cf_progress
            a.client.CS.cs_model d.CS.delta_event c'.CS.cs_model;
          WStep.lemma_client_postappdata_recv_ge4_sent_ge1
            c'.CS.cs_model.CS.model_config c'
        end
      )
    )
#pop-options

(** STAGE 1B — the application-data tail LENGTH bound is preserved by a DELIVER TO
    CLIENT (a client RECEIVE).  A receive appends exactly one event (length +1) and
    one wire record to the client's RECEIVED log (the SENT log is unchanged).  If
    the post-state is ready (application data), a receive never ENTERS application
    data (`lemma_client_wire_recv_not_into_appdata`), so the pre-state was already
    at application data; the backward key-installation lemma then certifies the
    pre-state was ALSO ready, so `client_appdata_len_ok a` supplies the pre-state
    bounds.  The received record is ApplicationData
    (`lemma_client_recv_at_appdata_count1`), raising the RECEIVED count by exactly
    1, which exactly absorbs the length +1 for the upper bound; the lower floor(16)
    rises to 17. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_appdata_len_pres_deliver
  (a b:tls_system_state)
  (wire:CW.wire_message) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        CCP.client_step a.client (SM.WireEvent wire) c' out /\
        CS.connection_state_no_key_update_trace c' /\
        b == { a with client = c'; channel = TlsQuiet } /\
        WStep.client_reachable (CS.initial c'.CS.cs_model.CS.model_config) c')
      (ensures client_appdata_len_ok b)
  = let cs_a = a.client.CS.cs_wire_log.CL.raw_sent in
    let cr_a = a.client.CS.cs_wire_log.CL.raw_received in
    introduce client_ready b ==>
      ( 16 <= FStar.List.Tot.length b.client.CS.cs_event_log /\
        FStar.List.Tot.length b.client.CS.cs_event_log
          <= 11 + WStep.raw_appdata_count b.client.CS.cs_wire_log.CL.raw_sent
                + WStep.raw_appdata_count b.client.CS.cs_wire_log.CL.raw_received )
    with _ready_b.
    (
      // c' is at application data; a receive never ENTERS application data, so the
      // pre-state was already there.
      WStep.lemma_client_wire_recv_not_into_appdata a.client wire c' out;
      assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.client d c');
      eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.client d c'
      returns
        ( 16 <= FStar.List.Tot.length c'.CS.cs_event_log /\
          FStar.List.Tot.length c'.CS.cs_event_log
            <= 11 + WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_sent
                  + WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_received )
      with _pf_d.
      (
        PC.lemma_delta_length a.client c' d;
        lemma_no_key_update_last a.client.CS.cs_event_log d.CS.delta_event;
        // backward keys: the pre-state was also ready.
        lemma_client_appdata_installed_backward a.client d c';
        assert (client_ready a);
        // the received record is ApplicationData, so the RECEIVED count rises by 1.
        WStep.lemma_client_recv_at_appdata_count1 a.client wire c' out;
        // wire-log deltas: SENT unchanged, RECEIVED extended by (wire_serialize wire).
        WStep.lemma_client_wire_event_no_output a.client c' wire out;
        WStep.lemma_serialize_all_single_wire wire;
        Seq.lemma_eq_elim
          (WF.serialize_all CW.tls_record_wire_format [wire])
          (CW.wire_serialize wire);
        PNTWL.lemma_client_step_wire_log_delta a.client (SM.WireEvent wire) c' out;
        Seq.append_empty_r cs_a;
        Seq.lemma_eq_elim c'.CS.cs_wire_log.CL.raw_sent cs_a;
        Seq.lemma_eq_elim c'.CS.cs_wire_log.CL.raw_received
          (B.append cr_a (CW.wire_serialize wire));
        // count split on the RECEIVED log.
        WStep.lemma_client_reachable_raw_received_parses
          a.client.CS.cs_model.CS.model_config a.client;
        eliminate exists (msgs:list CW.wire_message).
          WF.parses_as CW.tls_record_wire_format cr_a msgs Seq.empty
        returns
          WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_received
            == WStep.raw_appdata_count cr_a
             + WStep.raw_appdata_count (CW.wire_serialize wire) /\
          WStep.raw_appdata_count c'.CS.cs_wire_log.CL.raw_sent
            == WStep.raw_appdata_count cs_a
        with _pf_parse.
        (
          WStep.lemma_raw_appdata_count_append cr_a (CW.wire_serialize wire) msgs
        )
      )
    )
#pop-options

(** STAGE 1B — the application-data tail LENGTH bound is vacuously preserved by a
    client LOCAL step (no wire output).  A ready post-state requires application
    data at `c'`; a LOCAL step cannot produce that.  If the pre-state was already
    at application data, control is unchanged and (as `client_progress` is flat off
    the handshake region) progress does not rise, so the internal-local guard
    `client_local_advances` is violated — contradiction.  If the pre-state was
    pre-application-data, a no-output LOCAL step never ENTERS application data
    (`lemma_client_local_noout_not_into_appdata`) — contradiction.  Either way
    `client_ready b` is impossible, so the bound holds vacuously. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_client_appdata_len_pres_local
  (a b:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [] /\
        client_local_advances a.client c' /\
        b == { a with client = c' })
      (ensures client_appdata_len_ok b)
  = introduce client_ready b ==>
      ( 16 <= FStar.List.Tot.length b.client.CS.cs_event_log /\
        FStar.List.Tot.length b.client.CS.cs_event_log
          <= 11 + WStep.raw_appdata_count b.client.CS.cs_wire_log.CL.raw_sent
                + WStep.raw_appdata_count b.client.CS.cs_wire_log.CL.raw_received )
    with _ready_b.
    (
      // client_ready b forces c' to be at application data; derive False.
      if a.client.CS.cs_model.CS.model_control = CS.ControlApplicationData
      then ()  // STAY: control unchanged + progress flat contradicts client_local_advances.
      else WStep.lemma_client_local_noout_not_into_appdata a.client local c' out
    )
#pop-options

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

(** SERVER: the only route into application data is the LocalVerifyClientFinished
    verify, at `HsClientFinishedReceived`, with the application record keys already
    installed (a genuine `ConnLocalEvent`). **)
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
        m.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.application_record_keys_installed_for_role CS.ServerEndpoint m /\
        CS.ConnLocalEvent? ev)
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

(** SERVER: a Received event never enters application data. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_server_recv_not_into_appdata
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (CS.received_tls_event msg) /\
        CS.step_model m (CS.received_tls_event msg) == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(m.CS.model_control == CS.ControlApplicationData))
      (ensures ~(m'.CS.model_control == CS.ControlApplicationData))
  = ()
#pop-options

(** SERVER step-level: a RECEIVE never moves control into application data. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_wire_recv_not_into_appdata
  (st0:CS.connection_state) (wire:CW.wire_message)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message CTy.local_output)
  : Lemma
      (requires
        SCP.server_step st0 (SM.WireEvent wire) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
  = if st0.CS.cs_model.CS.model_control = CS.ControlApplicationData then ()
    else
      eliminate exists (msg:M.tls_message).
        (let conn_ev = CS.ConnNetworkEvent {
             CL.message_direction = CL.Received; CL.message_value = msg; } in
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev;
             CS.delta_raw_sent =
               WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
             CS.delta_raw_received = CW.wire_serialize wire; } st1 /\
         CS.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         CS.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns st0.CS.cs_model.CS.model_control == CS.ControlApplicationData
      with _.
        lemma_server_recv_not_into_appdata st0.CS.cs_model msg st1.CS.cs_model
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
      lemma_server_into_appdata_is_verify st0.CS.cs_model conn_ev st1.CS.cs_model
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

(** `server_progress == 15` at the verify pre-state (all three application
    obligations discharged: both app-traffic secrets installed by the verify
    legality, and the shared secret present by the key-schedule prefix). **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_server_verify_pre_length (m:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.application_record_keys_installed_for_role CS.ServerEndpoint m /\
        PC.model_ksp m)
      (ensures PC.server_progress m == 15)
  = ()
#pop-options

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
        server_ready s /\
        FStar.List.Tot.length s.client.CS.cs_event_log == 16 /\
        FStar.List.Tot.length s.server.CS.cs_event_log == 16)
      (ensures
        P.paired_protected_handshake_event_projection_pair_witnesses s.client s.server)
  = let cfg_c = s.client.CS.cs_model.CS.model_config in
    let cfg_s = s.server.CS.cs_model.CS.model_config in
    WStep.lemma_client_valid_byte_trace_of_reachable cfg_c s.client;
    WStep.lemma_server_valid_byte_trace_of_reachable cfg_s s.server;
    assert (PNT.paired_no_tail_application_ready_boundary16 s.client s.server);
    SBD.lemma_paired_protected_witnesses_from_clean16_valid_byte_traces_and_hello_key_shares
      (CS.initial cfg_c) (CS.initial cfg_s) s.client s.server
      s.client.CS.cs_wire_log.CL.raw_received
      s.client.CS.cs_wire_log.CL.raw_sent
      s.server.CS.cs_wire_log.CL.raw_received
      s.server.CS.cs_wire_log.CL.raw_sent
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
  : Lemma
      (requires
        tls_system_inv a /\
        SCP.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        CS.connection_state_no_key_update_trace s' /\
        b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) })
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

(** deliver TO SERVER — a receive never enters application data (ROUTE A). **)
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
        b == { a with server = s'; channel = TlsQuiet })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      lemma_server_wire_recv_not_into_appdata a.server wire s' out;
      lemma_pw_pres_server_appdata_route_a a b (SM.WireEvent wire) s' out
    )
#pop-options

(** Client event-log length is exactly 16 at the server-verify instant.  The
    client is ready, so `client_appdata_len_ok a` bounds its length below by 16
    and above by `11 + raw_appdata_count(sent) + raw_appdata_count(received)`.
    The pre-appdata server has received ≤ 1 and sent ≤ 4 application-data records
    (`lemma_server_preappdata_recv_le1` / `_sent_le4`); the quiescent byte-pairing
    (Seq.equal client-sent/server-received and server-sent/client-received) carries
    those bounds onto the client, so the upper bound collapses to 16. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pw_verify_client_len16 (a:tls_system_state)
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        client_ready a /\
        WStep.pre_appdata_ctrl a.server.CS.cs_model.CS.model_control)
      (ensures FStar.List.Tot.length a.client.CS.cs_event_log == 16)
  = let cfg_s = a.server.CS.cs_model.CS.model_config in
    WStep.lemma_server_preappdata_recv_le1 cfg_s a.server;
    WStep.lemma_server_preappdata_sent_le4 cfg_s a.server;
    WStep.lemma_raw_appdata_count_seq_equal
      a.client.CS.cs_wire_log.CL.raw_sent a.server.CS.cs_wire_log.CL.raw_received;
    WStep.lemma_raw_appdata_count_seq_equal
      a.server.CS.cs_wire_log.CL.raw_sent a.client.CS.cs_wire_log.CL.raw_received
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

(** server LOCAL — either the server was already ready (ROUTE A) or this is the
    verify step that NEWLY creates the both-ready boundary (ROUTE B ESTABLISHMENT).
    At the verify, the server has just entered application data at event-log length
    16; the client (unchanged, already ready) is at length 16 by the quiescent
    byte-pairing; so `tls_application_ready b` holds and `lemma_pw_establish`
    supplies the witnesses. **)
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
        // ROUTE B — this is the verify step.
        lemma_server_local_into_appdata_shape a.server local s' out;
        // ── b-structural facts. ──
        lemma_bp_server_local a local s' out;
        lemma_wire_facts_server_local a b;
        // ── client length 16 (unchanged; quiescent byte-pairing bounds). ──
        assert (client_ready a);
        lemma_pw_verify_client_len16 a;
        assert (FStar.List.Tot.length a.client.CS.cs_event_log == 16);
        // ── server length 16 + reachability (via the underlying legal delta). ──
        assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s');
        eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s'
        returns
          P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
        with _pd.
        (
          CSL.lemma_step_model_preserves_config
            a.server.CS.cs_model d.CS.delta_event s'.CS.cs_model;
          lemma_server_reach_pres a s' (SM.LocalEvent local) out;
          lemma_server_verify_pre_length a.server.CS.cs_model;
          PC.lemma_delta_length a.server s' d;
          assert (FStar.List.Tot.length s'.CS.cs_event_log == 16);
          assert (FStar.List.Tot.length b.client.CS.cs_event_log == 16 /\
                  FStar.List.Tot.length b.server.CS.cs_event_log == 16);
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
  : Lemma
      (requires
        tls_system_inv a /\
        TlsQuiet? a.channel /\
        CCP.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        CS.connection_state_no_key_update_trace c' /\
        b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) })
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

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      CS.connection_state_no_key_update_trace c' /\
      client_advances a.client c' /\
      b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) }
    returns tls_system_inv b
    with _pf.
      (lemma_client_step_preserves_stage_ok a.client c' (SM.LocalEvent local) out;
       lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_client_step_len_micro a.client c' (SM.LocalEvent local) out;
       lemma_client_step_ksp a.client c' (SM.LocalEvent local) out;
       lemma_client_step_e2e a.client c' (SM.LocalEvent local) out;
       lemma_bp_client_send a local c' out w;
       lemma_wire_facts_client_send a b;
       lemma_client_appdata_len_pres_send a b local c' out w;
       lemma_pw_pres_client_send a b local c' out w)
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
      SCP.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      CS.connection_state_no_key_update_trace s' /\
      server_advances a.server s' /\
      b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) }
    returns tls_system_inv b
    with _pf.
      (lemma_server_step_preserves_stage_ok a.server s' (SM.LocalEvent local) out;
       lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_server_step_len_micro a.server s' (SM.LocalEvent local) out;
       lemma_server_step_ksp a.server s' (SM.LocalEvent local) out;
       lemma_server_step_e2e a.server s' (SM.LocalEvent local) out;
       lemma_bp_server_send a local s' out w;
       lemma_wire_facts_server_send a b;
       lemma_pw_pres_server_send a b local s' out w)
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

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pres_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b)
          (ensures tls_system_inv b)
  = eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
      a.channel == TlsInFlight CS.ServerEndpoint raw /\
      Seq.equal (CW.wire_serialize wire) raw /\
      SCP.server_step a.server (SM.WireEvent wire) s' out /\
      CS.connection_state_no_key_update_trace s' /\
      server_advances a.server s' /\
      b == { a with server = s'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_server_step_preserves_stage_ok a.server s' (SM.WireEvent wire) out;
       lemma_server_step_pres a.server s' (SM.WireEvent wire) out;
       lemma_server_step_shape a.server s' (SM.WireEvent wire) out;
       lemma_server_reach_pres a s' (SM.WireEvent wire) out;
       lemma_server_step_len_micro a.server s' (SM.WireEvent wire) out;
       lemma_server_step_ksp a.server s' (SM.WireEvent wire) out;
       lemma_server_step_e2e a.server s' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_server a wire s' out raw;
       lemma_wire_facts_deliver_to_server a b;
       lemma_pw_pres_deliver_to_server a b wire s' out;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pres_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b)
          (ensures tls_system_inv b)
  = eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                    (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
      a.channel == TlsInFlight CS.ClientEndpoint raw /\
      Seq.equal (CW.wire_serialize wire) raw /\
      CCP.client_step a.client (SM.WireEvent wire) c' out /\
      CS.connection_state_no_key_update_trace c' /\
      client_advances a.client c' /\
      b == { a with client = c'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_client_step_preserves_stage_ok a.client c' (SM.WireEvent wire) out;
       lemma_client_step_pres a.client c' (SM.WireEvent wire) out;
       lemma_client_step_shape a.client c' (SM.WireEvent wire) out;
       lemma_client_reach_pres a c' (SM.WireEvent wire) out;
       lemma_client_step_len_micro a.client c' (SM.WireEvent wire) out;
       lemma_client_step_ksp a.client c' (SM.WireEvent wire) out;
       lemma_client_step_e2e a.client c' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_client a wire c' out raw;
       lemma_wire_facts_deliver_to_client a b;
       lemma_client_appdata_len_pres_deliver a b wire c' out;
       lemma_pw_pres_deliver_to_client a b wire c' out;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_local a b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      CS.connection_state_no_key_update_trace c' /\
      client_local_advances a.client c' /\
      b == { a with client = c' }
    returns tls_system_inv b
    with _pf.
      (lemma_client_step_preserves_stage_ok a.client c' (SM.LocalEvent local) out;
       lemma_client_local_advances_to_advances a.client c' local out;
       lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_client_step_len_micro a.client c' (SM.LocalEvent local) out;
       lemma_client_step_ksp a.client c' (SM.LocalEvent local) out;
       lemma_client_step_e2e a.client c' (SM.LocalEvent local) out;
       lemma_bp_client_local a local c' out;
       lemma_wire_facts_client_local a b;
       lemma_client_appdata_len_pres_local a b local c' out;
       lemma_pw_pres_client_local a b local c' out;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_local a b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output).
      SCP.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      CS.connection_state_no_key_update_trace s' /\
      server_local_advances a.server s' /\
      b == { a with server = s' }
    returns tls_system_inv b
    with _pf.
      (lemma_server_step_preserves_stage_ok a.server s' (SM.LocalEvent local) out;
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
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ TlsQuiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_inv_preserved (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_sys_step a b)
          (ensures tls_system_inv b)
  = FStar.Classical.move_requires_2 lemma_pres_client_send a b;
    FStar.Classical.move_requires_2 lemma_pres_server_send a b;
    FStar.Classical.move_requires_2 lemma_pres_deliver_to_client a b;
    FStar.Classical.move_requires_2 lemma_pres_deliver_to_server a b;
    FStar.Classical.move_requires_2 lemma_pres_client_local a b;
    FStar.Classical.move_requires_2 lemma_pres_server_local a b
#pop-options

(** Reachable states satisfy the invariant. **)
val lemma_reachable_inv (cfg_c cfg_s:CS.connection_config) (s:tls_system_state)
  : Lemma (requires cfg_c.CS.config_role == CS.ClientEndpoint /\
                    cfg_s.CS.config_role == CS.ServerEndpoint /\
                    WFL.supported_client_config_wire_profile cfg_c /\
                    RTC.closure tls_sys_step (initial_tls_system cfg_c cfg_s) s)
          (ensures tls_system_inv s)
let lemma_reachable_inv cfg_c cfg_s s =
  lemma_initial_inv cfg_c cfg_s;
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 lemma_inv_preserved);
  RTC.stable_on_closure tls_sys_step tls_system_inv ()

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
