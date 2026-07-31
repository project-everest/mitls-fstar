module TLS13.System

(**
  The combined TLS 1.3 client<->server system — WIRE-LEVEL channel.

  This scales the `calc_sample` combined-system + temporal approach up to real
  TLS.  It composes two `TLS13.Spec.StateMachine.connection_state`s (a client
  and a server) with an explicit in-flight *raw-byte* channel, and advances each
  endpoint by exactly one step of the OFFICIAL canonical TLS transition relation
  (`TLS13.Spec.Endpoint.Client.client_step` /
  `TLS13.Spec.Endpoint.Server.server_step`) — used verbatim, with no
  wrapper and no event-log pin.

  Because the channel carries raw bytes, a delivery feeds the receiver *real wire
  bytes*, which the receiver parses into its own (body=full) message.  This makes
  deliveries genuinely inhabited (unlike a body=empty semantic delivery, which is
  unsatisfiable against `CS.received_cleartext_tls_message_raw`), so the flagship
  record-material-agreement theorem is NON-VACUOUS.  The body asymmetry (sender
  body=empty, receiver body=full) is reconciled by WIRE EQUIVALENCE, exactly what
  the pairing payoff lemma expects.
**)

module CS  = TLS13.Spec.StateMachine
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
module CW  = TLS13.Spec.Endpoint.Wire
module CTy = TLS13.Impl.CanonicalTypes
module EC  = TLS13.Spec.Endpoint.Client
module EAPI = TLS13.Spec.Endpoint.API
module SMR  = TLS13.Spec.StateMachine.Reachability
module SMC  = TLS13.Spec.StateMachine.Correspondence
module SMKI = TLS13.Spec.StateMachine.KeyIdentifiers
module SMKM = TLS13.Spec.StateMachine.KeyMaterial
module SMCan = TLS13.Spec.StateMachine.Canonical
module ES  = TLS13.Spec.Endpoint.Server
module WF  = Common.WireFormat
module WFL = TLS13.Spec.WireFormatLemmas
module W   = TLS13.Wire.Spec
module T   = TLS13.Types
module R   = TLS13.Record.Spec
module S   = TLS13.Spec.StateMachine.ClientTrace
module WStep = TLS13.System.WireStep
module CTy2 = TLS13.Impl.Client.Types
module SP  = Common.SystemProduct
module MP  = Common.MachineProduct
module X    = TLS13.X509.Spec
module U8   = FStar.UInt8
module TM   = TLS13.Impl.Messages
module SHPB = TLS13.Wire.Spec.Reveal.ServerHello.Parseback
module WFSM = Common.WireFormatStateMachine
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module PC   = TLS13.System.ProgressCount
module PWL  = TLS13.ConnectionState.ProtectedWireBase
module ST   = TLS13.Impl.Server.Types
module Bounds = TLS13.Impl.ConnectionState.Bounds
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module Sem = TLS13.Wire.Semantics

open FStar.List.Tot

(** ─────────────────────────────────────────────────────────────────────────
    States
    ───────────────────────────────────────────────────────────────────────── **)

(** The in-flight PAYLOAD of the raw-byte channel: the raw record bytes, plus the
    sender-side ghost material the invariant wants to remember (a snapshot of the
    sender's model at emission time, and the logical message that was sent).

    The CHANNEL and the SYSTEM STATE themselves are no longer declared here: they
    are the generic ones from `Common.MachineProduct`, whose constructors are
    `MP.Quiet` / `MP.ToServer` / `MP.ToClient` and whose record fields are already
    named `client` / `server` / `channel`.  The `pl_` prefixes keep the payload
    projectors clear of the `raw` / `raw_sent` identifiers used throughout this
    module. **)
noeq
type tls_payload = {
  pl_raw  : B.bytes;
  pl_snap : CS.connection_model;
  pl_sent : M.tls_message;
}

(** The combined system state: a client endpoint, a server endpoint, and the raw
    channel between them — the generic two-party product state. **)
type tls_system_state = MP.sys CS.connection_state CS.connection_state tls_payload

(** Channel constructors, spelled in the old (raw, snapshot, sent) argument order
    so that every construction site in this module stays a one-line rewrite. **)
let tls_to_server (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message)
  : MP.chan tls_payload
  = MP.ToServer ({ pl_raw = raw; pl_snap = snap; pl_sent = sent })

let tls_to_client (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message)
  : MP.chan tls_payload
  = MP.ToClient ({ pl_raw = raw; pl_snap = snap; pl_sent = sent })

(** The raw bytes an official step emits on the wire. **)
let emitted_raw (out:SM.step_output CW.wire_message EAPI.local_output) : GTot B.bytes =
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
let tls_quiescent (s:tls_system_state) : prop = MP.Quiet? s.channel

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
  SMC.connection_state_no_key_update_trace s.client /\
  SMC.connection_state_no_key_update_trace s.server

(** Initial state: fresh client and server from their configs, empty channel. **)
let initial_tls_system (cfg_c cfg_s:CS.connection_config) : tls_system_state = {
  client  = CS.initial cfg_c;
  server  = CS.initial cfg_s;
  channel = MP.Quiet;
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
  | MP.Quiet -> True
  | MP.ToServer p ->
    (let raw = p.pl_raw in
     (exists server_ch.
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) raw)
     ==>
     (match (hsf s.client).CS.hs_client_hello with
      | Some client_ch ->
        WFL.supported_client_hello_wire_profile client_ch /\
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) raw
      | None -> False))
  | MP.ToClient p ->
    (let raw = p.pl_raw in
     (exists (some_sh:GSH.serverHello).
        B.length (W.serialize_handshake (M.ServerHello some_sh)) <= 16640 /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello some_sh)) raw)
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
         to exact `SMC.paired_wire_logs`.
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
  | MP.Quiet ->
    Seq.equal cs sr /\ Seq.equal ss cr
  | MP.ToServer p ->
    Seq.equal cs (B.append sr p.pl_raw) /\ Seq.equal ss cr
  | MP.ToClient p ->
    Seq.equal ss (B.append cr p.pl_raw) /\ Seq.equal cs sr

(** ─────────────────────────────────────────────────────────────────────────
    Application-data STREAM integrity (STAGE C).

    The application-data BYTE STREAM each endpoint sends is the CONCATENATION of
    its `app_log.app_sent` chunks; likewise what it has received is the
    concatenation of its `app_log.app_received` chunks.  These are the honest
    TLS byte streams (record boundaries need not align, so the statement must be
    about the concatenations, not the chunk lists — see the note at
    `CS.LocalDeliverApplicationData` in `TLS13.Spec.StateMachine.fst`).
    ───────────────────────────────────────────────────────────────────────── **)

let app_stream_sent (st:CS.connection_state) : GTot B.bytes =
  CL.concat_bytes st.CS.cs_model.CS.model_application.CS.app_log.CL.app_sent

let app_stream_received (st:CS.connection_state) : GTot B.bytes =
  CL.concat_bytes st.CS.cs_model.CS.model_application.CS.app_log.CL.app_received

(** The application-data byte delta a single (received or sent) TLS message
    carries: the plaintext of an application-data record, and nothing for every
    other message kind. **)
let app_bytes_delta (msg:M.tls_message) : GTot B.bytes =
  match msg with
  | M.TlsApplicationData b -> b
  | _ -> B.empty

(** The application-data bytes an in-flight payload carries — the byte delta of
    the message the sender appended to its event log when it emitted the payload. **)
let app_bytes_of (p:tls_payload) : GTot B.bytes =
  app_bytes_delta p.pl_sent

(** Phase 2 — the pending-plaintext field is pinned empty on both endpoints.
    `app_pending_plaintext` is assigned exactly once (to `B.empty`, in
    `empty_application_state`) and never written by any step, so this is a trivial
    per-endpoint inductive property.  It is what forces the (unimplemented)
    `LocalDeliverApplicationData` hop to deliver only `B.empty`, keeping the
    received byte STREAM (concatenation) unchanged in the LOCAL case of
    `app_pairing`. **)
let app_pending_empty (s:tls_system_state) : prop =
  Seq.equal s.client.CS.cs_model.CS.model_application.CS.app_pending_plaintext B.empty /\
  Seq.equal s.server.CS.cs_model.CS.model_application.CS.app_pending_plaintext B.empty

(** ─────────────────────────────────────────────────────────────────────────
    Application-data STREAM pairing (the analogue of `byte_pairing` at the
    application byte-stream level) and the end-to-end STREAM-INTEGRITY payoff.

    `app_pairing` says: each endpoint's SENT application byte stream equals the
    peer's RECEIVED application byte stream plus whatever application bytes are
    currently in flight (`app_bytes_of p`); at `Quiet` (nothing in flight) it
    collapses to exact stream equality in both directions.  This mirrors
    `byte_pairing` exactly, one level up (streams instead of raw records).

    NOTE (status): `app_pairing` is provided as a STANDALONE definition together
    with the fully-verified PURE reduction `lemma_app_pairing_implies_stream_integrity`
    below, which shows it entails end-to-end stream integrity.  It is NOT (yet) a
    conjunct of `tls_system_inv`: its inductive DELIVERY case requires an
    application-data decode-faithfulness bridge that is currently a genuine gap in
    this model — see the extended note above `lemma_app_pairing_implies_stream_integrity`
    for the precise obstruction.
    ───────────────────────────────────────────────────────────────────────── **)
let app_pairing (s:tls_system_state) : prop =
  let cs = app_stream_sent s.client in
  let cr = app_stream_received s.client in
  let ss = app_stream_sent s.server in
  let sr = app_stream_received s.server in
  match s.channel with
  | MP.Quiet ->
    Seq.equal cs sr /\ Seq.equal ss cr
  | MP.ToServer p ->
    Seq.equal cs (B.append sr (app_bytes_of p)) /\ Seq.equal ss cr
  | MP.ToClient p ->
    Seq.equal ss (B.append cr (app_bytes_of p)) /\ Seq.equal cs sr

(** `pre` is a prefix of the byte string `full`. **)
let is_byte_prefix (pre full:B.bytes) : prop =
  exists (rest:B.bytes). Seq.equal full (B.append pre rest)

(** End-to-end application-data STREAM INTEGRITY: each endpoint's received
    application byte stream is a prefix of the peer's sent application byte
    stream. **)
let stream_integrity_holds (s:tls_system_state) : prop =
  is_byte_prefix (app_stream_received s.client) (app_stream_sent s.server) /\
  is_byte_prefix (app_stream_received s.server) (app_stream_sent s.client)

(** Appending the empty byte string is the identity (extensional). **)
let lemma_append_empty_r (x:B.bytes)
  : Lemma (Seq.equal (B.append x B.empty) x)
  = ()

(** ─────────────────────────────────────────────────────────────────────────
    PURE reduction: the stream-pairing invariant entails end-to-end stream
    integrity.  In every channel state the in-flight application delta (or
    `B.empty` at `Quiet`) is exactly the `rest` witnessing the prefix.  This
    lemma is fully proved and reduces the open end-to-end goal to the single
    invariant `app_pairing`.

    WHY `app_pairing` IS NOT YET A `tls_system_inv` CONJUNCT (the genuine gap).
    Adding `app_pairing` requires proving it INDUCTIVELY preserved by all six
    step families.  Send and local cases are within reach (send grows the
    sender's `app_sent` stream by exactly `app_bytes_of p` via `tls_emit`'s
    event-log equation; local leaves `app_received` unchanged up to `B.empty`
    chunks by `app_pending_empty`).  The DELIVERY case is blocked:

      * The receiver's `app_received` stream grows by the bytes of the message
        IT decodes from the in-flight wire, so preservation needs
        `decoded_message == p.pl_sent` for application-data records — a
        decode-FAITHFULNESS fact.
      * The natural bridge (establish faithfulness at SEND time, when the channel
        is `Quiet`, and merely consume it at delivery, as `channel_consistent`
        does) FAILS for application data: a client legally sends app data at
        `model_control == ControlApplicationData`, but `client_clean` then only
        gives the peer `server_post_cf` (which includes `HsClientFinishedReceived`
        — the server has RECEIVED but not yet locally VERIFIED the client Finished).
        So the quiescent application-traffic-key AGREEMENT
        (`lemma_ready_quiescent_agrees`) is NOT available at such sends: in real
        TLS 1.3 the client may send app data before the server verifies CF.
      * Even with key agreement, the existing seal→decode bridges
        (`TLS13.Impl.Driver.Pairing.fsti`) additionally require record
        sequence-number ALIGNMENT (a new "record-count pairing" invariant, not
        present) and a decode-DETERMINISM/INJECTIVITY lemma (buildable but not
        present).  Finally the AEAD TCB (`TLS13.Crypto.Spec.fsti`) assumes only
        open-after-seal CORRECTNESS, with no authenticity/wrong-key-fails or
        injectivity lemma, so a decode by a not-yet-ready receiver is left
        unconstrained by the model.

    Closing this would need new infrastructure (record-count pairing + decode
    determinism) and EITHER an AEAD-authenticity crypto assumption (a TCB change,
    out of scope) OR a global deadlock argument that no legal app-data delivery
    to a pre-`ControlApplicationData` receiver can occur.  Rather than admit any
    of these, `app_pairing` is left as a standalone definition with this proven
    reduction to the end-to-end property.
    ───────────────────────────────────────────────────────────────────────── **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_app_pairing_implies_stream_integrity (s:tls_system_state)
  : Lemma (requires app_pairing s)
          (ensures stream_integrity_holds s)
  = let cs = app_stream_sent s.client in
    let cr = app_stream_received s.client in
    let ss = app_stream_sent s.server in
    let sr = app_stream_received s.server in
    // stream_integrity needs: is_byte_prefix cr ss  and  is_byte_prefix sr cs.
    lemma_append_empty_r cr;   // Seq.equal (B.append cr B.empty) cr
    lemma_append_empty_r sr;   // Seq.equal (B.append sr B.empty) sr
    match s.channel with
    | MP.Quiet ->
      // cs == sr and ss == cr: both prefixes witnessed by B.empty.
      assert (Seq.equal cs (B.append sr B.empty));
      assert (Seq.equal ss (B.append cr B.empty))
    | MP.ToServer p ->
      // cs == sr ++ (app_bytes_of p): server-received prefixes client-sent;
      // ss == cr: client-received prefixes server-sent (rest B.empty).
      assert (Seq.equal cs (B.append sr (app_bytes_of p)));
      assert (Seq.equal ss (B.append cr B.empty))
    | MP.ToClient p ->
      assert (Seq.equal ss (B.append cr (app_bytes_of p)));
      assert (Seq.equal cs (B.append sr B.empty))
#pop-options

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
  (client_ready s /\ MP.Quiet? s.channel ==> server_post_cf s)

(** The inductive structural invariant. **)
let tls_system_inv (s:tls_system_state) : prop =
  client_stage_ok s.client /\
  server_stage_ok s.server /\
  SMR.connection_state_consistent s.client /\
  SMR.connection_state_consistent s.server /\
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
  client_ksp s /\
  server_ksp s /\
  client_e2e s /\
  server_e2e s /\
  client_clean s /\
  app_pending_empty s /\
  protected_witnesses_ok s

(** Application record-epoch reachable-shape bridge (sub-goal (a)).  The
    orphaned-but-inductive shapes from `TLS13.ConnectionState.Lemmas` have been
    strengthened so that at `ControlApplicationData` they carry
    `application_record_keys_installed_for_role` for the endpoint's own role, and
    that shape is established purely from `connection_state_consistent` (already an
    invariant conjunct) via RTC closure.  So no new `tls_system_inv` conjunct is
    needed for the KEY-INSTALLATION half of driver readiness:
    `CSL.lemma_connection_appdata_keys_installed_for_role` bridges the existing
    `connection_state_consistent` conjunct to `application_record_keys_installed_for_role`.

    CLIENT: the bridge completes `client_ready` outright, because `client_e2e`
    (an *unconditional* invariant conjunct) supplies `client_end_to_end_invariant`
    and the bridge supplies the app record keys.

    SERVER: `server_ready` (= `server_driver_application_ready`) additionally
    requires `server_end_to_end_invariant`, which is only carried by the invariant
    conditionally (`server_e2e s = server_config_valid_e2e s.server ==>
    server_end_to_end_invariant s.server`).  `server_config_valid_e2e` demands
    `B.length server_certificate_chain <= max_server_certificate_chain_len` (16610),
    but spec-level reachability only bounds a sent certificate chain by the *wire*
    limit `certificate_chain_max_bytes` (32768); since the server config is
    immutable and unconstrained by the existing flagship's entry precondition, it
    is NOT derivable from reachability alone.

    RESOLUTION (Option A): the stream-integrity development carries
    `server_config_valid_e2e s.server` as its OWN invariant conjunct
    (`tls_stream_inv`, below), established at the initial state from a
    valid-server-config entry hypothesis added to the *new* stream-integrity
    theorem only (mirroring the existing client-side
    `supported_client_config_wire_profile cfg_c`), and trivially preserved because
    the config is immutable.  Crucially this conjunct is kept OUT of the shared
    `tls_system_inv` so the existing flagship (`lemma_flagship_record_material_
    agreement`, via `lemma_reachable_inv`) keeps its weaker entry precondition. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_appdata_implies_client_ready
  (s:tls_system_state)
  : Lemma
      (requires
        client_e2e s /\
        s.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        SMR.connection_state_consistent s.client /\
        ctrl s.client == CS.ControlApplicationData)
      (ensures client_ready s)
= CSL.lemma_connection_appdata_keys_installed_for_role CS.ClientEndpoint s.client

(** Server readiness at appdata, given the config-validity hypothesis (supplied
    by the `tls_stream_inv` conjunct below).  `server_e2e s` + validity discharges
    `server_end_to_end_invariant`; the bridge supplies the app record keys. **)
let lemma_appdata_implies_server_ready
  (s:tls_system_state)
  : Lemma
      (requires
        server_e2e s /\
        server_config_valid_e2e s.server /\
        s.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        SMR.connection_state_consistent s.server /\
        ctrl s.server == CS.ControlApplicationData)
      (ensures server_ready s)
= CSL.lemma_connection_appdata_keys_installed_for_role CS.ServerEndpoint s.server

(** ── OPTION-B SEAM ──────────────────────────────────────────────────────────
    The single readiness predicate the stream-integrity development depends on.
    Every use of `client_ready`/`server_ready` downstream is routed through this
    predicate and the one lemma establishing it
    (`lemma_appdata_implies_app_endpoints_ready`).  Option B (decoupling key
    agreement from full driver-readiness) later amounts to RE-PROVING that one
    lemma from "both endpoints at appdata with app record keys installed" — the
    rest of the development need not change.

    Why the cert-chain bound folded into `server_ready` is only PROOF-technically
    required: application-traffic key agreement is derived from the shared
    handshake transcript (through the server Finished) and is *semantically
    independent of the server certificate's length*.  The bound enters solely
    because `server_driver_application_ready` bundles in `server_end_to_end_
    invariant`, whose `server_state_core_correct` component happens to record the
    impl-side chain-length bound (16610).  That is exactly why B is worth
    attempting: it removes a proof-technical dependency that has no semantic force
    on the property being proved. **)
let app_endpoints_ready (s:tls_system_state) : prop =
  client_ready s /\ server_ready s

let lemma_appdata_implies_app_endpoints_ready
  (s:tls_system_state)
  : Lemma
      (requires
        tls_system_inv s /\
        server_config_valid_e2e s.server /\
        ctrl s.client == CS.ControlApplicationData /\
        ctrl s.server == CS.ControlApplicationData)
      (ensures app_endpoints_ready s)
= lemma_appdata_implies_client_ready s;
  lemma_appdata_implies_server_ready s
#pop-options


(** The wire-level EMISSION interface.  Both endpoints are
    `CS.connection_state`s stepping by the same kind of relation, so the client
    and the server emit in exactly the same way and `emit_c` and `emit_s` are THE
    SAME function.  `tls_emit c c' out p` says: the step emitted exactly one
    record; the payload's raw bytes are that record's serialization; the payload
    remembers the sender's model at emission time; and the sender's event log grew
    by exactly the `sent` event the payload records. **)
let tls_emit (c c':CS.connection_state)
             (out:SM.step_output CW.wire_message EAPI.local_output)
             (p:tls_payload) : prop =
  (exists (w:CW.wire_message). out.SM.so_wire_outputs == [w]) /\
  p.pl_raw == emitted_raw out /\
  p.pl_snap == c.CS.cs_model /\
  c'.CS.cs_event_log == c.CS.cs_event_log @ [SMKM.sent_tls_event p.pl_sent]

(** The DELIVERY interface: an in-flight payload delivers whichever wire message
    serializes to its raw bytes.  This is what makes a delivery feed the receiver
    REAL wire bytes, which the receiver parses into its own (body=full) message. **)
let tls_carries (p:tls_payload) (w:CW.wire_message) : prop =
  Seq.equal (CW.wire_serialize w) p.pl_raw

(** The TLS system as an instance of the generic MACHINE product
    (`Common.MachineProduct`), which itself feeds `Common.SystemProduct`'s
    single-slot directed-channel discipline.

    Nothing about message delivery is written here any more.  We supply only the
    two endpoints' step relations — the OFFICIAL canonical `EC.client_step` and
    `ES.server_step` VERBATIM, both over the SAME wire type `CW.wire_message` —
    plus the tiny channel interface (`tls_emit` / `tls_carries`).  No initial
    state is needed: where a run starts is `initial_tls_system cfg_c cfg_s`
    above, parameterized by the real configs, and the per-endpoint reachability
    conjuncts of `tls_system_inv` anchor at each endpoint's own `CS.initial cfg`.
    TLS has no fused
    receive-and-respond, so `MP.full_duplex_moves` enables exactly the six
    families this system has always had and leaves `server_serve` disabled.

    The six move families, and hence `tls_sys_step`, are then DERIVED: each is one
    `sm_step` of one endpoint plus channel bookkeeping. **)
let tls_machine_iface
  : MP.machine_iface
      CS.connection_state CS.connection_state tls_payload
      CW.wire_message CTy.client_local_event CTy.server_local_event EAPI.local_output = {
  cstep   = EC.client_step #CTy.client_local_event;
  sstep   = ES.server_step #CTy.server_local_event;
  emit_c  = tls_emit;
  emit_s  = tls_emit;
  carries = tls_carries;
  moves   = MP.full_duplex_moves;
}

(** ─────────────────────────────────────────────────────────────────────────
    The six transition shapes, DERIVED from the two endpoint state machines.

    These are no longer hand-written relations: each is the corresponding generic
    family of `Common.MachineProduct` at `tls_machine_iface`, i.e. exactly one
    step of the official canonical relation, VERBATIM (no wrapper, no pin), plus
    channel bookkeeping.  A LocalEvent that emits a record is a "send", one that
    emits nothing is a "local"; deliveries consume the matching in-flight raw and
    return the channel to quiet.  The shapes do NOT restrict rekeying: a raw
    canonical step is taken VERBATIM (the no-rekeying discipline is folded into
    the flagship theorem's antecedent and re-established on reachable states via
    the combined invariant below, not pinned per-step).

    NOTE (the one structural difference from the hand-written version): the
    quiet-channel precondition is no longer repeated inside the send/local
    families — `SP.product_step` supplies it once and for all.  `tls_sys_step` is
    therefore UNCHANGED AS A RELATION, but a helper lemma that takes a bare family
    as its hypothesis and used to read the gate off that hypothesis now takes an
    explicit `MP.Quiet? a.channel` precondition. **)

let tls_step_client_send (a b:tls_system_state) : prop =
  MP.mp_client_send tls_machine_iface a b

let tls_step_server_send (a b:tls_system_state) : prop =
  MP.mp_server_send tls_machine_iface a b

let tls_step_deliver_to_server (a b:tls_system_state) : prop =
  MP.mp_deliver_to_server tls_machine_iface a b

let tls_step_deliver_to_client (a b:tls_system_state) : prop =
  MP.mp_deliver_to_client tls_machine_iface a b

let tls_step_client_local (a b:tls_system_state) : prop =
  MP.mp_client_local tls_machine_iface a b

let tls_step_server_local (a b:tls_system_state) : prop =
  MP.mp_server_local tls_machine_iface a b

(** A single honest system transition — the generic machine product. **)
let tls_sys_step (a b:tls_system_state) : prop =
  MP.machine_step tls_machine_iface a b

(** ─────────────────────────────────────────────────────────────────────────
    Shape recovery for the two SEND families.

    The derived families bundle the emitted record and the sender-side ghost
    material into a single `tls_payload`; the endpoint-level lemmas below consume
    the unbundled existential instead.  The two directions are equivalent by pure
    unfolding of `MP.mp_*_send` at `tls_machine_iface` (the payload record is
    reconstructed from its three projections); stating that once here keeps the
    individual proofs from each having to redo it.
    ───────────────────────────────────────────────────────────────────────── **)

let client_send_shape (a b:tls_system_state) : prop =
  exists (local:CTy.client_local_event) (c':CS.connection_state)
         (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
         (sent:M.tls_message).
    EC.client_step a.client (SM.LocalEvent local) c' out /\
    out.SM.so_wire_outputs == [w] /\
    c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
    b == { a with client = c'; channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent }

let server_send_shape (a b:tls_system_state) : prop =
  exists (local:CTy.server_local_event) (s':CS.connection_state)
         (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
         (sent:M.tls_message).
    ES.server_step a.server (SM.LocalEvent local) s' out /\
    out.SM.so_wire_outputs == [w] /\
    s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
    b == { a with server = s'; channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent }

#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_client_send_shape (a b:tls_system_state)
  : Lemma (requires tls_step_client_send a b)
          (ensures client_send_shape a b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (p:tls_payload).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      Cons? out.SM.so_wire_outputs /\
      tls_emit a.client c' out p /\
      b == ({ a with client = c'; channel = MP.ToServer p } <: tls_system_state)
    returns client_send_shape a b
    with _pf.
      (eliminate exists (w:CW.wire_message). out.SM.so_wire_outputs == [w]
       returns client_send_shape a b
       with _pw.
         (assert (p == ({ pl_raw = emitted_raw out;
                          pl_snap = a.client.CS.cs_model;
                          pl_sent = p.pl_sent } <: tls_payload));
          assert (b == ({ a with client = c';
                                 channel = tls_to_server (emitted_raw out)
                                             a.client.CS.cs_model p.pl_sent }
                        <: tls_system_state))))

let lemma_server_send_shape (a b:tls_system_state)
  : Lemma (requires tls_step_server_send a b)
          (ensures server_send_shape a b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output)
                     (p:tls_payload).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      Cons? out.SM.so_wire_outputs /\
      tls_emit a.server s' out p /\
      b == ({ a with server = s'; channel = MP.ToClient p } <: tls_system_state)
    returns server_send_shape a b
    with _pf.
      (eliminate exists (w:CW.wire_message). out.SM.so_wire_outputs == [w]
       returns server_send_shape a b
       with _pw.
         (assert (p == ({ pl_raw = emitted_raw out;
                          pl_snap = a.server.CS.cs_model;
                          pl_sent = p.pl_sent } <: tls_payload));
          assert (b == ({ a with server = s';
                                 channel = tls_to_client (emitted_raw out)
                                             a.server.CS.cs_model p.pl_sent }
                        <: tls_system_state))))
#pop-options

(** Shape recovery for the two DELIVER families: the in-flight payload record is
    split back into its three projections. **)

let deliver_to_server_shape (a b:tls_system_state) : prop =
  exists (wire:CW.wire_message) (s':CS.connection_state)
         (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
         (snap:CS.connection_model) (sent:M.tls_message).
    a.channel == tls_to_server raw snap sent /\
    Seq.equal (CW.wire_serialize wire) raw /\
    ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
    b == { a with server = s'; channel = MP.Quiet }

let deliver_to_client_shape (a b:tls_system_state) : prop =
  exists (wire:CW.wire_message) (c':CS.connection_state)
         (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
         (snap:CS.connection_model) (sent:M.tls_message).
    a.channel == tls_to_client raw snap sent /\
    Seq.equal (CW.wire_serialize wire) raw /\
    EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
    b == { a with client = c'; channel = MP.Quiet }

#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_deliver_to_server_shape (a b:tls_system_state)
  : Lemma (requires tls_step_deliver_to_server a b)
          (ensures deliver_to_server_shape a b)
  = eliminate exists (p:tls_payload) (w:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      a.channel == MP.ToServer p /\
      tls_carries p w /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent w) s' out /\
      b == ({ a with server = s'; channel = MP.Quiet } <: tls_system_state)
    returns deliver_to_server_shape a b
    with _pf.
      (assert (p == ({ pl_raw = p.pl_raw; pl_snap = p.pl_snap; pl_sent = p.pl_sent }
                     <: tls_payload));
       assert (a.channel == tls_to_server p.pl_raw p.pl_snap p.pl_sent))

let lemma_deliver_to_client_shape (a b:tls_system_state)
  : Lemma (requires tls_step_deliver_to_client a b)
          (ensures deliver_to_client_shape a b)
  = eliminate exists (p:tls_payload) (w:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      a.channel == MP.ToClient p /\
      tls_carries p w /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent w) c' out /\
      b == ({ a with client = c'; channel = MP.Quiet } <: tls_system_state)
    returns deliver_to_client_shape a b
    with _pf.
      (assert (p == ({ pl_raw = p.pl_raw; pl_snap = p.pl_snap; pl_sent = p.pl_sent }
                     <: tls_payload));
       assert (a.channel == tls_to_client p.pl_raw p.pl_snap p.pl_sent))
#pop-options

(** The converse direction for a delivery to the server: unbundled components
    assemble into the derived family. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_deliver_to_server_intro
  (a b:tls_system_state) (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        a.channel == tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
        b == { a with server = s'; channel = MP.Quiet })
      (ensures tls_step_deliver_to_server a b)
  = let pl : tls_payload = { pl_raw = raw; pl_snap = snap; pl_sent = sent } in
    MP.lemma_mp_deliver_to_server_intro tls_machine_iface a b pl wire s' out
#pop-options

(** The converse direction for a server-internal step. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_server_local_intro
  (a b:tls_system_state) (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [] /\
        b == { a with server = s' })
      (ensures tls_step_server_local a b)
  = MP.lemma_mp_server_local_intro tls_machine_iface a b local s' out
#pop-options

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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires SMR.connection_state_consistent st0 /\ EC.client_step st0 e st1 out)
      (ensures
        SMR.connection_state_consistent st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      SMR.connection_state_consistent st1 /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires SMR.connection_state_consistent st0 /\ ES.server_step st0 e st1 out)
      (ensures
        SMR.connection_state_consistent st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      SMR.connection_state_consistent st1 /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 e st1 out /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 e st1 out /\
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

(** STAGE 2A — `model_ksp` preservation for a client / server step. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_client_step_ksp
  (a c':CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step a e c' out /\ PC.model_ksp a.CS.cs_model)
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step a e s' out /\ PC.model_ksp a.CS.cs_model)
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 (SM.LocalEvent local) st1 out)
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        st0.CS.cs_model.CS.model_handshake.CS.hs_server_hello)
  = let api = CTy.client_local_event_api local in
    eliminate exists conn_ev raw_sent.
      CTy.client_api_event_matches st0 api conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta st0
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } st1 /\
      SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
      SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 (SM.LocalEvent local) st1 out)
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello)
  = let api = CTy.server_local_event_api local in
    eliminate exists conn_ev raw_sent.
      CTy.server_api_event_matches api conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta st0
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } st1 /\
      SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
      SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty
    returns
      st1.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_client_hello
    with _pf.
      (assert (forall (dir:CS.direction) (ch:GCH.clientHello).
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
  = assert (SMR.connection_state_evolves (CS.initial cfg_c) (CS.initial cfg_c));
    assert (SMR.connection_state_evolves (CS.initial cfg_s) (CS.initial cfg_s));
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
    // app_pending_empty: fresh endpoints start from empty_application_state.
    assert (app_pending_empty (initial_tls_system cfg_c cfg_s))

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
#push-options "--fuel 1 --ifuel 4 --z3rlimit 120"
let lemma_cc_client_send
  (a:tls_system_state)
  (local:CTy.client_local_event) (c':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\ MP.Quiet? a.channel /\
        EC.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        channel_consistent
          ({ a with client = c';
                    channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent }))
  = let b = { a with client = c';
                     channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent } in
    lemma_serialize_all_single w;
    let api = CTy.client_local_event_api local in
    eliminate exists conn_ev raw_sent.
      CTy.client_api_event_matches a.client api conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta a.client
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } c' /\
      SMCan.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev raw_sent /\
      SMCan.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev B.empty
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
  : Lemma (requires tls_system_inv a /\ MP.Quiet? a.channel /\ tls_step_client_send a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   channel_consistent b /\ hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_wire_facts_client_send a b =
  lemma_client_send_shape a b;
  eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                   (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                   (sent:M.tls_message).
    EC.client_step a.client (SM.LocalEvent local) c' out /\
    out.SM.so_wire_outputs == [w] /\
    c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
    b == { a with client = c'; channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent }
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
#push-options "--fuel 1 --ifuel 4 --z3rlimit 120"
let lemma_cc_server_send
  (a:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\ MP.Quiet? a.channel /\
        ES.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        channel_consistent
          ({ a with server = s';
                    channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent }))
  = let b = { a with server = s';
                     channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent } in
    lemma_serialize_all_single w;
    let api = CTy.server_local_event_api local in
    eliminate exists conn_ev raw_sent.
      CTy.server_api_event_matches api conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta a.server
        { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty } s' /\
      SMCan.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev raw_sent /\
      SMCan.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev B.empty
    returns channel_consistent b
    with _pf. (
      Seq.lemma_eq_elim (emitted_raw out) raw_sent;
      let raw = emitted_raw out in
      introduce
        (exists (some_sh:GSH.serverHello).
           B.length (W.serialize_handshake (M.ServerHello some_sh)) <= 16640 /\
           CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello some_sh)) raw)
        ==>
        (match s'.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
         | Some server_sh ->
           CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw
         | None -> False)
      with _pa. (
        match conn_ev with
        | CS.ConnNetworkEvent nmsg ->
          (match nmsg.CL.message_value with
           | M.TlsHandshake (M.ServerHello sh) ->
             // SH send case: consequent holds directly.
             assert (s'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh);
             assert (CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello sh)) raw_sent)
           | _ ->
             // Non-SH sends are protected (Application_data format).
             // The antecedent gives parse_record_wire raw == Some (Handshake, ...) via
             // the wire bound + cleartext roundtrip, contradicting the protected send's
             // parse_record_wire raw == Some (Application_data, ...).
             assert (nmsg.CL.message_direction == CL.Sent);
             assert (CS.network_message_is_cleartext CL.Sent nmsg.CL.message_value == false);
             CSL.lemma_legal_connection_delta_protected_parse_prefix a.server
               { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
                 CS.delta_raw_received = B.empty } s';
             W.lemma_parse_record_implies_parse_record_wire raw;
             // Now: parse_record_wire raw == Some (Application_data, _, _)
             eliminate exists (some_sh:GSH.serverHello).
               B.length (W.serialize_handshake (M.ServerHello some_sh)) <= 16640 /\
               CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello some_sh)) raw
             returns _
             with _pw. (
               WStep.lemma_cleartext_server_hello_parse_record some_sh raw;
               // parse_record_wire raw == Some (Handshake, ...) contradicts
               // parse_record_wire raw == Some (Application_data, ...).
               ()))
        | CS.ConnLocalEvent _ ->
          // ConnLocalEvent requires raw_sent == empty (event_raw_delta_legal),
          // but raw_sent = serialize_all [w] is non-empty.  Contradiction.
          assert (CS.legal_connection_delta a.server
            { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
              CS.delta_raw_received = B.empty } s');
          assert (CS.event_raw_delta_legal a.server.CS.cs_model conn_ev raw_sent B.empty);
          // raw and raw_sent are the same (from Seq.lemma_eq_elim above)
          assert (raw == raw_sent);
          // raw_sent = emitted_raw out = serialize_all [w] = wire_serialize w
          WStep.lemma_wire_serialize_nonempty w;
          // B.length (wire_serialize w) > 0 == B.length raw > 0 == B.length raw_sent > 0
          // But event_raw_delta_legal for ConnLocalEvent gives Seq.equal raw_sent B.empty
          // (i.e. B.length raw_sent == 0).  Contradiction.
          ()))
#pop-options

(** FACTS 1–5 across a server SEND (server emits one record; needs field
    stability + carried cleartext for the channel at SH-send). **)
val lemma_wire_facts_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ MP.Quiet? a.channel /\ tls_step_server_send a b)
          (ensures ch_wire_equiv b /\ sh_wire_equiv b /\ hello_key_shares_ok b /\
                   channel_consistent b /\ hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_wire_facts_server_send a b =
  lemma_server_send_shape a b;
  eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                   (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                   (sent:M.tls_message).
    ES.server_step a.server (SM.LocalEvent local) s' out /\
    out.SM.so_wire_outputs == [w] /\
    s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
    b == { a with server = s'; channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent }
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
  lemma_deliver_to_server_shape a b;
  eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                   (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                   (snap:CS.connection_model) (sent:M.tls_message).
    a.channel == tls_to_server raw snap sent /\
    Seq.equal (CW.wire_serialize wire) raw /\
    ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
    b == { a with server = s'; channel = MP.Quiet }
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
       SMCan.sent_event_nonempty_seal_projection a.server.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection a.server.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  (client_sh:GSH.serverHello)
  : Lemma
      (requires
        tls_system_inv a /\
        a.channel == tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
        c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        c'.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
          a.client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh)) raw /\
        b == { a with client = c'; channel = MP.Quiet })
      (ensures sh_wire_equiv b /\ hello_key_shares_ok b /\ hello_coupling b)
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_deliver_to_client_sh_bridge a b wire c' out raw snap sent client_sh =
  assert (channel_consistent a);
  assert (SMR.connection_state_consistent a.server);
  // c' (the stepped client) is consistent, so its stored ServerHello satisfies the
  // single-record wire bound (client-receive legality carries it) — supplying the
  // hypothesis the parse-record lemma now needs on the unbounded generated SH type.
  lemma_client_step_pres a.client c' (SM.WireEvent wire) out;
  assert (SMR.connection_state_consistent c');
  WStep.lemma_consistent_server_hello_wire_bound c';
  assert (B.length (W.serialize_handshake (M.ServerHello client_sh)) <= 16640);
  // received cleartext for client_sh is a plain cleartext (SH is not HRR).
  assert (CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw);
  // Fire channel_consistent a's ClientEndpoint branch directly:
  // `received_cleartext_tls_message_raw (SH client_sh) raw` instantiates the antecedent.
  assert (CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw);
  assert (Some? (hsf a.server).CS.hs_server_hello);
  let server_sh : GSH.serverHello = Some?.v (hsf a.server).CS.hs_server_hello in
  WStep.lemma_consistent_server_hello_wire_bound a.server;
  assert (B.length (W.serialize_handshake (M.ServerHello server_sh)) <= 16640);
  assert (CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw);
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
  lemma_deliver_to_client_shape a b;
  eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                   (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                   (snap:CS.connection_model) (sent:M.tls_message).
    a.channel == tls_to_client raw snap sent /\
    Seq.equal (CW.wire_serialize wire) raw /\
    EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
    b == { a with client = c'; channel = MP.Quiet }
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
       SMCan.sent_event_nonempty_seal_projection a.client.CS.cs_model conn_ev
         (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
       SMCan.received_event_nonempty_decode_projection a.client.CS.cs_model conn_ev
         (CW.wire_serialize wire) /\
       EC.network_input_message_projection a.client wire msg /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
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
         // EC.network_input_message_projection for cleartext SH gives received_cleartext:
         assert (CS.received_cleartext_tls_message_raw
                   (M.TlsHandshake (M.ServerHello client_sh)) raw);
         assert (c'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh);
         lemma_deliver_to_client_sh_bridge a b wire c' out raw snap sent client_sh
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
                   (out:SM.step_output CW.wire_message EAPI.local_output).
    EC.client_step a.client (SM.LocalEvent local) c' out /\
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
                   (out:SM.step_output CW.wire_message EAPI.local_output).
    ES.server_step a.server (SM.LocalEvent local) s' out /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        client_byte_reachable a /\ EC.client_step a.client ev c' out /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        server_byte_reachable a /\ ES.server_step a.server ev s' out /\
        s'.CS.cs_model.CS.model_config == a.server.CS.cs_model.CS.model_config)
      (ensures
        WStep.server_reachable (CS.initial s'.CS.cs_model.CS.model_config) s')
  = WStep.lemma_server_reachable_step
      (CS.initial a.server.CS.cs_model.CS.model_config) a.server s' ev out
#pop-options

(** STAGE 2B — a client step preserves the client end-to-end invariant (e2e).
    e2e is a genuine per-endpoint inductive property (`CTy2.client_end_to_end_invariant`
    = client_state_correct /\ raw_to_message_replay_consistent).  A `EC.client_step`
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 e st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CTy2.client_end_to_end_invariant st0)
      (ensures CTy2.client_end_to_end_invariant st1)
  = assert (exists (d:CS.connection_delta).
        CS.legal_connection_delta st0 d st1 /\
        SMCan.sent_event_nonempty_seal_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
        SMCan.received_event_nonempty_decode_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received);
    eliminate exists (d:CS.connection_delta).
        CS.legal_connection_delta st0 d st1 /\
        SMCan.sent_event_nonempty_seal_projection
          st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
        SMCan.received_event_nonempty_decode_projection
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
    invariant.  Mirrors `lemma_client_step_e2e`: a `ES.server_step` supplies a
    legal connection delta with the sent/received non-empty projection witnesses,
    the `CSL` delta lemmas carry each replay-consistency component across the step,
    and config immutability transports the validity guard.  Because the guard is on
    the immutable config, the real work only fires when the pre-state is already
    valid; otherwise the post-guard is false and the obligation is vacuous. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_server_step_e2e
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 e st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (server_config_valid_e2e st0 ==> ST.server_end_to_end_invariant st0))
      (ensures
        (server_config_valid_e2e st1 ==> ST.server_end_to_end_invariant st1))
  = introduce server_config_valid_e2e st1 ==> ST.server_end_to_end_invariant st1
    with _guard1.
    (
      assert (exists (d:CS.connection_delta).
          CS.legal_connection_delta st0 d st1 /\
          SMCan.sent_event_nonempty_seal_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
          SMCan.received_event_nonempty_decode_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_received);
      eliminate exists (d:CS.connection_delta).
          CS.legal_connection_delta st0 d st1 /\
          SMCan.sent_event_nonempty_seal_projection
            st0.CS.cs_model d.CS.delta_event d.CS.delta_raw_sent /\
          SMCan.received_event_nonempty_decode_projection
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\ MP.Quiet? a.channel /\
        EC.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        byte_pairing
          ({ a with client = c';
                    channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent }))
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\ MP.Quiet? a.channel /\
        ES.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w])
      (ensures
        byte_pairing
          ({ a with server = s';
                    channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent }))
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\
        a.channel == tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out)
      (ensures byte_pairing ({ a with server = s'; channel = MP.Quiet }))
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
  (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        byte_pairing a /\
        a.channel == tls_to_client raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out)
      (ensures byte_pairing ({ a with client = c'; channel = MP.Quiet }))
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        byte_pairing a /\ MP.Quiet? a.channel /\
        EC.client_step a.client (SM.LocalEvent local) c' out /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        byte_pairing a /\ MP.Quiet? a.channel /\
        ES.server_step a.server (SM.LocalEvent local) s' out /\
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

(** ─────────────────────────────────────────────────────────────────────────
    Phase 2 — `app_pending_empty` preservation.

    `app_pending_plaintext` is written exactly once (`empty_application_state`)
    and carried unchanged by every model step, so it stays empty on both
    endpoints.  The two step-level sublemmas below establish the field is
    preserved by any legal model step; the endpoint wrappers lift that through
    the (existentially bundled) legal delta of a canonical step.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_step_local_preserves_pending
  (model0:CS.connection_model) (ev:CS.local_event) (model1:CS.connection_model)
  : Lemma (requires CS.step_local_event model0 ev == Some model1)
          (ensures model1.CS.model_application.CS.app_pending_plaintext ==
                   model0.CS.model_application.CS.app_pending_plaintext)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_step_tls_preserves_pending
  (model0:CS.connection_model) (dir:CS.direction) (msg:M.tls_message) (model1:CS.connection_model)
  : Lemma (requires CS.step_tls_message model0 dir msg == Some model1)
          (ensures model1.CS.model_application.CS.app_pending_plaintext ==
                   model0.CS.model_application.CS.app_pending_plaintext)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_step_model_preserves_pending
  (model0:CS.connection_model) (ev:CS.conn_event) (model1:CS.connection_model)
  : Lemma (requires CS.step_model model0 ev == Some model1)
          (ensures model1.CS.model_application.CS.app_pending_plaintext ==
                   model0.CS.model_application.CS.app_pending_plaintext)
  = match ev with
    | CS.ConnNetworkEvent msg ->
      lemma_step_tls_preserves_pending model0 msg.CL.message_direction msg.CL.message_value model1
    | CS.ConnLocalEvent local ->
      lemma_step_local_preserves_pending model0 local model1
#pop-options

(** A canonical client step preserves the pending-plaintext field: the step
    supplies a legal connection delta, whose model transition carries the field
    unchanged. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_step_preserves_pending
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 e st1 out)
      (ensures
        st1.CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
        st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      st1.CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
      st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext
    with _pf.
      lemma_step_model_preserves_pending st0.CS.cs_model d.CS.delta_event st1.CS.cs_model
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_step_preserves_pending
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 e st1 out)
      (ensures
        st1.CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
        st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns
      st1.CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
      st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext
    with _pf.
      lemma_step_model_preserves_pending st0.CS.cs_model d.CS.delta_event st1.CS.cs_model
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
        SMR.connection_state_consistent st /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
  = let p = PC.client_appdata_appkeys_st in
    let stable : squash (forall (x y:CS.connection_state).
        {:pattern (p y); (SMR.connection_state_single_step x y)}
        p x /\ SMR.connection_state_single_step x y ==> p y) =
      introduce forall (x y:CS.connection_state).
        p x /\ SMR.connection_state_single_step x y ==> p y
      with introduce _ ==> _ with _.
        (eliminate exists (d:CS.connection_delta). CS.legal_connection_delta x d y
         returns p y
         with _pd. PC.lemma_client_appdata_appkeys_delta x y d) in
    RTC.stable_on_closure SMR.connection_state_single_step p stable;
    assert (p (CS.initial st.CS.cs_model.CS.model_config));
    assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
    assert (p st)
#pop-options

(** Keys bridge: a consistent client carrying `client_at_appdata` has both
    application-traffic secrets installed.  Wraps the reachability lemma behind a
    guard so the call site only needs consistency + the client role. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_surface_client_appkeys (s:tls_system_state)
  : Lemma
      (requires
        SMR.connection_state_consistent s.client /\
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
      (requires SMC.conn_events_no_key_update (FStar.List.Tot.append l [ev]) == true)
      (ensures SMC.conn_event_is_key_update ev == false)
      (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> lemma_no_key_update_last rest ev

(** A trace whose extension by one event has no key-update also has no key-update
    on its prefix (backward monotonicity of the no-rekeying predicate). **)
let rec lemma_no_key_update_prefix (l:list CS.conn_event) (ev:CS.conn_event)
  : Lemma
      (requires SMC.conn_events_no_key_update (FStar.List.Tot.append l [ev]) == true)
      (ensures SMC.conn_events_no_key_update l == true)
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
                SMC.connection_state_no_key_update_trace st1)
      (ensures SMC.connection_state_no_key_update_trace st0)
  = eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1
    returns SMC.connection_state_no_key_update_trace st0
    with _pf.
      (lemma_no_key_update_prefix st0.CS.cs_event_log d.CS.delta_event)

(** Backward no-rekeying across an official client step. **)
let lemma_client_step_no_ku_backward
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 e st1 out /\
                SMC.connection_state_no_key_update_trace st1)
      (ensures SMC.connection_state_no_key_update_trace st0)
  = assert (exists (d:CS.connection_delta). CS.legal_connection_delta st0 d st1);
    lemma_delta_no_key_update_backward st0 st1

(** Backward no-rekeying across an official server step. **)
let lemma_server_step_no_ku_backward
  (st0 st1:CS.connection_state)
  (e:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 e st1 out /\
                SMC.connection_state_no_key_update_trace st1)
      (ensures SMC.connection_state_no_key_update_trace st0)
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
        SMC.connection_state_no_key_update_trace st1 /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step a e c' out /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step a e s' out /\
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

(** SERVER: the routes into application data.  Under Model-Fix-1 the honest route
    is the ATOMIC wire receive of the client Finished at `HsServerFinishedSent`
    (a `ConnNetworkEvent` with `Received` direction).  The old LOCAL verify at
    `HsClientFinishedReceived` (with the application record keys already installed,
    a `ConnLocalEvent`) remains legal but is off the honest path.  Hence the
    pre-state / event-kind is exactly one of these two. **)
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

(** SERVER: a Received event that enters application data comes from
    `HsServerFinishedSent` (the atomic recv-Finished). **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_server_recv_into_appdata_shape
  (m:CS.connection_model) (msg:M.tls_message) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m (SMKM.received_tls_event msg) /\
        CS.step_model m (SMKM.received_tls_event msg) == Some m' /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ~(m.CS.model_control == CS.ControlApplicationData) /\
        m'.CS.model_control == CS.ControlApplicationData)
      (ensures m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
  = ()
#pop-options

(** SERVER step-level: a wire RECEIVE that enters application data was either
    already at application data, or at `HsServerFinishedSent` (the atomic
    recv-Finished verify instant). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_wire_recv_into_appdata_shape
  (st0:CS.connection_state) (wire:CW.wire_message)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step #CTy.server_local_event st0 (SM.WireEvent wire) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
        st0.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedSent)
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
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev
           (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns st0.CS.cs_model.CS.model_control == CS.ControlApplicationData \/
              st0.CS.cs_model.CS.model_control
                == CS.ControlHandshaking CS.HsServerFinishedSent
      with _.
        lemma_server_recv_into_appdata_shape st0.CS.cs_model msg st1.CS.cs_model
#pop-options

(** SERVER step-level: a SEND (nonempty wire output) never enters application data. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_send_not_into_appdata
  (st0:CS.connection_state) (local:CTy.server_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  (w:CW.wire_message)
  : Lemma
      (requires
        ES.server_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        out.SM.so_wire_outputs == [w] /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
  = if st0.CS.cs_model.CS.model_control = CS.ControlApplicationData then ()
    else begin
      let api = CTy.server_local_event_api local in
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (CTy.server_api_event_matches api conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         CS.legal_connection_delta st0
           { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
             CS.delta_raw_received = B.empty; } st1 /\
         SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
         SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
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

(** A server LOCAL event never matches a Received network conn-event: every arm of
    `server_local_event_matches` yields either a `ConnLocalEvent` or a `Sent`
    network event. **)
#push-options "--fuel 2 --ifuel 8 --z3rlimit 40"
let lemma_server_local_event_not_received
  (local:CTy.server_local_event) (conn_ev:CS.conn_event)
  : Lemma
      (requires CTy.server_api_event_matches (CTy.server_local_event_api local) conn_ev)
      (ensures
        ~(CS.ConnNetworkEvent? conn_ev /\
          (CS.ConnNetworkEvent?._0 conn_ev).CL.message_direction == CL.Received))
  = ()
#pop-options

(** SERVER step-level: the shape of a no-output LOCAL step that enters application
    data — pre-control `HsClientFinishedReceived` with the record keys installed. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_server_local_into_appdata_shape
  (st0:CS.connection_state) (local:CTy.server_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 (SM.LocalEvent local) st1 out /\
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
      (CTy.server_api_event_matches api conn_ev /\
       ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns
      (st0.CS.cs_model.CS.model_control
         == CS.ControlHandshaking CS.HsClientFinishedReceived /\
       CS.application_record_keys_installed_for_role CS.ServerEndpoint st0.CS.cs_model)
    with _.
     (
       lemma_server_local_event_not_received local conn_ev;
       lemma_server_into_appdata_is_verify st0.CS.cs_model conn_ev st1.CS.cs_model
     )
#pop-options

(** CLIENT step-level: the shape of a SEND ([w]) that enters application data —
    the pre-control is `HsServerFinishedVerified`. **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 60 --split_queries always"
let lemma_client_into_appdata_shape
  (st0:CS.connection_state) (local:CTy.client_local_event)
  (st1:CS.connection_state) (out:SM.step_output CW.wire_message EAPI.local_output)
  (w:CW.wire_message)
  : Lemma
      (requires
        EC.client_step st0 (SM.LocalEvent local) st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        out.SM.so_wire_outputs == [w] /\
        ~(st0.CS.cs_model.CS.model_control == CS.ControlApplicationData) /\
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st0.CS.cs_model.CS.model_control
          == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = let api = CTy.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      (CTy.client_api_event_matches st0 api conn_ev /\
       EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
       EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
       CS.legal_connection_delta st0
         { CS.delta_event = conn_ev; CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = B.empty; } st1 /\
       SMCan.sent_event_nonempty_seal_projection st0.CS.cs_model conn_ev raw_sent /\
       SMCan.received_event_nonempty_decode_projection st0.CS.cs_model conn_ev B.empty)
    returns
      st0.CS.cs_model.CS.model_control
        == CS.ControlHandshaking CS.HsServerFinishedVerified
    with _.
      lemma_client_into_appdata_is_send_finished
        st0.CS.cs_model conn_ev st1.CS.cs_model
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
        SMC.connection_state_no_key_update_trace st1 /\
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
        MP.Quiet? s.channel /\
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
  (* ── unfold the System predicates on `s` to the System-free, cs-level facts
       the (Option-C re-based) bridges require on `s.client` / `s.server` ── *)
  assert (WStep.client_reachable (CS.initial s.client.CS.cs_model.CS.model_config) s.client);
  assert (WStep.server_reachable (CS.initial s.server.CS.cs_model.CS.model_config) s.server);
  (* byte pairing at TlsQuiet collapses to the two raw-log equalities *)
  assert (Seq.equal s.client.CS.cs_wire_log.CL.raw_sent
                   s.server.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal s.server.CS.cs_wire_log.CL.raw_sent
                   s.client.CS.cs_wire_log.CL.raw_received);
  assert (TLS13.ConnectionState.ProtectedWireServerFlightInversion.server_flight_bridge_inputs
           s.client s.server);
  assert (TLS13.ConnectionState.ProtectedWireClientFinishedInversion.client_finished_bridge_inputs
           s.client s.server);
  (* ── the two field-pinned bridge conclusions (4 server pairs + client CF) ── *)
  TLS13.ConnectionState.ProtectedWireServerFlightInversion.lemma_server_flight_pairs_from_replays_and_pairing
    s.client s.server;
  TLS13.ConnectionState.ProtectedWireClientFinishedInversion.lemma_client_finished_pair_from_replays_and_pairing
    s.client s.server;
  let client_hs = s.client.CS.cs_model.CS.model_handshake in
  let server_hs = s.server.CS.cs_model.CS.model_handshake in
  (* both conclusions are `False` in their None arms, so all ten fields are Some *)
  assert (Some? client_hs.CS.hs_encrypted_extensions /\ Some? server_hs.CS.hs_encrypted_extensions /\
         Some? client_hs.CS.hs_certificate           /\ Some? server_hs.CS.hs_certificate /\
         Some? client_hs.CS.hs_certificate_verify    /\ Some? server_hs.CS.hs_certificate_verify /\
         Some? client_hs.CS.hs_server_finished       /\ Some? server_hs.CS.hs_server_finished /\
         Some? client_hs.CS.hs_client_finished       /\ Some? server_hs.CS.hs_client_finished);
  (* ── bind the ten front-door messages to the ACTUAL model fields ──
       server-flight pairs project sent=SERVER field / received=CLIENT field;
       the client Finished reverses (sent=CLIENT field / received=SERVER field). *)
  let sent_msg0     = M.EncryptedExtensions (Some?.v server_hs.CS.hs_encrypted_extensions) in
  let received_msg0 = M.EncryptedExtensions (Some?.v client_hs.CS.hs_encrypted_extensions) in
  let sent_msg1     = M.Certificate (Some?.v server_hs.CS.hs_certificate) in
  let received_msg1 = M.Certificate (Some?.v client_hs.CS.hs_certificate) in
  let sent_msg2     = M.CertificateVerify (Some?.v server_hs.CS.hs_certificate_verify) in
  let received_msg2 = M.CertificateVerify (Some?.v client_hs.CS.hs_certificate_verify) in
  let sent_msg3     = M.Finished (Some?.v server_hs.CS.hs_server_finished) in
  let received_msg3 = M.Finished (Some?.v client_hs.CS.hs_server_finished) in
  let sent_msg4     = M.Finished (Some?.v client_hs.CS.hs_client_finished) in
  let received_msg4 = M.Finished (Some?.v server_hs.CS.hs_client_finished) in
  (* ── the front door: from the two staged pair-output blocks to the flagship
       witness bundle (its `ensures` is definitionally
       `P.paired_protected_handshake_event_projection_pair_witnesses`) ── *)
  TLS13.ConnectionState.ProtectedWireProjection.lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_pair_outputs
    s.client s.server
    sent_msg0 received_msg0
    sent_msg1 received_msg1
    sent_msg2 received_msg2
    sent_msg3 received_msg3
    sent_msg4 received_msg4;
  assert (P.paired_protected_handshake_event_projection_pair_witnesses s.client s.server)
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        EC.client_step a.client e c' out /\
        SMC.connection_state_no_key_update_trace c' /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        ES.server_step a.server e s' out /\
        SMC.connection_state_no_key_update_trace s' /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        EC.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [] /\
        SMC.connection_state_no_key_update_trace c' /\
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
        SMC.connection_state_no_key_update_trace c' /\
        b == { a with client = c'; channel = MP.Quiet })
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        ES.server_step a.server (SM.LocalEvent local) s' out /\
        out.SM.so_wire_outputs == [w] /\
        SMC.connection_state_no_key_update_trace s' /\
        b == { a with server = s'; channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent })
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

(** deliver TO SERVER — either the server was already at application data (ROUTE A
    transport), or this WIRE recv-Finished is the ATOMIC verify that NEWLY creates
    the both-ready boundary (ROUTE B ESTABLISHMENT).  In ROUTE B the client is
    unchanged (and already ready) and the server has just entered application data,
    so `lemma_pw_establish` — which is COUNTING-FREE, going through the field-pinned
    protected-wire inversion bridges — supplies the witnesses directly from the
    byte-level reachability/pairing facts. **)
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

#push-options "--fuel 2 --ifuel 3 --z3rlimit 80 --split_queries always"
let lemma_pw_pres_deliver_to_server
  (a b:tls_system_state)
  (wire:CW.wire_message) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  (raw:B.bytes) (snap:CS.connection_model) (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        a.channel == tls_to_server raw snap sent /\
        Seq.equal (CW.wire_serialize wire) raw /\
        ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
        server_stage_ok s' /\
        SMC.connection_state_no_key_update_trace s' /\
        b == { a with server = s'; channel = MP.Quiet })
      (ensures protected_witnesses_ok b)
  = reveal_opaque (`%protected_witnesses_ok) (protected_witnesses_ok b);
    introduce (client_ready b /\ server_ready b) ==>
      P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
    with _br.
    (
      lemma_server_wire_recv_into_appdata_shape a.server wire s' out;
      if a.server.CS.cs_model.CS.model_control = CS.ControlApplicationData
      then lemma_pw_pres_server_appdata_route_a a b (SM.WireEvent wire) s' out
      else begin
        // ROUTE B — the atomic WIRE recv-Finished verify: a.server at HsServerFinishedSent.
        // ── b-structural byte facts. ──
        lemma_bp_deliver_to_server a wire s' out raw snap sent;
        lemma_deliver_to_server_intro a b wire s' out raw snap sent;
        lemma_wire_facts_deliver_to_server a b;
        // client unchanged: readiness / reachability transfer from a.
        assert (client_ready a);
        assert (client_byte_reachable b);
        // ── server reachability / config (via the underlying legal delta). ──
        assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s');
        eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s'
        returns
          P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
        with _pd.
        (
          CSL.lemma_step_model_preserves_config
            a.server.CS.cs_model d.CS.delta_event s'.CS.cs_model;
          lemma_server_reach_pres a s' (SM.WireEvent wire) out;
          // ── four hellos Some on both sides. ──
          assert (b.server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          lemma_server_appdata_hellos_some b.server;
          assert (b.client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          lemma_client_appdata_hellos_some b.client;
          lemma_pw_establish b
        )
      end
    )
#pop-options

(** server LOCAL — either the server was already ready (ROUTE A) or this is the
    verify step that NEWLY creates the both-ready boundary (ROUTE B ESTABLISHMENT).
    At the verify the server has just entered application data and the client is
    unchanged (and already ready), so the both-ready boundary holds at `b` and the
    counting-free `lemma_pw_establish` supplies the witnesses. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 30 --split_queries always"
let lemma_pw_pres_server_local
  (a b:tls_system_state)
  (local:CTy.server_local_event) (s':CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        tls_system_inv a /\
        MP.Quiet? a.channel /\
        ES.server_step a.server (SM.LocalEvent local) s' out /\
        server_stage_ok s' /\
        out.SM.so_wire_outputs == [] /\
        SMC.connection_state_no_key_update_trace s' /\
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
        lemma_server_local_intro a b local s' out;
        lemma_wire_facts_server_local a b;
        // client unchanged: readiness transfers from a.
        assert (client_ready a);
        // ── server reachability / config (via the underlying legal delta). ──
        assert (exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s');
        eliminate exists (d:CS.connection_delta). CS.legal_connection_delta a.server d s'
        returns
          P.paired_protected_handshake_event_projection_pair_witnesses b.client b.server
        with _pd.
        (
          CSL.lemma_step_model_preserves_config
            a.server.CS.cs_model d.CS.delta_event s'.CS.cs_model;
          lemma_server_reach_pres a s' (SM.LocalEvent local) out;
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
  (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
  (sent:M.tls_message)
  : Lemma
      (requires
        tls_system_inv a /\
        MP.Quiet? a.channel /\
        EC.client_step a.client (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [w] /\
        SMC.connection_state_no_key_update_trace c' /\
        b == { a with client = c'; channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent })
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 e st1 out /\ client_stage_ok st0)
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step st0 e st1 out /\
        SMR.connection_state_consistent st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures server_stage_ok st1)
  = lemma_server_step_pres st0 st1 e out;
    WStep.lemma_connection_state_consistent_server_stage_shape st1
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ MP.Quiet? a.channel /\ tls_step_client_send a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = lemma_client_send_shape a b;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == a.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with client = c'; channel = tls_to_server (emitted_raw out) a.client.CS.cs_model sent }
    returns tls_system_inv b
    with _pf.
      (assert (SMC.connection_state_no_key_update_trace c');
       lemma_client_step_preserves_stage_ok a.client c' (SM.LocalEvent local) out;
       lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_client_step_ksp a.client c' (SM.LocalEvent local) out;
       lemma_client_step_e2e a.client c' (SM.LocalEvent local) out;
       lemma_bp_client_send a local c' out w sent;
       lemma_wire_facts_client_send a b;
       lemma_client_step_preserves_pending a.client c' (SM.LocalEvent local) out;
       lemma_pw_pres_client_send a b local c' out w sent)
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ MP.Quiet? a.channel /\ tls_step_server_send a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = lemma_server_send_shape a b;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == a.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      b == { a with server = s'; channel = tls_to_client (emitted_raw out) a.server.CS.cs_model sent }
    returns tls_system_inv b
    with _pf.
      (assert (SMC.connection_state_no_key_update_trace s');
       lemma_server_step_preserves_stage_ok a.server s' (SM.LocalEvent local) out;
       lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_server_step_ksp a.server s' (SM.LocalEvent local) out;
       lemma_server_step_e2e a.server s' (SM.LocalEvent local) out;
       lemma_bp_server_send a local s' out w sent;
       lemma_wire_facts_server_send a b;
       lemma_server_step_preserves_pending a.server s' (SM.LocalEvent local) out;
       lemma_pw_pres_server_send a b local s' out w sent)
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
            MP.Quiet? s.channel /\
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
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = lemma_deliver_to_server_shape a b;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event a.server (SM.WireEvent wire) s' out /\
      b == { a with server = s'; channel = MP.Quiet }
    returns tls_system_inv b
    with _pf.
      (assert (SMC.connection_state_no_key_update_trace s');
       lemma_server_step_preserves_stage_ok a.server s' (SM.WireEvent wire) out;
       lemma_server_step_pres a.server s' (SM.WireEvent wire) out;
       lemma_server_step_shape a.server s' (SM.WireEvent wire) out;
       lemma_server_reach_pres a s' (SM.WireEvent wire) out;
       lemma_server_step_ksp a.server s' (SM.WireEvent wire) out;
       lemma_server_step_e2e a.server s' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_server a wire s' out raw snap sent;
       lemma_wire_facts_deliver_to_server a b;
       lemma_server_step_preserves_pending a.server s' (SM.WireEvent wire) out;
       lemma_pw_pres_deliver_to_server a b wire s' out raw snap sent;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ MP.Quiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40 --split_queries always"
let lemma_pres_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = lemma_deliver_to_client_shape a b;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                    (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                    (snap:CS.connection_model) (sent:M.tls_message).
      a.channel == tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event a.client (SM.WireEvent wire) c' out /\
      b == { a with client = c'; channel = MP.Quiet }
    returns tls_system_inv b
    with _pf.
      (assert (SMC.connection_state_no_key_update_trace c');
       lemma_client_step_preserves_stage_ok a.client c' (SM.WireEvent wire) out;
       lemma_client_step_pres a.client c' (SM.WireEvent wire) out;
       lemma_client_step_shape a.client c' (SM.WireEvent wire) out;
       lemma_client_reach_pres a c' (SM.WireEvent wire) out;
       lemma_client_step_ksp a.client c' (SM.WireEvent wire) out;
       lemma_client_step_e2e a.client c' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_client a wire c' out raw snap sent;
       lemma_wire_facts_deliver_to_client a b;
       lemma_client_step_preserves_pending a.client c' (SM.WireEvent wire) out;
       lemma_pw_pres_deliver_to_client a b wire c' out;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ MP.Quiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ MP.Quiet? a.channel /\ tls_step_client_local a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with client = c' }
    returns tls_system_inv b
    with _pf.
      (assert (SMC.connection_state_no_key_update_trace c');
       lemma_client_step_preserves_stage_ok a.client c' (SM.LocalEvent local) out;
       lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_client_step_ksp a.client c' (SM.LocalEvent local) out;
       lemma_client_step_e2e a.client c' (SM.LocalEvent local) out;
       lemma_bp_client_local a local c' out;
       lemma_wire_facts_client_local a b;
       lemma_client_step_preserves_pending a.client c' (SM.LocalEvent local) out;
       lemma_pw_pres_client_local a b local c' out;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ MP.Quiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ MP.Quiet? a.channel /\ tls_step_server_local a b /\ tls_no_rekeying b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step a.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      b == { a with server = s' }
    returns tls_system_inv b
    with _pf.
      (assert (SMC.connection_state_no_key_update_trace s');
       lemma_server_step_preserves_stage_ok a.server s' (SM.LocalEvent local) out;
       lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_server_step_ksp a.server s' (SM.LocalEvent local) out;
       lemma_server_step_e2e a.server s' (SM.LocalEvent local) out;
       lemma_bp_server_local a local s' out;
       lemma_wire_facts_server_local a b;
       lemma_server_step_preserves_pending a.server s' (SM.LocalEvent local) out;
       lemma_pw_pres_server_local a b local s' out;
       // client_clean b (ready-couple): a ready client at a quiescent post-state forces
       // the server past client-Finished receipt.
       introduce (client_ready b /\ MP.Quiet? b.channel) ==> server_post_cf b
       with _rc. (assert (client_byte_reachable b); lemma_ready_couple_post_cf b))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_no_ku_backward_client_send (x y:tls_system_state)
  : Lemma (requires tls_step_client_send x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = lemma_client_send_shape x y;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step x.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == x.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      y == { x with client = c'; channel = tls_to_server (emitted_raw out) x.client.CS.cs_model sent }
    returns tls_no_rekeying x
    with _pf. lemma_client_step_no_ku_backward x.client c' (SM.LocalEvent local) out

let lemma_no_ku_backward_server_send (x y:tls_system_state)
  : Lemma (requires tls_step_server_send x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = lemma_server_send_shape x y;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step x.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == x.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      y == { x with server = s'; channel = tls_to_client (emitted_raw out) x.server.CS.cs_model sent }
    returns tls_no_rekeying x
    with _pf. lemma_server_step_no_ku_backward x.server s' (SM.LocalEvent local) out

let lemma_no_ku_backward_deliver_to_client (x y:tls_system_state)
  : Lemma (requires tls_step_deliver_to_client x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = lemma_deliver_to_client_shape x y;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      x.channel == tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event x.client (SM.WireEvent wire) c' out /\
      y == { x with client = c'; channel = MP.Quiet }
    returns tls_no_rekeying x
    with _pf. lemma_client_step_no_ku_backward x.client c' (SM.WireEvent wire) out

let lemma_no_ku_backward_deliver_to_server (x y:tls_system_state)
  : Lemma (requires tls_step_deliver_to_server x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = lemma_deliver_to_server_shape x y;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      x.channel == tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event x.server (SM.WireEvent wire) s' out /\
      y == { x with server = s'; channel = MP.Quiet }
    returns tls_no_rekeying x
    with _pf. lemma_server_step_no_ku_backward x.server s' (SM.WireEvent wire) out

let lemma_no_ku_backward_client_local (x y:tls_system_state)
  : Lemma (requires tls_step_client_local x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step x.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      y == { x with client = c' }
    returns tls_no_rekeying x
    with _pf. lemma_client_step_no_ku_backward x.client c' (SM.LocalEvent local) out

let lemma_no_ku_backward_server_local (x y:tls_system_state)
  : Lemma (requires tls_step_server_local x y /\ tls_no_rekeying y)
          (ensures tls_no_rekeying x)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step x.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
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
    Stream-integrity invariant layer.

    `server_config_valid_e2e s.server` (Some config + impl-side certificate-chain
    bound) is NOT derivable from spec-level reachability (the wire limit 32768 is
    looser than the impl bound 16610), so it must be *assumed at entry* and then
    *carried*.  It is deliberately kept OUT of `tls_system_inv` — adding it there
    would force the entry hypothesis onto `lemma_reachable_inv` and hence onto the
    existing `lemma_flagship_record_material_agreement`, changing that theorem's
    statement.  Instead we layer it here.  Preservation is trivial: the config is
    immutable, so its validity is a function of a quantity every step preserves.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_cfg_pres_client_send (x y:tls_system_state)
  : Lemma (requires tls_step_client_send x y)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = lemma_client_send_shape x y;
    eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      EC.client_step x.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      c'.CS.cs_event_log == x.client.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      y == { x with client = c'; channel = tls_to_server (emitted_raw out) x.client.CS.cs_model sent }
    returns y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config
    with _pf. ()

let lemma_cfg_pres_client_local (x y:tls_system_state)
  : Lemma (requires tls_step_client_local x y)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      EC.client_step x.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [] /\
      y == { x with client = c' }
    returns y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config
    with _pf. ()

let lemma_cfg_pres_deliver_to_client (x y:tls_system_state)
  : Lemma (requires tls_step_deliver_to_client x y)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = lemma_deliver_to_client_shape x y;
    eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      x.channel == tls_to_client raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      EC.client_step #CTy.client_local_event x.client (SM.WireEvent wire) c' out /\
      y == { x with client = c'; channel = MP.Quiet }
    returns y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config
    with _pf. ()

let lemma_cfg_pres_server_send (x y:tls_system_state)
  : Lemma (requires
            tls_step_server_send x y /\
            x.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = lemma_server_send_shape x y;
    eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (w:CW.wire_message)
                     (sent:M.tls_message).
      ES.server_step x.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [w] /\
      s'.CS.cs_event_log == x.server.CS.cs_event_log @ [SMKM.sent_tls_event sent] /\
      y == { x with server = s'; channel = tls_to_client (emitted_raw out) x.server.CS.cs_model sent }
    returns y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config
    with _pf. WStep.lemma_server_step_model_facts x.server (SM.LocalEvent local) s' out

let lemma_cfg_pres_server_local (x y:tls_system_state)
  : Lemma (requires
            tls_step_server_local x y /\
            x.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = eliminate exists (local:CTy.server_local_event) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output).
      ES.server_step x.server (SM.LocalEvent local) s' out /\
      out.SM.so_wire_outputs == [] /\
      y == { x with server = s' }
    returns y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config
    with _pf. WStep.lemma_server_step_model_facts x.server (SM.LocalEvent local) s' out

let lemma_cfg_pres_deliver_to_server (x y:tls_system_state)
  : Lemma (requires
            tls_step_deliver_to_server x y /\
            x.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = lemma_deliver_to_server_shape x y;
    eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message EAPI.local_output) (raw:B.bytes)
                     (snap:CS.connection_model) (sent:M.tls_message).
      x.channel == tls_to_server raw snap sent /\
      Seq.equal (CW.wire_serialize wire) raw /\
      ES.server_step #CTy.server_local_event x.server (SM.WireEvent wire) s' out /\
      y == { x with server = s'; channel = MP.Quiet }
    returns y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config
    with _pf. WStep.lemma_server_step_model_facts x.server (SM.WireEvent wire) s' out

(** Config immutability at the system level: any single step preserves the
    server endpoint's (immutable) config, hence its validity. **)
let lemma_sys_step_preserves_server_config (x y:tls_system_state)
  : Lemma (requires
            tls_sys_step x y /\
            x.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
          (ensures
            y.server.CS.cs_model.CS.model_config == x.server.CS.cs_model.CS.model_config)
  = FStar.Classical.move_requires_2 lemma_cfg_pres_client_send x y;
    FStar.Classical.move_requires_2 lemma_cfg_pres_server_send x y;
    FStar.Classical.move_requires_2 lemma_cfg_pres_deliver_to_client x y;
    FStar.Classical.move_requires_2 lemma_cfg_pres_deliver_to_server x y;
    FStar.Classical.move_requires_2 lemma_cfg_pres_client_local x y;
    FStar.Classical.move_requires_2 lemma_cfg_pres_server_local x y
#pop-options

(** The stream-integrity invariant: structural invariant + server config
    validity. **)
let tls_stream_inv (s:tls_system_state) : prop =
  tls_system_inv s /\ server_config_valid_e2e s.server

(** Combined form used for the RTC induction (mirrors `combined_inv`): the
    no-rekeying-gated structural invariant, the (unconditional) config validity,
    and the (unconditional, immutable) server role.  The role is carried
    explicitly because the structural invariant — the usual source of
    `config_role == ServerEndpoint` — is only available under `tls_no_rekeying`,
    whereas config preservation must fire on every step. **)
let stream_combined_inv (s:tls_system_state) : prop =
  combined_inv s /\
  server_config_valid_e2e s.server /\
  s.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_stream_combined_inv_preserved (x y:tls_system_state)
  : Lemma (requires stream_combined_inv x /\ tls_sys_step x y)
          (ensures stream_combined_inv y)
  = lemma_combined_inv_preserved x y;
    // config_role is carried explicitly in `stream_combined_inv x`, so it is
    // available even when `x` has rekeyed; config immutability then transports
    // both the role and the validity forward.
    assert (x.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    lemma_sys_step_preserves_server_config x y
#pop-options

let lemma_initial_stream_combined_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        cfg_s.CS.config_role == CS.ServerEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c /\
        server_config_valid_e2e (CS.initial cfg_s))
      (ensures stream_combined_inv (initial_tls_system cfg_c cfg_s))
  = lemma_initial_combined_inv cfg_c cfg_s

(** Reachable, non-rekeyed states with a valid server config satisfy the
    stream-integrity invariant.  Mirror of `lemma_reachable_inv` with the extra
    entry hypothesis `server_config_valid_e2e (CS.initial cfg_s)`. **)
val lemma_reachable_stream_inv (cfg_c cfg_s:CS.connection_config) (s:tls_system_state)
  : Lemma (requires cfg_c.CS.config_role == CS.ClientEndpoint /\
                    cfg_s.CS.config_role == CS.ServerEndpoint /\
                    WFL.supported_client_config_wire_profile cfg_c /\
                    server_config_valid_e2e (CS.initial cfg_s) /\
                    tls_no_rekeying s /\
                    RTC.closure tls_sys_step (initial_tls_system cfg_c cfg_s) s)
          (ensures tls_stream_inv s)
let lemma_reachable_stream_inv cfg_c cfg_s s =
  lemma_initial_stream_combined_inv cfg_c cfg_s;
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 lemma_stream_combined_inv_preserved);
  RTC.stable_on_closure tls_sys_step stream_combined_inv ()

(** ─────────────────────────────────────────────────────────────────────────
    The payoff at a completed state.

    NOTE: this lemma does NOT require `tls_quiescent`.  It once did, back when
    the witnesses were produced on demand from a byte trace (the retired clean16
    route), which needed a `Quiet` channel in order to use `byte_pairing`.  Since
    the witnesses became an invariant conjunct (`protected_witnesses_ok`, gated
    on readiness alone) the quiescence hypothesis has been dead weight.

    Dropping it is not cosmetic: it makes record-material agreement available at
    NON-quiescent states, i.e. with a message in flight.  That is exactly what is
    needed to prove decode-faithfulness at an application-data DELIVERY, since
    both `step_tls_message` arms for `M.TlsApplicationData` pin
    `model_control == ControlApplicationData` -- so at a delivery step the
    receiver, not just the sender, is application-ready.
    ───────────────────────────────────────────────────────────────────────── **)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
val lemma_ready_quiescent_agrees (s:tls_system_state)
  : Lemma (requires tls_system_inv s /\ tls_application_ready s)
          (ensures SMKM.supported_profile_application_record_material_agrees s.client s.server)
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
    returns SMKM.supported_profile_application_record_material_agrees s.client s.server
    with _p1.
      eliminate exists raw2.
        CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) raw2 /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) raw2
      returns SMKM.supported_profile_application_record_material_agrees s.client s.server
      with _p2.
        P.lemma_client_server_application_record_material_agrees_from_cleartext_raw_key_shares_and_protected_event_projection_witnesses
          s.client s.server client_ch server_ch client_sh server_sh
          raw1 raw1 raw2 raw2
  | _ -> ()
#pop-options
