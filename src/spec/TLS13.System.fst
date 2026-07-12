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
  TLS13.Impl.Server.Driver.server_driver_application_ready s.server /\
  FStar.List.Tot.length s.client.CS.cs_event_log == 16 /\
  FStar.List.Tot.length s.server.CS.cs_event_log == 16

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

(** FACT 4 — protected event-projection witnesses once all five encrypted-flight
    fields are present on both sides.  (Established in STAGE B.) **)
let protected_witnesses_ok (s:tls_system_state) : prop =
  (Some? (hsf s.client).CS.hs_encrypted_extensions /\ Some? (hsf s.server).CS.hs_encrypted_extensions /\
   Some? (hsf s.client).CS.hs_certificate /\ Some? (hsf s.server).CS.hs_certificate /\
   Some? (hsf s.client).CS.hs_certificate_verify /\ Some? (hsf s.server).CS.hs_certificate_verify /\
   Some? (hsf s.client).CS.hs_server_finished /\ Some? (hsf s.server).CS.hs_server_finished /\
   Some? (hsf s.client).CS.hs_client_finished /\ Some? (hsf s.server).CS.hs_client_finished) ==>
    P.paired_protected_handshake_event_projection_pair_witnesses s.client s.server

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
  tls_no_rekeying s

(** ─────────────────────────────────────────────────────────────────────────
    The six transition shapes.  Each advances exactly one endpoint by exactly one
    step of the official canonical relation, VERBATIM (no wrapper, no pin).  Sends
    require a quiet channel and emit a single record; a LocalEvent that emits a
    record is a "send", one that emits nothing is a "local".  Deliveries consume
    the matching in-flight raw and return the channel to quiet.  Every shape
    guards the changed endpoint with `connection_state_no_key_update_trace`.
    ───────────────────────────────────────────────────────────────────────── **)

let tls_step_client_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.client_local_event) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
     CCP.client_step a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [w] /\
     CS.connection_state_no_key_update_trace c' /\
     client_stage_ok c' /\
     b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) })

let tls_step_server_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.server_local_event) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
     SCP.server_step a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [w] /\
     CS.connection_state_no_key_update_trace s' /\
     server_stage_ok s' /\
     b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) })

let tls_step_deliver_to_server (a b:tls_system_state) : prop =
  (exists (wire:CW.wire_message) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
     a.channel == TlsInFlight CS.ServerEndpoint raw /\
     Seq.equal (CW.wire_serialize wire) raw /\
     SCP.server_step a.server (SM.WireEvent wire) s' out /\
     CS.connection_state_no_key_update_trace s' /\
     server_stage_ok s' /\
     b == { a with server = s'; channel = TlsQuiet })

let tls_step_deliver_to_client (a b:tls_system_state) : prop =
  (exists (wire:CW.wire_message) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
     a.channel == TlsInFlight CS.ClientEndpoint raw /\
     Seq.equal (CW.wire_serialize wire) raw /\
     CCP.client_step a.client (SM.WireEvent wire) c' out /\
     CS.connection_state_no_key_update_trace c' /\
     client_stage_ok c' /\
     b == { a with client = c'; channel = TlsQuiet })

let tls_step_client_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.client_local_event) (c':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output).
     CCP.client_step a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [] /\
     CS.connection_state_no_key_update_trace c' /\
     client_stage_ok c' /\
     b == { a with client = c' })

let tls_step_server_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (local:CTy.server_local_event) (s':CS.connection_state)
          (out:SM.step_output CW.wire_message CTy.local_output).
     SCP.server_step a.server (SM.LocalEvent local) s' out /\
     out.SM.so_wire_outputs == [] /\
     CS.connection_state_no_key_update_trace s' /\
     server_stage_ok s' /\
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
    WStep.lemma_server_reachable_initial cfg_s

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
    client_stage_ok c' /\
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
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
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
    server_stage_ok s' /\
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
    server_stage_ok s' /\
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
#push-options "--fuel 1 --ifuel 4 --z3rlimit 60"
let lemma_wire_facts_deliver_to_client a b =
  eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                   (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
    a.channel == TlsInFlight CS.ClientEndpoint raw /\
    Seq.equal (CW.wire_serialize wire) raw /\
    CCP.client_step a.client (SM.WireEvent wire) c' out /\
    CS.connection_state_no_key_update_trace c' /\
    client_stage_ok c' /\
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
    client_stage_ok c' /\
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
    server_stage_ok s' /\
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

(** The six preservation lemmas.  Each proves the STRUCTURAL half of the
    invariant fully (both stage predicates, consistency of both endpoints via the
    official step-preservation lemmas, the client-config profile, and
    no-rekeying, all from the shape guards + `inv a`), and pulls the wire FACTS
    from the named helpers above (with channel_consistent discharged inline in the
    LOCAL/DELIVER cases, where the post-state channel is quiet). **)
#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (local:CTy.client_local_event) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (w:CW.wire_message).
      CCP.client_step a.client (SM.LocalEvent local) c' out /\
      out.SM.so_wire_outputs == [w] /\
      CS.connection_state_no_key_update_trace c' /\
      client_stage_ok c' /\
      b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint (emitted_raw out) }
    returns tls_system_inv b
    with _pf.
      (lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_bp_client_send a local c' out w;
       lemma_wire_facts_client_send a b)
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
      server_stage_ok s' /\
      b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint (emitted_raw out) }
    returns tls_system_inv b
    with _pf.
      (lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_bp_server_send a local s' out w;
       lemma_wire_facts_server_send a b)
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b)
          (ensures tls_system_inv b)
  = eliminate exists (wire:CW.wire_message) (s':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
      a.channel == TlsInFlight CS.ServerEndpoint raw /\
      Seq.equal (CW.wire_serialize wire) raw /\
      SCP.server_step a.server (SM.WireEvent wire) s' out /\
      CS.connection_state_no_key_update_trace s' /\
      server_stage_ok s' /\
      b == { a with server = s'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_server_step_pres a.server s' (SM.WireEvent wire) out;
       lemma_server_step_shape a.server s' (SM.WireEvent wire) out;
       lemma_server_reach_pres a s' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_server a wire s' out raw;
       lemma_wire_facts_deliver_to_server a b)
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 40"
let lemma_pres_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b)
          (ensures tls_system_inv b)
  = eliminate exists (wire:CW.wire_message) (c':CS.connection_state)
                     (out:SM.step_output CW.wire_message CTy.local_output) (raw:B.bytes).
      a.channel == TlsInFlight CS.ClientEndpoint raw /\
      Seq.equal (CW.wire_serialize wire) raw /\
      CCP.client_step a.client (SM.WireEvent wire) c' out /\
      CS.connection_state_no_key_update_trace c' /\
      client_stage_ok c' /\
      b == { a with client = c'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_client_step_pres a.client c' (SM.WireEvent wire) out;
       lemma_client_step_shape a.client c' (SM.WireEvent wire) out;
       lemma_client_reach_pres a c' (SM.WireEvent wire) out;
       lemma_bp_deliver_to_client a wire c' out raw;
       lemma_wire_facts_deliver_to_client a b)
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
      client_stage_ok c' /\
      b == { a with client = c' }
    returns tls_system_inv b
    with _pf.
      (lemma_client_step_pres a.client c' (SM.LocalEvent local) out;
       lemma_client_step_shape a.client c' (SM.LocalEvent local) out;
       lemma_client_reach_pres a c' (SM.LocalEvent local) out;
       lemma_bp_client_local a local c' out;
       lemma_wire_facts_client_local a b)
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
      server_stage_ok s' /\
      b == { a with server = s' }
    returns tls_system_inv b
    with _pf.
      (lemma_server_step_pres a.server s' (SM.LocalEvent local) out;
       lemma_server_step_shape a.server s' (SM.LocalEvent local) out;
       lemma_server_reach_pres a s' (SM.LocalEvent local) out;
       lemma_bp_server_local a local s' out;
       lemma_wire_facts_server_local a b)
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
  // ── Establish FACT 4 on demand at the ready+quiescent boundary. ──
  // Both endpoints are reachable from their own `CS.initial cfg`, so each has a
  // byte-level `valid_byte_trace`; quiescence collapses `byte_pairing` to exact
  // `paired_wire_logs`; `tls_application_ready` supplies the length-16 boundary;
  // the invariant supplies the client-config wire profile, no-rekeying, and the
  // hello key-share agreement (FACT 3).  Together these are exactly `clean16`.
  let cfg_c = s.client.CS.cs_model.CS.model_config in
  let cfg_s = s.server.CS.cs_model.CS.model_config in
  WStep.lemma_client_valid_byte_trace_of_reachable cfg_c s.client;
  WStep.lemma_server_valid_byte_trace_of_reachable cfg_s s.server;
  assert (PNT.paired_no_tail_application_ready_boundary16 s.client s.server);
  SBD.lemma_paired_protected_witnesses_from_clean16_valid_byte_traces_and_hello_key_shares
    (CS.initial cfg_c) (CS.initial cfg_s) s.client s.server
    s.client.CS.cs_wire_log.CL.raw_received
    s.client.CS.cs_wire_log.CL.raw_sent
    s.server.CS.cs_wire_log.CL.raw_received
    s.server.CS.cs_wire_log.CL.raw_sent;
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
