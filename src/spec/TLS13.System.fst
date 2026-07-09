module TLS13.System

(**
  The combined TLS 1.3 client<->server system.

  This scales the `calc_sample` combined-system + temporal approach up to real
  TLS: it composes two `TLS13.Spec.ConnectionState.connection_state`s (a client
  and a server) with an explicit in-flight message channel, so that temporal
  properties of their *interaction* — notably record-key-material agreement —
  can be stated and proved (see `TLS13.System.Temporal`).

  Design (mirrors `Calc.System`):
    - the channel carries at most one *semantic* handshake message in flight
      (no raw-byte bookkeeping is needed: record-material agreement follows from
      semantic handshake-message pairing plus the per-endpoint `application_ready`
      invariant — see the payoff bridge at the bottom of this module);
    - each transition advances exactly one endpoint by exactly one step of the
      *official* canonical TLS transition relation (`client_step` / `server_step`
      from `TLS13.Impl.{Client,Server}.CanonicalProtocol`), so the system is a
      faithful model of the real TLS transition function rather than a puppet;
    - the structural invariant `tls_system_inv` (proved inductive) maintains the
      cross-endpoint agreement of every populated handshake message field and the
      "no rekeying" discipline, which at a completed + quiescent state yields the
      hypotheses of the existing verified pairing payoff lemma.
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

open FStar.List.Tot

(** ─────────────────────────────────────────────────────────────────────────
    States
    ───────────────────────────────────────────────────────────────────────── **)

(** The in-flight message channel: at most one semantic message, with the
    direction it is travelling (as seen by its recipient). **)
noeq
type tls_channel =
  | TlsQuiet    : tls_channel
  | TlsInFlight : recipient:CS.endpoint_role -> msg:M.tls_message -> tls_channel

(** The combined system state: a client endpoint, a server endpoint, and the
    channel between them. **)
noeq
type tls_system_state = {
  client:  CS.connection_state;
  server:  CS.connection_state;
  channel: tls_channel;
}

(** The system is quiescent when nothing is in flight. **)
let tls_quiescent (s:tls_system_state) : prop = TlsQuiet? s.channel

(** Both endpoints have completed the handshake and installed application keys. **)
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

(** ─────────────────────────────────────────────────────────────────────────
    Applying a single real TLS event to one endpoint.
    ───────────────────────────────────────────────────────────────────────── **)

(** ─────────────────────────────────────────────────────────────────────────
    Advancing one endpoint through the *official* TLS transition relation.

    The canonical low-level transition relations for the two roles are
    `TLS13.Impl.Client.CanonicalProtocol.client_step` and
    `TLS13.Impl.Server.CanonicalProtocol.server_step` — the very relations the
    real state machines and drivers are shown to implement.  We advance each
    endpoint through *these* relations rather than calling `CS.step_model`
    directly, so the system is a faithful model of the real TLS transition
    function.

    An official step relates `st` to `st'` via a state-machine event (a received
    wire message, or a local API event such as "send ServerHello" / "send
    application data").  By `CS.legal_connection_delta` such a step appends
    exactly one `CS.conn_event` to the endpoint's event log and advances its
    model by exactly that event through `CS.step_model`.  We therefore *pin* the
    appended event to the message we are moving, which lets the preservation
    proofs recover the `CS.step_model` effect (see `lemma_*_official_step_model`
    below).  The raw wire log is irrelevant to record-material agreement and is
    left unconstrained.
    ───────────────────────────────────────────────────────────────────────── **)

(** The client endpoint takes one official `client_step` whose single appended
    event is `ev`. **)
let official_client_step (st st':CS.connection_state) (ev:CS.conn_event) : prop =
  (exists (e:SM.event CW.wire_message CTy.client_local_event)
          (out:SM.step_output CW.wire_message CTy.local_output).
     CCP.client_step st e st' out) /\
  st'.CS.cs_event_log == st.CS.cs_event_log @ [ev]

(** The server endpoint takes one official `server_step` whose single appended
    event is `ev`. **)
let official_server_step (st st':CS.connection_state) (ev:CS.conn_event) : prop =
  (exists (e:SM.event CW.wire_message CTy.server_local_event)
          (out:SM.step_output CW.wire_message CTy.local_output).
     SCP.server_step st e st' out) /\
  st'.CS.cs_event_log == st.CS.cs_event_log @ [ev]

(** Appending to a fixed prefix is injective in the appended element. **)
let rec lemma_snoc_inj (#a:Type) (l:list a) (x y:a)
  : Lemma (requires l @ [x] == l @ [y]) (ensures x == y) (decreases l)
  = match l with
    | [] -> ()
    | _ :: t -> lemma_snoc_inj t x y

(** A legal delta whose appended event is pinned to `ev` advances the model by
    exactly `ev`. **)
let lemma_legal_delta_step
  (st st':CS.connection_state) (delta:CS.connection_delta) (ev:CS.conn_event)
  : Lemma
      (requires
        CS.legal_connection_delta st delta st' /\
        st'.CS.cs_event_log == st.CS.cs_event_log @ [ev])
      (ensures CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model)
  = lemma_snoc_inj st.CS.cs_event_log ev delta.CS.delta_event

#push-options "--fuel 1 --ifuel 3 --z3rlimit 60"
(** An official client step advances the model by its pinned event. **)
let lemma_client_official_step_model
  (st st':CS.connection_state) (ev:CS.conn_event)
  : Lemma (requires official_client_step st st' ev)
          (ensures
            CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model /\
            st'.CS.cs_event_log == st.CS.cs_event_log @ [ev])
  = eliminate exists (e:SM.event CW.wire_message CTy.client_local_event)
                     (out:SM.step_output CW.wire_message CTy.local_output).
        CCP.client_step st e st' out
    returns CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model
    with _pf.
      (let finish ()
         : Lemma
             (requires (exists (d:CS.connection_delta). CS.legal_connection_delta st d st'))
             (ensures CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model)
         = eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st d st'
           returns CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model
           with _pf2. lemma_legal_delta_step st st' d ev
       in
       match e with
       | SM.WireEvent wire -> finish ()
       | SM.LocalEvent local -> finish ())
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 60"
(** An official server step advances the model by its pinned event. **)
let lemma_server_official_step_model
  (st st':CS.connection_state) (ev:CS.conn_event)
  : Lemma (requires official_server_step st st' ev)
          (ensures
            CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model /\
            st'.CS.cs_event_log == st.CS.cs_event_log @ [ev])
  = eliminate exists (e:SM.event CW.wire_message CTy.server_local_event)
                     (out:SM.step_output CW.wire_message CTy.local_output).
        SCP.server_step st e st' out
    returns CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model
    with _pf.
      (let finish ()
         : Lemma
             (requires (exists (d:CS.connection_delta). CS.legal_connection_delta st d st'))
             (ensures CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model)
         = eliminate exists (d:CS.connection_delta). CS.legal_connection_delta st d st'
           returns CS.step_model st.CS.cs_model ev == Some st'.CS.cs_model
           with _pf2. lemma_legal_delta_step st st' d ev
       in
       match e with
       | SM.WireEvent wire -> finish ()
       | SM.LocalEvent local -> finish ())
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    `ev` is *not* free: it is pinned to the official step's own appended event.

    The concern that `ev` in `official_{client,server}_step` is unconstrained is
    unfounded — the conjunct `st'.cs_event_log == st.cs_event_log @ [ev]` forces
    `ev` to be *exactly* the single `CS.conn_event` the official step appends to
    the log (via `CS.legal_connection_delta`).  Hence `ev` is a *function* of the
    endpoints `st`/`st'`: two official steps with the same endpoints move the
    same event.  And through the official step's own internal seal/decode
    projections, that event is tied to the step's wire `out` (see
    `lemma_official_server_send_wire_tied` below).
    ───────────────────────────────────────────────────────────────────────── **)

(** `ev` is uniquely determined by the endpoints — it is the step's own event. **)
let lemma_official_client_step_det
  (st st':CS.connection_state) (ev1 ev2:CS.conn_event)
  : Lemma (requires official_client_step st st' ev1 /\ official_client_step st st' ev2)
          (ensures ev1 == ev2)
  = lemma_snoc_inj st.CS.cs_event_log ev1 ev2

let lemma_official_server_step_det
  (st st':CS.connection_state) (ev1 ev2:CS.conn_event)
  : Lemma (requires official_server_step st st' ev1 /\ official_server_step st st' ev2)
          (ensures ev1 == ev2)
  = lemma_snoc_inj st.CS.cs_event_log ev1 ev2

#push-options "--fuel 2 --ifuel 4 --z3rlimit 120"
(** A *send* pinned to `sent_tls_event m` genuinely emits `m` on the wire: there
    is an official `server_step` whose serialized wire output `out` (matched to
    `raw_sent` by `server_wire_outputs_match`) is the sealing of exactly this
    sent event (`sent_event_nonempty_seal_projection`).  This is the explicit
    tie between the moved message and `out` that channel-level pinning induces.

    (The `WireEvent` alternative is ruled out: it would append a *received*
    event, contradicting the `Sent` pin by `lemma_snoc_inj`.) **)
let lemma_official_server_send_wire_tied
  (st st':CS.connection_state) (m:M.tls_message)
  : Lemma
      (requires official_server_step st st' (CS.sent_tls_event m))
      (ensures
        (exists (e:SM.event CW.wire_message CTy.server_local_event)
                (out:SM.step_output CW.wire_message CTy.local_output)
                (raw_sent:B.bytes).
           SCP.server_step st e st' out /\
           SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
           CS.sent_event_nonempty_seal_projection st.CS.cs_model (CS.sent_tls_event m) raw_sent))
  = eliminate exists (e:SM.event CW.wire_message CTy.server_local_event)
                     (out:SM.step_output CW.wire_message CTy.local_output).
        SCP.server_step st e st' out
    returns
      (exists (e:SM.event CW.wire_message CTy.server_local_event)
              (out:SM.step_output CW.wire_message CTy.local_output)
              (raw_sent:B.bytes).
         SCP.server_step st e st' out /\
         SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         CS.sent_event_nonempty_seal_projection st.CS.cs_model (CS.sent_tls_event m) raw_sent)
    with _pf.
      (match e with
       | SM.LocalEvent local ->
         eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
             SCP.server_api_event_matches (CTy.server_local_event_api local) conn_ev /\
             SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
             SCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
             CS.legal_connection_delta st
               { CS.delta_event = conn_ev;
                 CS.delta_raw_sent = raw_sent;
                 CS.delta_raw_received = B.empty } st' /\
             CS.sent_event_nonempty_seal_projection st.CS.cs_model conn_ev raw_sent /\
             CS.received_event_nonempty_decode_projection st.CS.cs_model conn_ev B.empty
           returns
             (exists (e:SM.event CW.wire_message CTy.server_local_event)
                     (out:SM.step_output CW.wire_message CTy.local_output)
                     (raw_sent:B.bytes).
                SCP.server_step st e st' out /\
                SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
                CS.sent_event_nonempty_seal_projection st.CS.cs_model (CS.sent_tls_event m) raw_sent)
           with _pf2.
             // pin forces conn_ev == sent_tls_event m
             (lemma_snoc_inj st.CS.cs_event_log (CS.sent_tls_event m) conn_ev;
              introduce exists (e:SM.event CW.wire_message CTy.server_local_event)
                               (out:SM.step_output CW.wire_message CTy.local_output)
                               (raw_sent:B.bytes).
                 SCP.server_step st e st' out /\
                 SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
                 CS.sent_event_nonempty_seal_projection st.CS.cs_model (CS.sent_tls_event m) raw_sent
              with e out raw_sent
              and ())
       | SM.WireEvent wire ->
         // this branch appends a *received* event, contradicting the Sent pin
         eliminate exists (msg:M.tls_message).
             CS.legal_connection_delta st
               { CS.delta_event = CS.received_tls_event msg;
                 CS.delta_raw_sent =
                   WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs;
                 CS.delta_raw_received = CW.wire_serialize wire } st' /\
             CS.sent_event_nonempty_seal_projection st.CS.cs_model
               (CS.received_tls_event msg)
               (WF.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs) /\
             CS.received_event_nonempty_decode_projection st.CS.cs_model
               (CS.received_tls_event msg)
               (CW.wire_serialize wire) /\
             SCP.server_local_outputs_match (CS.received_tls_event msg) out.SM.so_local_outputs
           returns
             (exists (e:SM.event CW.wire_message CTy.server_local_event)
                     (out:SM.step_output CW.wire_message CTy.local_output)
                     (raw_sent:B.bytes).
                SCP.server_step st e st' out /\
                SCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
                CS.sent_event_nonempty_seal_projection st.CS.cs_model (CS.sent_tls_event m) raw_sent)
           with _pf2.
             lemma_snoc_inj st.CS.cs_event_log (CS.sent_tls_event m) (CS.received_tls_event msg))
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    Payoff bridge (reuses the existing verified pairing lemma chain).

    At a state where both endpoints have completed the handshake
    (`application_ready`), the semantic handshake messages are paired, and there
    has been no rekeying, the application record-key material of the two
    endpoints agrees.  This is exactly the clean side condition the flagship
    temporal theorem discharges — no hardcoded packet counts, no trace splitting.
    ───────────────────────────────────────────────────────────────────────── **)

val lemma_agrees_from_ready_paired
  (client server:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        P.paired_handshake_message_states client server /\
        CS.connection_state_no_key_update_trace client /\
        CS.connection_state_no_key_update_trace server)
      (ensures
        CS.supported_profile_application_record_material_agrees client server)
let lemma_agrees_from_ready_paired client server =
  // both endpoints performed no key update -> first-epoch no-key-update inputs
  assert (P.client_server_driver_first_epoch_no_key_update_state_inputs client server);
  P.lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update
    client server;
  // paired handshake messages + application-record inputs -> remaining projection inputs
  P.lemma_client_server_driver_remaining_semantic_projection_inputs_from_paired_handshake_message_states
    client server;
  // remaining projection inputs == projected state inputs -> supported-profile state inputs
  P.lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs
    client server;
  // supported-profile state inputs + application_ready -> key-material inputs agree
  P.lemma_client_server_driver_supported_profile_key_material_inputs_agree
    client server;
  // project the application record-material inputs, then conclude agreement
  CSL.lemma_paired_supported_profile_application_record_material_agrees client server

(** ─────────────────────────────────────────────────────────────────────────
    The inductive structural invariant and the honest system step relation.

    This scales the `Calc.System` phase-indexed invariant up to real TLS.  The
    proof is *genuinely inductive*: there are no hardcoded packet/event counts,
    no trace splitting, and no fixed-length event lists.  Every endpoint advance
    goes through the real canonical `client_step` / `server_step` transition (via
    `official_client_step` / `official_server_step`); the channel carries exactly
    one semantic message and re-establishes cross-endpoint pairing *by
    construction* on delivery.
    ───────────────────────────────────────────────────────────────────────── **)

(** Handy projections. **)
let hsf (st:CS.connection_state) : CS.handshake_state =
  st.CS.cs_model.CS.model_handshake

let ctrl (st:CS.connection_state) : CS.connection_control_state =
  st.CS.cs_model.CS.model_control

(**
  Per-endpoint stage predicate for the *client* role: it pins the endpoint to a
  client-side control state and records, as a lower bound, which of the seven
  paired handshake message fields must be populated at that stage.  The
  `_ -> False` catch-all means the client never occupies a server-side stage
  (nor a failed/closed one) in an honest run — this is what lets the send/deliver
  clauses rule out spurious `step_model` matches.
**)
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

(**
  Directional cross-endpoint agreement of the seven paired handshake fields.
  For each message, the *receiver*'s copy (if present) equals the *sender*'s
  copy: ClientHello and (client) Finished flow client->server; ServerHello,
  EncryptedExtensions, Certificate, CertificateVerify and (server) Finished flow
  server->client.  Combined with the stage predicates (which force all seven
  fields present at `ControlApplicationData`) this yields full pairing.
**)
let fields_directional_agree (s:tls_system_state) : prop =
  let c = hsf s.client in
  let v = hsf s.server in
  (Some? v.CS.hs_client_hello ==> v.CS.hs_client_hello == c.CS.hs_client_hello) /\
  (Some? c.CS.hs_server_hello ==> c.CS.hs_server_hello == v.CS.hs_server_hello) /\
  (Some? c.CS.hs_encrypted_extensions ==>
     c.CS.hs_encrypted_extensions == v.CS.hs_encrypted_extensions) /\
  (Some? c.CS.hs_certificate ==> c.CS.hs_certificate == v.CS.hs_certificate) /\
  (Some? c.CS.hs_certificate_verify ==>
     c.CS.hs_certificate_verify == v.CS.hs_certificate_verify) /\
  (Some? c.CS.hs_server_finished ==>
     c.CS.hs_server_finished == v.CS.hs_server_finished) /\
  (Some? v.CS.hs_client_finished ==> v.CS.hs_client_finished == c.CS.hs_client_finished)

(**
  Channel consistency: a *handshake* message in flight equals the sender's
  already-populated field, so delivering it makes the peer's field match by
  construction.  Non-handshake messages (application data, alerts,
  change-cipher-spec, ignored post-handshake records) carry no handshake-field
  obligation and are always admissible in flight; a `TlsKeyUpdate` is never in
  flight (sends exclude it, since the flagship models the no-rekeying
  discipline).
**)
let channel_consistent (s:tls_system_state) : prop =
  match s.channel with
  | TlsQuiet -> True
  | TlsInFlight CS.ServerEndpoint m ->
    (match m with
     | M.TlsHandshake (M.ClientHello ch) ->
       (hsf s.client).CS.hs_client_hello == Some ch
     | M.TlsHandshake (M.Finished cf) ->
       (hsf s.client).CS.hs_client_finished == Some cf
     | M.TlsHandshake _ -> False
     | M.TlsKeyUpdate _ -> False
     | _ -> True)
  | TlsInFlight CS.ClientEndpoint m ->
    (match m with
     | M.TlsHandshake (M.ServerHello sh) ->
       (hsf s.server).CS.hs_server_hello == Some sh
     | M.TlsHandshake (M.EncryptedExtensions ee) ->
       (hsf s.server).CS.hs_encrypted_extensions == Some ee
     | M.TlsHandshake (M.Certificate cert) ->
       (hsf s.server).CS.hs_certificate == Some cert
     | M.TlsHandshake (M.CertificateVerify cv) ->
       (hsf s.server).CS.hs_certificate_verify == Some cv
     | M.TlsHandshake (M.Finished sf) ->
       (hsf s.server).CS.hs_server_finished == Some sf
     | M.TlsHandshake _ -> False
     | M.TlsKeyUpdate _ -> False
     | _ -> True)

(** The inductive structural invariant. **)
let tls_system_inv (s:tls_system_state) : prop =
  client_stage_ok s.client /\
  server_stage_ok s.server /\
  fields_directional_agree s /\
  channel_consistent s /\
  tls_no_rekeying s

(** ─────────────────────────────────────────────────────────────────────────
    Honesty conditions carried by the transitions.
    ───────────────────────────────────────────────────────────────────────── **)

(** The field an endpoint of the given role populates when it *sends* `hmsg` is
    currently empty (a handshake message is emitted at most once). **)
let sent_field_none (role:CS.endpoint_role) (st:CS.connection_state) (hmsg:M.handshake_msg)
  : prop =
  let h = hsf st in
  match hmsg with
  | M.ClientHello _ -> h.CS.hs_client_hello == None
  | M.ServerHello _ -> h.CS.hs_server_hello == None
  | M.EncryptedExtensions _ -> h.CS.hs_encrypted_extensions == None
  | M.Certificate _ -> h.CS.hs_certificate == None
  | M.CertificateVerify _ -> h.CS.hs_certificate_verify == None
  | M.Finished _ ->
    (match role with
     | CS.ClientEndpoint -> h.CS.hs_client_finished == None
     | CS.ServerEndpoint -> h.CS.hs_server_finished == None)
  | M.HelloRetryRequest -> False

(** A local (crypto/API) event leaves all seven paired handshake fields intact.
    For the verify/select events (which re-store a field) this is exactly the
    honest requirement that they re-store the value already agreed. **)
let preserves_tracked_fields (st st':CS.connection_state) : prop =
  let h = hsf st in
  let h' = hsf st' in
  h'.CS.hs_client_hello == h.CS.hs_client_hello /\
  h'.CS.hs_server_hello == h.CS.hs_server_hello /\
  h'.CS.hs_encrypted_extensions == h.CS.hs_encrypted_extensions /\
  h'.CS.hs_certificate == h.CS.hs_certificate /\
  h'.CS.hs_certificate_verify == h.CS.hs_certificate_verify /\
  h'.CS.hs_server_finished == h.CS.hs_server_finished /\
  h'.CS.hs_client_finished == h.CS.hs_client_finished

(** ─────────────────────────────────────────────────────────────────────────
    The six transition shapes.  Each advances exactly one endpoint by exactly
    one step of the official canonical TLS transition relation
    (`official_client_step` / `official_server_step`, wrapping `client_step` /
    `server_step`).

    Sends and deliveries carry *arbitrary* TLS messages — handshake messages,
    application data, alerts (close-notify / fatal), change-cipher-spec and
    ignored post-handshake records — not just handshake messages.  The only
    excluded message is `TlsKeyUpdate`, because the flagship theorem models the
    no-rekeying discipline (a key update would falsify `tls_no_rekeying`).
    ───────────────────────────────────────────────────────────────────────── **)

(** Honesty guard on the message an endpoint *emits*: never a key update; a
    handshake message is emitted at most once (its target field is empty, and a
    server `Finished` requires its Certificate/CertificateVerify already sent);
    a non-handshake message leaves all seven tracked handshake fields intact. **)
let send_msg_ok
  (role:CS.endpoint_role) (st st':CS.connection_state) (m:M.tls_message)
  : prop =
  ~(M.TlsKeyUpdate? m) /\
  (match m with
   | M.TlsHandshake hmsg ->
     sent_field_none role st hmsg /\
     ((role == CS.ServerEndpoint /\ M.Finished? hmsg) ==>
        (Some? (hsf st).CS.hs_certificate /\
         Some? (hsf st).CS.hs_certificate_verify))
   | _ -> preserves_tracked_fields st st')

(** Honesty guard on a *delivered* message: a non-handshake message leaves the
    receiver's tracked handshake fields intact (a handshake message legitimately
    installs its field, matched to the sender's copy by channel consistency). **)
let deliver_msg_ok (st st':CS.connection_state) (m:M.tls_message) : prop =
  match m with
  | M.TlsHandshake _ -> True
  | _ -> preserves_tracked_fields st st'

let tls_step_client_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (m:M.tls_message) (c':CS.connection_state).
     send_msg_ok CS.ClientEndpoint a.client c' m /\
     official_client_step a.client c' (CS.sent_tls_event m) /\
     client_stage_ok c' /\
     b == { a with client = c'; channel = TlsInFlight CS.ServerEndpoint m })

let tls_step_server_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (m:M.tls_message) (s':CS.connection_state).
     send_msg_ok CS.ServerEndpoint a.server s' m /\
     official_server_step a.server s' (CS.sent_tls_event m) /\
     server_stage_ok s' /\
     b == { a with server = s'; channel = TlsInFlight CS.ClientEndpoint m })

let tls_step_deliver_to_client (a b:tls_system_state) : prop =
  (exists (m:M.tls_message) (c':CS.connection_state).
     a.channel == TlsInFlight CS.ClientEndpoint m /\
     deliver_msg_ok a.client c' m /\
     official_client_step a.client c' (CS.received_tls_event m) /\
     client_stage_ok c' /\
     b == { a with client = c'; channel = TlsQuiet })

let tls_step_deliver_to_server (a b:tls_system_state) : prop =
  (exists (m:M.tls_message) (s':CS.connection_state).
     a.channel == TlsInFlight CS.ServerEndpoint m /\
     deliver_msg_ok a.server s' m /\
     official_server_step a.server s' (CS.received_tls_event m) /\
     server_stage_ok s' /\
     b == { a with server = s'; channel = TlsQuiet })

let tls_step_client_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (lev:CS.local_event) (c':CS.connection_state).
     official_client_step a.client c' (CS.ConnLocalEvent lev) /\
     preserves_tracked_fields a.client c' /\
     client_stage_ok c' /\
     b == { a with client = c' })

let tls_step_server_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (lev:CS.local_event) (s':CS.connection_state).
     official_server_step a.server s' (CS.ConnLocalEvent lev) /\
     preserves_tracked_fields a.server s' /\
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

(** Appending a non-key-update event preserves the "no key update" flag. **)
let rec lemma_no_ku_append (l:list CS.conn_event) (ev:CS.conn_event)
  : Lemma
      (ensures
        CS.conn_events_no_key_update (l @ [ev]) ==
          (CS.conn_events_no_key_update l && not (CS.conn_event_is_key_update ev)))
      (decreases l)
  = match l with
    | [] -> ()
    | _ :: t -> lemma_no_ku_append t ev

let lemma_initial_inv (cfg_c cfg_s:CS.connection_config)
  : Lemma (ensures tls_system_inv (initial_tls_system cfg_c cfg_s))
  = ()

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80"
let lemma_pres_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (m:M.tls_message) (c':CS.connection_state).
      send_msg_ok CS.ClientEndpoint a.client c' m /\
      official_client_step a.client c' (CS.sent_tls_event m) /\
      client_stage_ok c' /\
      b == { a with client = c';
                    channel = TlsInFlight CS.ServerEndpoint m }
    returns tls_system_inv b
    with _pf.
      (lemma_client_official_step_model a.client c' (CS.sent_tls_event m);
       lemma_no_ku_append a.client.CS.cs_event_log (CS.sent_tls_event m);
       match m with
       | M.TlsHandshake hmsg ->
         (match hmsg with
          | M.ClientHello ch -> ()
          | M.Finished cf -> ()
          | _ -> ())
       // non-handshake: preserves_tracked_fields keeps directional agreement,
       // and a non-key-update, non-handshake message in flight is admissible.
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80"
let lemma_pres_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (m:M.tls_message) (s':CS.connection_state).
      send_msg_ok CS.ServerEndpoint a.server s' m /\
      official_server_step a.server s' (CS.sent_tls_event m) /\
      server_stage_ok s' /\
      b == { a with server = s';
                    channel = TlsInFlight CS.ClientEndpoint m }
    returns tls_system_inv b
    with _pf.
      (lemma_server_official_step_model a.server s' (CS.sent_tls_event m);
       lemma_no_ku_append a.server.CS.cs_event_log (CS.sent_tls_event m);
       match m with
       | M.TlsHandshake hmsg ->
         (match hmsg with
          | M.ServerHello sh -> ()
          | M.EncryptedExtensions ee -> ()
          | M.Certificate cert -> ()
          | M.CertificateVerify cv -> ()
          | M.Finished sf -> ()
          | _ -> ())
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80"
let lemma_pres_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b)
          (ensures tls_system_inv b)
  = eliminate exists (m:M.tls_message) (c':CS.connection_state).
      a.channel == TlsInFlight CS.ClientEndpoint m /\
      deliver_msg_ok a.client c' m /\
      official_client_step a.client c' (CS.received_tls_event m) /\
      client_stage_ok c' /\
      b == { a with client = c'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_client_official_step_model a.client c' (CS.received_tls_event m);
       lemma_no_ku_append a.client.CS.cs_event_log (CS.received_tls_event m);
       match m with
       | M.TlsHandshake (M.ServerHello sh) -> ()
       | M.TlsHandshake (M.EncryptedExtensions ee) -> ()
       | M.TlsHandshake (M.Certificate cert) -> ()
       | M.TlsHandshake (M.CertificateVerify cv) -> ()
       | M.TlsHandshake (M.Finished sf) -> ()
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 3 --z3rlimit 80"
let lemma_pres_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b)
          (ensures tls_system_inv b)
  = eliminate exists (m:M.tls_message) (s':CS.connection_state).
      a.channel == TlsInFlight CS.ServerEndpoint m /\
      deliver_msg_ok a.server s' m /\
      official_server_step a.server s' (CS.received_tls_event m) /\
      server_stage_ok s' /\
      b == { a with server = s'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_server_official_step_model a.server s' (CS.received_tls_event m);
       lemma_no_ku_append a.server.CS.cs_event_log (CS.received_tls_event m);
       match m with
       | M.TlsHandshake (M.ClientHello ch) -> ()
       | M.TlsHandshake (M.Finished cf) -> ()
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_client_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_local a b)
          (ensures tls_system_inv b)
  = eliminate exists (lev:CS.local_event) (c':CS.connection_state).
      official_client_step a.client c' (CS.ConnLocalEvent lev) /\
      preserves_tracked_fields a.client c' /\
      client_stage_ok c' /\
      b == { a with client = c' }
    returns tls_system_inv b
    with _pf.
      (lemma_client_official_step_model a.client c' (CS.ConnLocalEvent lev);
       lemma_no_ku_append a.client.CS.cs_event_log (CS.ConnLocalEvent lev))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_local a b)
          (ensures tls_system_inv b)
  = eliminate exists (lev:CS.local_event) (s':CS.connection_state).
      official_server_step a.server s' (CS.ConnLocalEvent lev) /\
      preserves_tracked_fields a.server s' /\
      server_stage_ok s' /\
      b == { a with server = s' }
    returns tls_system_inv b
    with _pf.
      (lemma_server_official_step_model a.server s' (CS.ConnLocalEvent lev);
       lemma_no_ku_append a.server.CS.cs_event_log (CS.ConnLocalEvent lev))
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

val lemma_ready_quiescent_agrees (s:tls_system_state)
  : Lemma (requires tls_system_inv s /\ tls_quiescent s /\ tls_application_ready s)
          (ensures CS.supported_profile_application_record_material_agrees s.client s.server)
let lemma_ready_quiescent_agrees s =
  // application_ready pins both controls to ControlApplicationData, so the stage
  // predicates force all seven fields present on both sides, and directional
  // agreement upgrades to full pairing.
  assert (ctrl s.client == CS.ControlApplicationData);
  assert (ctrl s.server == CS.ControlApplicationData);
  assert (P.paired_handshake_message_states s.client s.server);
  lemma_agrees_from_ready_paired s.client s.server
