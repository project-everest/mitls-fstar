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
    - each transition advances exactly one endpoint by exactly one real
      `CS.step_model` event, so the system is a faithful model of the real TLS
      transition function rather than a puppet;
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

(** Advance one endpoint by one real `CS.step_model` event, recording it in the
    endpoint's event log (so the "no key update" trace stays meaningful). The
    raw wire log is irrelevant to record-material agreement and is left as-is. **)
let ep_apply (st:CS.connection_state) (ev:CS.conn_event)
  : GTot (option CS.connection_state) =
  match CS.step_model st.CS.cs_model ev with
  | Some m' ->
    Some ({ st with
            CS.cs_model     = m';
            CS.cs_event_log = st.CS.cs_event_log @ [ev] })
  | None -> None

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
    goes through the real `CS.step_model` transition (via `ep_apply`); the
    channel carries exactly one semantic message and re-establishes cross-endpoint
    pairing *by construction* on delivery.
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
  Channel consistency: a message in flight equals the sender's already-populated
  field, so delivering it makes the peer's field match by construction.  Only
  semantic handshake messages ever travel on the channel.
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
     | _ -> False)
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
     | _ -> False)

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
    one real `CS.step_model` event through `ep_apply`.
    ───────────────────────────────────────────────────────────────────────── **)

let tls_step_client_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (hmsg:M.handshake_msg) (c':CS.connection_state).
     sent_field_none CS.ClientEndpoint a.client hmsg /\
     ep_apply a.client (CS.sent_tls_event (M.TlsHandshake hmsg)) == Some c' /\
     client_stage_ok c' /\
     b == { a with client = c';
                   channel = TlsInFlight CS.ServerEndpoint (M.TlsHandshake hmsg) })

let tls_step_server_send (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (hmsg:M.handshake_msg) (s':CS.connection_state).
     sent_field_none CS.ServerEndpoint a.server hmsg /\
     (M.Finished? hmsg ==>
        (Some? (hsf a.server).CS.hs_certificate /\
         Some? (hsf a.server).CS.hs_certificate_verify)) /\
     ep_apply a.server (CS.sent_tls_event (M.TlsHandshake hmsg)) == Some s' /\
     server_stage_ok s' /\
     b == { a with server = s';
                   channel = TlsInFlight CS.ClientEndpoint (M.TlsHandshake hmsg) })

let tls_step_deliver_to_client (a b:tls_system_state) : prop =
  (exists (m:M.tls_message) (c':CS.connection_state).
     a.channel == TlsInFlight CS.ClientEndpoint m /\
     ep_apply a.client (CS.received_tls_event m) == Some c' /\
     client_stage_ok c' /\
     b == { a with client = c'; channel = TlsQuiet })

let tls_step_deliver_to_server (a b:tls_system_state) : prop =
  (exists (m:M.tls_message) (s':CS.connection_state).
     a.channel == TlsInFlight CS.ServerEndpoint m /\
     ep_apply a.server (CS.received_tls_event m) == Some s' /\
     server_stage_ok s' /\
     b == { a with server = s'; channel = TlsQuiet })

let tls_step_client_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (lev:CS.local_event) (c':CS.connection_state).
     ep_apply a.client (CS.ConnLocalEvent lev) == Some c' /\
     preserves_tracked_fields a.client c' /\
     client_stage_ok c' /\
     b == { a with client = c' })

let tls_step_server_local (a b:tls_system_state) : prop =
  TlsQuiet? a.channel /\
  (exists (lev:CS.local_event) (s':CS.connection_state).
     ep_apply a.server (CS.ConnLocalEvent lev) == Some s' /\
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

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_client_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_client_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (hmsg:M.handshake_msg) (c':CS.connection_state).
      sent_field_none CS.ClientEndpoint a.client hmsg /\
      ep_apply a.client (CS.sent_tls_event (M.TlsHandshake hmsg)) == Some c' /\
      client_stage_ok c' /\
      b == { a with client = c';
                    channel = TlsInFlight CS.ServerEndpoint (M.TlsHandshake hmsg) }
    returns tls_system_inv b
    with _pf.
      (lemma_no_ku_append a.client.CS.cs_event_log
        (CS.sent_tls_event (M.TlsHandshake hmsg));
       match hmsg with
       | M.ClientHello ch -> ()
       | M.Finished cf -> ()
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_server_send (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_send a b)
          (ensures tls_system_inv b)
  = eliminate exists (hmsg:M.handshake_msg) (s':CS.connection_state).
      sent_field_none CS.ServerEndpoint a.server hmsg /\
      (M.Finished? hmsg ==>
         (Some? (hsf a.server).CS.hs_certificate /\
          Some? (hsf a.server).CS.hs_certificate_verify)) /\
      ep_apply a.server (CS.sent_tls_event (M.TlsHandshake hmsg)) == Some s' /\
      server_stage_ok s' /\
      b == { a with server = s';
                    channel = TlsInFlight CS.ClientEndpoint (M.TlsHandshake hmsg) }
    returns tls_system_inv b
    with _pf.
      (lemma_no_ku_append a.server.CS.cs_event_log
        (CS.sent_tls_event (M.TlsHandshake hmsg));
       match hmsg with
       | M.ServerHello sh -> ()
       | M.EncryptedExtensions ee -> ()
       | M.Certificate cert -> ()
       | M.CertificateVerify cv -> ()
       | M.Finished sf -> ()
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_deliver_to_client (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_client a b)
          (ensures tls_system_inv b)
  = eliminate exists (m:M.tls_message) (c':CS.connection_state).
      a.channel == TlsInFlight CS.ClientEndpoint m /\
      ep_apply a.client (CS.received_tls_event m) == Some c' /\
      client_stage_ok c' /\
      b == { a with client = c'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_no_ku_append a.client.CS.cs_event_log (CS.received_tls_event m);
       match m with
       | M.TlsHandshake (M.ServerHello sh) -> ()
       | M.TlsHandshake (M.EncryptedExtensions ee) -> ()
       | M.TlsHandshake (M.Certificate cert) -> ()
       | M.TlsHandshake (M.CertificateVerify cv) -> ()
       | M.TlsHandshake (M.Finished sf) -> ()
       | _ -> ())
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_deliver_to_server (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_deliver_to_server a b)
          (ensures tls_system_inv b)
  = eliminate exists (m:M.tls_message) (s':CS.connection_state).
      a.channel == TlsInFlight CS.ServerEndpoint m /\
      ep_apply a.server (CS.received_tls_event m) == Some s' /\
      server_stage_ok s' /\
      b == { a with server = s'; channel = TlsQuiet }
    returns tls_system_inv b
    with _pf.
      (lemma_no_ku_append a.server.CS.cs_event_log (CS.received_tls_event m);
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
      ep_apply a.client (CS.ConnLocalEvent lev) == Some c' /\
      preserves_tracked_fields a.client c' /\
      client_stage_ok c' /\
      b == { a with client = c' }
    returns tls_system_inv b
    with _pf.
      (lemma_no_ku_append a.client.CS.cs_event_log (CS.ConnLocalEvent lev))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_pres_server_local (a b:tls_system_state)
  : Lemma (requires tls_system_inv a /\ tls_step_server_local a b)
          (ensures tls_system_inv b)
  = eliminate exists (lev:CS.local_event) (s':CS.connection_state).
      ep_apply a.server (CS.ConnLocalEvent lev) == Some s' /\
      preserves_tracked_fields a.server s' /\
      server_stage_ok s' /\
      b == { a with server = s' }
    returns tls_system_inv b
    with _pf.
      (lemma_no_ku_append a.server.CS.cs_event_log (CS.ConnLocalEvent lev))
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
