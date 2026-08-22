module TLS13.ConnectionState.ServerCanonicalShape

(**
  Exact event-log SPINE decomposition for a CANONICAL-reachable TLS 1.3 SERVER
  connection that has reached [ControlApplicationData], proved by FORWARD
  INDUCTION over the canonical reachability trace ([WStep.server_reachable], i.e.
  [SM.valid_state (WStep.server_sm init)]).

  Unlike [TLS13.ConnectionState.ServerLogShape] (which is over MODEL-LEVEL
  reachability [SR.connection_state_consistent] and concludes an ORDERED
  SUBSEQUENCE [is_subsequence]), this module is over CANONICAL reachability and
  concludes an EXACT list equality [==]:

      cs_event_log ==
        server_cleartext_handshake_prefix_events ch selection server_shared sh
        ++ region
        ++ ( Sent EncryptedExtensions ee
           :: Sent Certificate cert
           :: cv_local (= LocalSignCertificateVerify cv)
           :: Sent CertificateVerify cv
           :: Sent Finished sf
           :: tail )

  where [region] is an existential run of ServerEndpoint TrafficHandshake key
  installs (either direction), and it necessarily contains at least one WRITE
  install (forced by the EncryptedExtensions send) and at least one READ install
  (forced by the received client Finished).  The hypothesis
  [log_has_no_received_ccs] rules out the only remaining source of interspersion
  (received ChangeCipherSpec, legal at every handshaking stage); canonical
  reachability rules out non-role installs and sent ChangeCipherSpec.
**)

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module C = TLS13.Crypto.Spec
module ES = TLS13.Spec.Endpoint.Server
module WStep = TLS13.System.WireStep
module SMCan = TLS13.Spec.StateMachine.Canonical
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module L = FStar.List.Tot

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

(** A received ChangeCipherSpec network event. *)
let is_received_ccs (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnNetworkEvent msg ->
    msg.CL.message_direction = CL.Received &&
    (match msg.CL.message_value with M.TlsChangeCipherSpec -> true | _ -> false)
  | _ -> false

(** No received ChangeCipherSpec anywhere in the log. *)
let log_has_no_received_ccs (log:list CS.conn_event) : prop =
  forall (ev:CS.conn_event). L.memP ev log ==> is_received_ccs ev == false

(** A cleartext-handshake BUFFERING step: takes delivery of one record, appends
    its fragment to the pending cleartext reassembly buffer, and delivers NO
    message. *)
let is_cleartext_buffering_step (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnCleartextHandshake _ -> true
  | _ -> false

(** No cleartext-handshake BUFFERING step anywhere in the log.

    Server mirror of [ClientCanonicalShape.no_buffering_steps], and threaded
    through the forward induction ([lemma_trace_shape]) by the SAME per-step
    membership argument already used here to exclude received CCS.

    The exact-log-SHAPE invariant this file maintains ([log_shape] /
    [*_region_ok]) pins the event log to an EXACT list of milestone events per
    control state.  A buffering step appends to that log WITHOUT moving the
    control, so it violates the [HsAwaitingClientHello] arm outright and shifts
    every later arm.  Rather than move [log_shape] onto a filtered view of the
    log -- which would push an existential all the way into the flagship
    inversion lemmas that consume its exact-list conclusion
    ([ProtectedWireServerFlightInversion], [ProtectedWireClientFinishedInversion])
    -- the shape lemmas simply do not speak about logs that contain buffering.
    This is exactly the scoping the client already uses for its own
    cross-record reassembly, and those two flagship lemmas ALREADY carry the
    client's version of this hypothesis as a [requires].

    In the PAIRED SYSTEM this hypothesis holds: the verified client emits each
    cleartext handshake message as exactly one record, so the server never has
    cause to buffer.  Cross-record ClientHellos arise only against a THIRD-PARTY
    client that really does split them, which the paired-system theorems do not
    model. *)
let no_cleartext_buffering_steps (log:list CS.conn_event) : prop =
  forall (ev:CS.conn_event). L.memP ev log ==> is_cleartext_buffering_step ev == false

(** A ServerEndpoint TrafficHandshake key install event (either direction). *)
let is_server_hs_install (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole ri) ->
    (match ri.CS.install_role with CS.ServerEndpoint -> true | _ -> false) &&
    (match ri.CS.install_payload.CS.install_epoch with
     | CS.TrafficHandshake -> true
     | _ -> false)
  | _ -> false

(** The same, pinned to a traffic direction. *)
let is_server_hs_install_dir (d:CS.traffic_direction) (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole ri) ->
    (match ri.CS.install_role with CS.ServerEndpoint -> true | _ -> false) &&
    (match ri.CS.install_payload.CS.install_epoch with
     | CS.TrafficHandshake -> true
     | _ -> false) &&
    ri.CS.install_payload.CS.install_direction = d
  | _ -> false

(* ------------------------------------------------------------------ *)
(* Top lemma                                                           *)
(* ------------------------------------------------------------------ *)

(** STAGING DISCHARGE.  [WStep.server_sm] is currently built over
    [ES.server_step_nonbuffering], so no reachable server log contains a
    cleartext-handshake buffering step and every
    [no_cleartext_buffering_steps] gate above is derivable from reachability
    alone.  This val is DELETED together with [ES.server_step_nonbuffering];
    at that point those gates stop being derivable and start carrying real
    content, exactly as the client's [no_buffering_steps] gates do. *)
val lemma_server_reachable_no_cleartext_buffering
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma (requires WStep.server_reachable (CS.initial cfg) s)
          (ensures no_cleartext_buffering_steps s.CS.cs_event_log)

val lemma_server_canonical_appdata_exact_spine
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.server_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
       log_has_no_received_ccs s.CS.cs_event_log /\
       no_cleartext_buffering_steps s.CS.cs_event_log)
    (ensures
       (exists (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
          (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
          (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
          (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
          (region:list CS.conn_event) (tail:list CS.conn_event).
          (forall (e:CS.conn_event). L.memP e region ==> is_server_hs_install e == true) /\
          (exists (ew:CS.conn_event). L.memP ew region /\ is_server_hs_install_dir CS.TrafficWrite ew) /\
          (exists (er:CS.conn_event). L.memP er region /\ is_server_hs_install_dir CS.TrafficRead er) /\
          s.CS.cs_event_log ==
            L.append
              (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
              (L.append region
                 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                  CS.ConnLocalEvent cv_local ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                  tail))))

(** Shared-secret PRESENCE at [HsServerFinishedSent], extracted from CANONICAL
    reachability + no-received-CCS.  Server mirror of the client brick; the
    canonical [sfs_region_ok] forces it, whereas [connection_state_consistent]
    alone cannot pin presence at this control. **)
val lemma_server_reachable_sfs_shared_secret_present
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.server_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
       log_has_no_received_ccs s.CS.cs_event_log /\
       no_cleartext_buffering_steps s.CS.cs_event_log)
    (ensures Some? s.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)

(** The server's client-handshake-traffic (READ) key slot is installed only at
    control [HsServerHelloSent], at which point both the ClientHello and the
    ServerHello have already been recorded; and neither those fields nor the slot
    is ever cleared afterwards (in particular [fail_model] preserves
    [model_handshake] wholesale).  Hence, at ANY CANONICAL-reachable server state
    — including a failed one, where the control-keyed [server_canonical_shape]
    carries no information — presence of the slot forces both hellos present.
    Proved by monotone forward induction over the canonical trace. **)
val lemma_server_reachable_traffic_slot_hellos_present
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.server_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       Some? s.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
       log_has_no_received_ccs s.CS.cs_event_log /\
       no_cleartext_buffering_steps s.CS.cs_event_log)
    (ensures
       Some? s.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
       Some? s.CS.cs_model.CS.model_handshake.CS.hs_client_hello)

