module TLS13.ConnectionState.ClientCanonicalShape

(**
  Exact event-log SPINE decomposition for a CANONICAL-reachable TLS 1.3 CLIENT
  connection that has reached [ControlApplicationData], proved by FORWARD
  INDUCTION over the canonical reachability trace ([WStep.client_reachable], i.e.
  [SM.valid_state (WStep.client_sm init)]).

  This is the CLIENT MIRROR of [TLS13.ConnectionState.ServerCanonicalShape].  It
  is over CANONICAL reachability and concludes an EXACT list equality [==]:

      cs_event_log ==
        client_cleartext_handshake_prefix_events start ch sh client_shared
        ++ region
        ++ ( Received EncryptedExtensions ee
           :: Received Certificate cert
           :: cv_validate (= LocalValidateCertificate peer)
           :: Received CertificateVerify cv
           :: cv_verify (= LocalVerifyCertificateSignature cv)
           :: Received Finished sf
           :: tail )

  where [region] is an existential run of ClientEndpoint TrafficHandshake key
  installs (either direction, via the PLAIN [LocalInstallTrafficKeys]
  constructor), and it necessarily contains at least one READ install (forced by
  decoding the received EncryptedExtensions flight) and at least one WRITE
  install (forced by the client's own Finished send required to reach
  [ControlApplicationData]).

  Under Model-Fix-1 the client's receipt of the server Finished is ATOMIC: the
  [Received Finished sf] step (arm [HsCertificateVerifyVerified] -> lands at
  [HsServerFinishedVerified]) also derives the server-application read secret and
  installs the server-application read keys WITHIN the single step, so those are
  NOT separate [region]/tail conn_events.  In particular [ClientVerifyFinished]
  is NOT emitted as a separate local conn_event on the honest path (the honest
  path never visits [HsServerFinishedReceived]); it is folded into the atomic
  [Received Finished sf] step.  The two per-message local skips ([cv_validate =
  LocalValidateCertificate peer] after [Received Certificate], and [cv_verify =
  LocalVerifyCertificateSignature cv] after [Received CertificateVerify]) are the
  only local conn_events interspersed in the received encrypted flight; they are
  kept ABSTRACT as [CS.local_event].

  The hypothesis [log_has_no_received_ccs] rules out the only remaining source of
  interspersion (received ChangeCipherSpec, legal at every handshaking stage);
  canonical reachability rules out other events.
**)

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module C = TLS13.Crypto.Spec
module EC = TLS13.Spec.Endpoint.Client
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

(** A received ChangeCipherSpec network event.  (Identical to the server
    module's [is_received_ccs] so a later joint module can unify them.) *)
let is_received_ccs (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnNetworkEvent msg ->
    msg.CL.message_direction = CL.Received &&
    (match msg.CL.message_value with M.TlsChangeCipherSpec -> true | _ -> false)
  | _ -> false

(** No received ChangeCipherSpec anywhere in the log. *)
let log_has_no_received_ccs (log:list CS.conn_event) : prop =
  forall (ev:CS.conn_event). L.memP ev log ==> is_received_ccs ev == false

(** A ClientEndpoint TrafficHandshake key install event (either direction).
    The client uses the PLAIN [LocalInstallTrafficKeys] constructor. *)
let is_client_hs_install (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match install.CS.install_epoch with
     | CS.TrafficHandshake -> true
     | _ -> false)
  | _ -> false

(** The same, pinned to a traffic direction. *)
let is_client_hs_install_dir (d:CS.traffic_direction) (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match install.CS.install_epoch with
     | CS.TrafficHandshake -> true
     | _ -> false) &&
    install.CS.install_direction = d
  | _ -> false

(* ------------------------------------------------------------------ *)
(* Top lemma                                                           *)
(* ------------------------------------------------------------------ *)

val lemma_client_canonical_appdata_exact_spine
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.client_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
       log_has_no_received_ccs s.CS.cs_event_log)
    (ensures
       (exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
          (client_shared:C.x25519_shared_secret)
          (region:list CS.conn_event)
          (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
          (cv_validate:CS.local_event)
          (cv:GCV.certificateVerify)
          (cv_verify:CS.local_event)
          (sf:GFin.finished)
          (tail:list CS.conn_event).
          (forall (e:CS.conn_event). L.memP e region ==> is_client_hs_install e == true) /\
          (exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er) /\
          (exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew) /\
          s.CS.cs_event_log ==
            L.append
              (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
              (L.append region
                 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                  CS.ConnLocalEvent cv_validate ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                  CS.ConnLocalEvent cv_verify ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                  tail))))

(** Shared-secret PRESENCE at [HsServerFinishedVerified], extracted from
    CANONICAL reachability + no-received-CCS.  Load-bearing brick for the
    non-ready cross-endpoint HANDSHAKE agreement producer: NOT derivable from
    [connection_state_consistent] alone (the model-level x25519 shape cannot pin
    presence at this control), but the canonical [sfv_region_ok] forces it. **)
val lemma_client_reachable_sfv_shared_secret_present
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.client_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
       log_has_no_received_ccs s.CS.cs_event_log)
    (ensures Some? s.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
