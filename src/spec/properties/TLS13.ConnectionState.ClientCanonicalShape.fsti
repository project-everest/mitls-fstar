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

(** Project an authenticated protected-handshake step to the received
    handshake message it contributes to the top-level audit trace. *)
let canonical_event (ev:CS.conn_event) : CS.conn_event =
  match ev with
  | CS.ConnProtectedHandshake step ->
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake step.CS.protected_handshake_message;
    })
  | _ -> ev

let rec canonical_log (events:list CS.conn_event) : Tot (list CS.conn_event)
  (decreases events)
=
  match events with
  | [] -> []
  | ev :: rest -> canonical_event ev :: canonical_log rest

(** A received handshake message, as a conn_event. *)
let recv_handshake_ev (msg:M.handshake_msg) : CS.conn_event =
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake msg;
  }

(** A DELIVERY GROUP: the run of consecutive client events by which the client
    takes delivery of exactly one received handshake message.

    Today a group is always a singleton -- either a cleartext
    [ConnNetworkEvent], or a protected step, which [canonical_event] projects
    to the same network event.

    Once record receipt is separated from message processing (see
    INTERNAL_EVENT_PLAN.md), a protected group becomes a record event followed
    by the internal step that consumes it, and this predicate gains one case.
    Stating the spine over groups rather than over single events is what keeps
    that later change from perturbing the surrounding argument: the group is
    the unit that pairs with ONE sender event, because the sender emits exactly
    one record per handshake message
    ([protected_record_count Sent msg == 1]). *)
let delivers_handshake (grp:list CS.conn_event) (msg:M.handshake_msg) : prop =
  match grp with
  | [ev] -> canonical_event ev == recv_handshake_ev msg
  | _ -> False

(** While every delivery group is a singleton, the group IS its message
    event.  Consumers use this to descend from the group-shaped spine to the
    single event, without committing the spine's statement to singletons. *)
val lemma_delivers_handshake_singleton
  (grp:list CS.conn_event) (msg:M.handshake_msg)
  : Lemma
      (requires delivers_handshake grp msg)
      (ensures
        Cons? grp /\
        grp == [L.hd grp] /\
        canonical_event (L.hd grp) == recv_handshake_ev msg)

(** The actual raw encrypted-flight suffix, retaining protected head/drain
    events while identifying their canonical handshake messages.

    The suffix is an append of delivery groups rather than a cons-chain of
    single events; with singleton groups [L.append [x] l] reduces to [x :: l],
    so this is the same statement as before. *)
let raw_flight_spine
  (raw_suffix:list CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event)
  (cv:GCV.certificateVerify)
  (cv_verify:CS.local_event)
  (sf:GFin.finished)
  (tail:list CS.conn_event)
  : prop =
  exists (g_ee g_cert g_cv g_sf raw_tail:list CS.conn_event).
    raw_suffix ==
      L.append g_ee
        (L.append g_cert
          (CS.ConnLocalEvent cv_validate ::
            L.append g_cv
              (CS.ConnLocalEvent cv_verify ::
                L.append g_sf raw_tail))) /\
    delivers_handshake g_ee (M.EncryptedExtensions ee) /\
    delivers_handshake g_cert (M.Certificate cert) /\
    delivers_handshake g_cv (M.CertificateVerify cv) /\
    delivers_handshake g_sf (M.Finished sf) /\
    canonical_log raw_tail == tail

val lemma_client_raw_suffix_flight_spine
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (region raw_suffix log:list CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event)
  (cv:GCV.certificateVerify)
  (cv_verify:CS.local_event)
  (sf:GFin.finished)
  (tail:list CS.conn_event)
  : Lemma
      (requires
        (forall (e:CS.conn_event).
           L.memP e region ==> is_client_hs_install e == true) /\
        log ==
          L.append
            (PWSeg.client_cleartext_handshake_prefix_events
              start ch sh client_shared)
            (L.append region raw_suffix) /\
        canonical_log log ==
          L.append
            (PWSeg.client_cleartext_handshake_prefix_events
              start ch sh client_shared)
            (L.append region
              (CS.ConnNetworkEvent {
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
               } ::
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.Certificate cert);
               } ::
               CS.ConnLocalEvent cv_validate ::
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
               } ::
               CS.ConnLocalEvent cv_verify ::
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.Finished sf);
               } ::
               tail)))
      (ensures
        raw_flight_spine raw_suffix ee cert cv_validate cv cv_verify sf tail)

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
          (exists (raw_suffix:list CS.conn_event).
             s.CS.cs_event_log ==
               L.append
                 (PWSeg.client_cleartext_handshake_prefix_events
                   start ch sh client_shared)
                 (L.append region raw_suffix)) /\
          canonical_log s.CS.cs_event_log ==
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
