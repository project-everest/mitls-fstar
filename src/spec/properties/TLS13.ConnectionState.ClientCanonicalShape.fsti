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
module SM = Common.StateMachine
module CW = TLS13.Spec.Endpoint.Wire
module CTy = TLS13.Impl.CanonicalTypes
module EAPI = TLS13.Spec.Endpoint.API
module B = TLS13.Bytes
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

(** A BUFFERING protected-handshake step: takes delivery of one record,
    appends its plaintext to the pending reassembly buffer, and delivers NO
    message (see the module-level comment on [protected_handshake_buffering]
    in [TLS13.Spec.StateMachine]). *)
let is_protected_buffering_step (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnProtectedHandshake step -> step.CS.protected_handshake_buffering
  | _ -> false

(** No BUFFERING protected-handshake step anywhere in the log.  Mirrors
    [log_has_no_received_ccs] exactly, and is threaded through the forward
    induction ([lemma_trace_shape]) via the SAME per-step membership argument
    already used to exclude received CCS: a buffering step is legal only for
    a [ClientEndpoint] at the four stages in
    [CS.protected_handshake_buffering_stage], and the exact-log-SHAPE
    invariant this file maintains ([log_shape]/[*_region_ok]) pins the
    "region" of key installs to be EXACTLY the [is_client_hs_install] events
    seen so far -- a genuinely reachable buffering step at one of those
    stages would put a non-install event where the invariant has no room for
    one.  In the PAIRED SYSTEM (a verified ATLAS client talking to the
    verified ATLAS server) this hypothesis is always true and dischargeable
    from [SY.tls_system_inv]: the server emits exactly one record per
    handshake message, so every record the client receives during the
    honest run opens to a COMPLETE handshake message, and
    [legal_protected_handshake_step]'s STEP-1 guard makes buffering illegal
    whenever the pending buffer is empty and the fragment parses in full --
    which is inductively always the case against this server.  Cross-record
    buffering only arises against a THIRD-PARTY server that really does
    split messages across records, which the paired-system theorems below do
    not model. *)
let no_buffering_steps (log:list CS.conn_event) : prop =
  forall (ev:CS.conn_event). L.memP ev log ==> is_protected_buffering_step ev == false

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
    handshake message it contributes to the top-level audit trace -- UNLESS
    it is a BUFFERING step (see [CS.protected_handshake_buffering]): a
    buffering step takes delivery of one record, appends its plaintext to the
    pending reassembly buffer, and advances [record_read.seq], but delivers
    NO message.  Its [protected_handshake_message] field is INERT (legality
    pins only [offset]/[consumed] to 0 and says nothing about the message;
    the implementation sets it to an arbitrary placeholder), so routing it
    through the [ConnNetworkEvent] case below would fabricate a received
    handshake message that never arrived -- the same soundness bug we already
    fixed in [TLS13.Spec.StateMachine.Log].

    For a buffering step we leave [ev] UNCHANGED (still a
    [ConnProtectedHandshake]).  This is enough on its own, with NO other
    change anywhere in this file: [CS.ConnProtectedHandshake _] can never
    equal [CS.ConnNetworkEvent _] (different constructors of [conn_event]),
    so any hypothesis of the shape [canonical_log log == ... @ [ee_ev; ...] @
    ...] -- which pins six POSITIONS of [canonical_log log] to
    [ConnNetworkEvent]/[ConnLocalEvent] values -- already, syntactically,
    forces the raw event at each of those positions to be non-buffering. *)
let canonical_event (ev:CS.conn_event) : CS.conn_event =
  match ev with
  | CS.ConnProtectedHandshake step ->
    if step.CS.protected_handshake_buffering
    then ev
    else
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

(** A CLIENT LOCAL step (no wire output) as ONE existential witness exposing
    BOTH the underlying `conn_event`'s legality/step facts AND its exact
    event-log append -- unlike [TLS13.System.AppSeqPairing.lemma_client_local_extract],
    which exposes the former but not the latter (it has no use for the event
    log).  Callers that need to reason about `cs_event_log` across a client-local
    step (e.g. to propagate [no_buffering_steps]) need the SAME witness to carry
    both facts, since two separately-obtained existentials need not agree on
    which `conn_event` they describe. *)
val lemma_client_local_step_event_log_append
  (st0 c':CS.connection_state) (local:CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 (SM.LocalEvent local) c' out /\
        out.SM.so_wire_outputs == [])
      (ensures
        exists (ce:CS.conn_event).
          CS.legal_event st0.CS.cs_model ce /\
          CS.step_model st0.CS.cs_model ce == Some c'.CS.cs_model /\
          CS.event_raw_delta_legal st0.CS.cs_model ce B.empty B.empty /\
          c'.CS.cs_event_log == L.append st0.CS.cs_event_log [ce])

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
       log_has_no_received_ccs s.CS.cs_event_log /\
       (* Needed so the forward induction underlying this lemma can rule a
          BUFFERING step out at each of the four stages where it is legal
          ([CS.protected_handshake_buffering_stage]): such a step would put a
          non-install event where the region invariant maintained below has
          no room for one (see [no_buffering_steps]'s docstring).  In the
          PAIRED SYSTEM this is always true, dischargeable from
          [SY.tls_system_inv]. *)
       no_buffering_steps s.CS.cs_event_log)
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
       log_has_no_received_ccs s.CS.cs_event_log /\
       no_buffering_steps s.CS.cs_event_log)
    (ensures Some? s.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
