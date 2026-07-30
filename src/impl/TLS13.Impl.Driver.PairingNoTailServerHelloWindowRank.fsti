module TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module PNI = TLS13.Impl.Driver.PairingNoTailInversion

(**
  Corrected, exactly-tight SERVER-role obligation-rank measure for the "hello
  window": the stages from [CS.HsServerHelloSent] through
  [CS.ControlApplicationData] that follow the (already-established) 5-event
  cleartext prefix ending in [Sent ServerHello]
  ([TLS13.ConnectionState.ProtectedWireSegmentation.server_cleartext_handshake_prefix_events]).

  This module exists to close the specific gap documented in
  [TLS13.Impl.Driver.PairingNoTailServerShape.server_no_tail_next_two_events_handshake_installs]:
  a bare role-local length-16 hypothesis was believed too weak to rule out an
  extra [TlsChangeCipherSpec] no-op immediately after [Sent ServerHello].

  The existing *private* measure [server_application_progress_rank] in
  [TLS13.Impl.Driver.PairingNoTailServerShape.fst] (used there for the older,
  stale length-15 boundary) bundles the entire encrypted-flight sub-phase
  ([Sent EncryptedExtensions], [Sent Certificate],
  [LocalSignCertificateVerify], [Sent CertificateVerify], [Sent Finished])
  into a single opaque [server_encrypted_flight_constant] driven only by
  [hs_certificate] and [hs_certificate_verify_verified]. That constant does
  *not* change when [LocalSignCertificateVerify] fires (it only sets
  [hs_certificate_verify], which the old constant never inspects), so the old
  measure under-counts the true minimal remaining-event budget by exactly one
  at every encrypted-flight stage. That one-unit under-count is precisely the
  slack a spurious [TlsChangeCipherSpec] would need, so the old measure
  cannot rule one out immediately after [Sent ServerHello].

  [server_hello_window_rank] below fixes this by tracking
  [hs_certificate_verify] (the local sign step) as its own obligation, in
  addition to [hs_encrypted_extensions], [hs_certificate] and
  [hs_certificate_verify_verified]. With this fix the rank is *exactly* 9 at
  a fresh [HsServerHelloSent] model (see
  [lemma_server_hello_window_rank_fresh_is_nine]) and decreases by
  *exactly* 1 on every one of the 9 events of the minimal completion path to
  [CS.ControlApplicationData] (Model-Fix-1 made recv-Finished atomic, merging
  the old 3-step client-Finished delivery into a single event and shortening
  the window by 2), with zero slack anywhere -- this was checked
  by hand against every legal transition in
  [TLS13.Spec.StateMachine.legal_event]/[step_model] for the
  [ServerEndpoint] role at these stages (see
  [lemma_server_hello_window_rank_step]).

  [lemma_server_hello_window_tight_next_event_handshake_traffic_install] is
  the reusable payload: given the rank is exactly tight against the number of
  events remaining (i.e. no event has yet been "wasted"), the very next event
  cannot be a [TlsChangeCipherSpec] no-op or a failure, so by exhaustive
  legality case analysis at these stages it must be a
  [PNI.server_no_tail_handshake_traffic_install_event]. Applying it twice in
  a row (once at a fresh [HsServerHelloSent] model, once more at the
  resulting model after the first install) is exactly what is needed to
  prove [server_no_tail_next_two_events_handshake_installs].  This module also
  exposes the model-local prefix-boundary facts needed by
  [PairingNoTailServerPostHelloShape.lemma_clean16_no_tail_valid_byte_traces_server_next_two_events_handshake_installs],
  where the clean16 paired byte-trace hypotheses supply the actual event-log
  prefix/suffix split.
**)

(**
  Deliberately written as a "staircase" of nested conditionals on the *most
  advanced* flag first (verified, then signed, then certificate sent, then
  encrypted extensions sent), rather than as an additive sum of independent
  [option_missing] terms.  [handshake_state] is a plain record with no
  dependent-type coupling between these fields, so a per-step lemma that is
  universally quantified over arbitrary [connection_model] values (as
  opposed to only history-reachable ones) must also handle ill-formed
  combinations where, say, [hs_certificate_verify_verified] is [true] while
  [hs_certificate] is [None] (nothing here rules that out for an arbitrary
  model satisfying only the *current* transition's [legal_event]
  precondition, which does not reference earlier-stage fields). With an
  additive sum, such a combination can make the measure *increase* across a
  transition that only ever sets a single one of these fields (e.g.
  [Sent EncryptedExtensions] only touches [hs_encrypted_extensions], but a
  weird model with [hs_certificate] already [Some] would have the sum
  decrease by only the encrypted-extensions term while carrying stale
  certificate/verify contributions, ***not*** breaking anything -- but the
  dual issue, an already-[verified] model with the *earlier* fields still
  [None], breaks the "flight is essentially done" collapse the old
  [TLS13.Impl.Driver.PairingNoTailServerShape.server_encrypted_flight_constant]
  relied on). The staircase avoids this: each transition only ever flips the
  one field examined at its own priority level, and every check for a
  *later* stage's flag short-circuits before ever inspecting that field, so
  the measure is provably insensitive to any such earlier-field weirdness
  and never moves by more than the single priority level touched.
**)
noextract
let server_hello_window_late_flight_progress
  (hs:CS.handshake_state)
  : nat =
  if hs.CS.hs_certificate_verify_verified then 0
  else if Some? hs.CS.hs_certificate_verify then 1
  else if Some? hs.CS.hs_certificate then 2
  else if Some? hs.CS.hs_encrypted_extensions then 3
  else 4

noextract
let server_hello_window_app_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  PNI.option_missing keys.CS.ks_shared_secret +
  PNI.option_missing keys.CS.ks_server_application_traffic +
  PNI.option_missing keys.CS.ks_client_application_traffic

noextract
let server_hello_window_handshake_traffic_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  PNI.option_missing keys.CS.ks_server_handshake_traffic +
  PNI.option_missing keys.CS.ks_client_handshake_traffic

noextract
let server_hello_window_rank
  (model:CS.connection_model)
  : nat =
  let hs = model.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  let final_rank = server_hello_window_app_obligation_rank keys in
  match model.CS.model_control with
  | CS.ControlApplicationData ->
    final_rank
  | CS.ControlHandshaking CS.HsServerHelloSent ->
    1 +
    server_hello_window_late_flight_progress hs +
    server_hello_window_handshake_traffic_obligation_rank keys +
    final_rank
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent ->
    1 +
    server_hello_window_late_flight_progress hs +
    PNI.option_missing keys.CS.ks_client_handshake_traffic +
    final_rank
  | CS.ControlHandshaking CS.HsServerFinishedSent ->
    PNI.option_missing keys.CS.ks_client_handshake_traffic +
    final_rank
  | CS.ControlHandshaking CS.HsClientFinishedReceived ->
    1 + final_rank
  | _ ->
    0

val lemma_server_hello_window_rank_fresh_is_nine
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false)
      (ensures server_hello_window_rank model == 9)

val lemma_server_hello_window_rank_application_data_installed_zero
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlApplicationData /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        CS.application_record_keys_installed_for_role
          CS.ServerEndpoint
          model)
      (ensures server_hello_window_rank model == 0)

val lemma_server_hello_window_after_server_cleartext_prefix_fresh
  (model0:CS.connection_model)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (model1:CS.connection_model)
  (model2:CS.connection_model)
  (model3:CS.connection_model)
  (model4:CS.connection_model)
  (model5:CS.connection_model)
  : Lemma
      (requires
        model0 == CS.initial_model model0.CS.model_config /\
        model0.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.step_model
          model0
          (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
        CS.step_model
          model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some model2 /\
        CS.step_model
          model2
          (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
          Some model3 /\
        CS.step_model
          model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
          Some model4 /\
        CS.step_model
          model4
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some model5)
      (ensures
        model5.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model5.CS.model_handshake.CS.hs_certificate == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        server_hello_window_rank model5 == 9)

val lemma_server_hello_window_rank_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived) /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        CS.ControlFailed? model'.CS.model_control \/
        server_hello_window_rank model <= server_hello_window_rank model' + 1)

val lemma_server_hello_window_rank_replay_lower_bound
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived \/
         model.CS.model_control == CS.ControlApplicationData) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model events raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_hello_window_rank final_model == 0)
      (ensures
        server_hello_window_rank model <= FStar.List.Tot.length events)

(**
  Auxiliary "stuck-forever" fact, needed because the tightness argument
  below is a numeric *upper* bound
  ([server_hello_window_rank model <= length events]) and, on its own, does
  not exclude [Sent EncryptedExtensions] firing while the
  [ServerEndpoint]/[TrafficHandshake]/[TrafficRead] key (i.e.
  [hs_keys.ks_client_handshake_traffic]) is still un-installed: that specific
  transition is legal (it only requires the *write* handshake key,
  [ks_server_handshake_traffic], to already be installed) and decreases the
  rank by exactly 1, so it is not numerically "wasteful". What rules it out
  is a different, non-numeric fact: [TrafficHandshake] key installs are only
  ever legal while [model_control == ControlHandshaking HsServerHelloSent]
  ([CS.traffic_install_allowed_at_stage_for_role]), and once
  [Sent EncryptedExtensions] fires the model leaves that stage for good (the
  handshake-stage machine here is a strict one-way sequence with no path back
  to [HsServerHelloSent]). So if the read key is still missing at that point,
  it can *never* become installed afterwards, which makes it permanently
  impossible to satisfy the [Some? ks_client_handshake_traffic] precondition
  of [Received Finished @ HsServerFinishedSent]
  ([TLS13.Spec.StateMachine.legal_handshake_message]) -- the connection
  can then only stall forever on [TlsChangeCipherSpec] no-ops or eventually
  fail, but can never legally reach [CS.ControlApplicationData].
**)
val lemma_server_hello_window_stuck_without_client_handshake_traffic
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent) /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model events raw_sent raw_received final_model)
      (ensures ~ (final_model.CS.model_control == CS.ControlApplicationData))

(**
  Tightness derivation: given the model is at [HsServerHelloSent] with the
  late-flight fields still fresh and *not both* [TrafficHandshake] keys
  installed yet, and the rank is *exactly* tight against the number of
  events remaining before [CS.ControlApplicationData]
  ([server_hello_window_rank model == length rest + 1], i.e. [ev] is the
  first of the tight remaining budget), [ev] cannot be a
  [TlsChangeCipherSpec] no-op (that would leave the rank unchanged at
  [server_hello_window_rank model], contradicting the lower bound once only
  [length rest] events remain), a failure (which can never reach
  [CS.ControlApplicationData]), nor [Sent EncryptedExtensions] fired while
  the read key is still missing (excluded by
  [lemma_server_hello_window_stuck_without_client_handshake_traffic] above);
  by exhaustive legality case analysis at this stage the only remaining
  possibility is a genuine [ServerEndpoint]/[TrafficHandshake] key install.

  The "not both keys installed yet" hypothesis holds at both intended call
  sites: with neither key installed (proving the *first* of the two target
  events is an install), and with exactly one key installed after applying
  this lemma once (proving the *second* target event is also an install).
**)
val lemma_server_hello_window_tight_next_event_handshake_traffic_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        ~ (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
           Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic) /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_hello_window_rank final_model == 0 /\
        server_hello_window_rank model == FStar.List.Tot.length rest + 1)
      (ensures PNI.server_no_tail_handshake_traffic_install_event ev)

val lemma_server_hello_window_tight_next_two_events_handshake_traffic_installs
  (model:CS.connection_model)
  (ev0:CS.conn_event)
  (ev1:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model
          (ev0 :: ev1 :: rest)
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_hello_window_rank final_model == 0 /\
        server_hello_window_rank model ==
          FStar.List.Tot.length (ev1 :: rest) + 1)
      (ensures
        PNI.server_no_tail_handshake_traffic_install_event ev0 /\
        PNI.server_no_tail_handshake_traffic_install_event ev1)
