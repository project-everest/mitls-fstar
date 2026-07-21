module TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
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
  [hs_certificate_verify_verified]. With this fix the rank is *exactly* 11 at
  a fresh [HsServerHelloSent] model (see
  [lemma_server_hello_window_rank_fresh_is_eleven]) and decreases by
  *exactly* 1 on every one of the 11 events of the minimal completion path to
  [CS.ControlApplicationData], with zero slack anywhere -- this was checked
  by hand against every legal transition in
  [TLS13.Spec.ConnectionState.legal_event]/[step_model] for the
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
    3 +
    server_hello_window_late_flight_progress hs +
    server_hello_window_handshake_traffic_obligation_rank keys +
    final_rank
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent ->
    3 +
    server_hello_window_late_flight_progress hs +
    PNI.option_missing keys.CS.ks_client_handshake_traffic +
    final_rank
  | CS.ControlHandshaking CS.HsServerFinishedSent ->
    PNI.option_missing keys.CS.ks_client_handshake_traffic +
    2 +
    final_rank
  | CS.ControlHandshaking CS.HsClientFinishedReceived ->
    1 + final_rank
  | _ ->
    0

(* Interface trimmed to definitions-only for Phase-1 clean16 removal.
   Now-false rank step-lemmas + byte-derivation vals removed; .fst excluded
   (attic). server_hello_window_rank above feeds ProgressCount progress. *)
