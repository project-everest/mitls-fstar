module TLS13.System.StreamTemporal.Realized

(**
  THE STREAM-INTEGRITY FLAGSHIP, INSTANTIATED AT A STATE THE IMPLEMENTATION
  ACTUALLY BUILDS.

  `TLS13.System.StreamTemporal.lemma_flagship_stream_integrity` carries an entry
  hypothesis about the server's starting state:

      SY.server_config_valid_e2e (CS.initial cfg_s)

  That hypothesis is not derivable from spec-level reachability -- it conjoins a
  protocol fact (the server credential is present) with an implementation buffer
  bound (the certificate chain fits `max_server_certificate_chain_len`, which is
  strictly tighter than what the wire format permits).  Left as an entry
  hypothesis it is an ASSUMPTION ABOUT THE STARTING STATE, and a reader is
  entitled to ask whether any state the implementation can actually construct
  satisfies it.

  This module answers that question by discharging the hypothesis outright for
  the configuration the Pulse server constructor builds.  The chain of custody is:

    * `TLS13.Impl.Server.new_server` (and its erased-credential variant) already
      REQUIRE the chain bound of their caller, and now also ESTABLISH
      `CR.server_config_valid (CR.server_initial_state chain cred)` as a
      postcondition, proved via `CR.lemma_server_initial_state_config_valid`.
    * `lemma_server_config_valid_matches_entry_hypothesis` below shows that
      predicate is the flagship's entry hypothesis -- definitionally, not merely
      implying it.
    * `lemma_flagship_stream_integrity_realized` then instantiates the flagship
      at `CR.server_connection_config`, leaving NO server-side hypothesis beyond
      the constructor's own precondition.

  NOTE ON DIRECTION OF DEPENDENCY.  `TLS13.Impl.Server` is strictly upstream of
  `TLS13.System` (through `TLS13.Impl.Server.Driver.State`), so the Pulse module
  cannot itself name `SY.server_config_valid_e2e`.  That is why the shared
  predicate is defined upstream, in `TLS13.Impl.ConnectionState.Repr`, and the
  two are reconciled here rather than at the constructor.

  WHAT IS *NOT* CLAIMED.  The client-side hypotheses of the flagship
  (`config_role == ClientEndpoint` and the wire profile
  `WFL.supported_client_config_wire_profile`) are passed through unchanged; only
  the server-side entry condition is discharged here.
**)

module T      = Common.Temporal
module CS     = TLS13.Spec.StateMachine
module WFL    = TLS13.Spec.WireFormatLemmas
module SY     = TLS13.System
module STm    = TLS13.System.StreamTemporal
module CR     = TLS13.Impl.ConnectionState.Repr
module Bounds = TLS13.Impl.ConnectionState.Bounds
module B      = TLS13.Bytes

(** The implementation-layer predicate and the flagship's entry hypothesis are
    the same property.  Both are the conjunction of "credential present" with the
    chain bound, so this is definitional; stating it as an iff pins the agreement
    so that a later drift in either definition breaks HERE, loudly, rather than
    silently widening the gap between what the implementation guarantees and what
    the theorem consumes. **)
let lemma_server_config_valid_matches_entry_hypothesis (st:CS.connection_state)
  : Lemma (CR.server_config_valid st <==> SY.server_config_valid_e2e st)
=
  ()

(** THE FLAGSHIP, REALIZED.  For the server configuration built by the Pulse
    constructor `TLS13.Impl.Server.new_server`, application-data stream integrity
    holds on every run, under no server-side assumption other than the
    certificate-chain bound that constructor already imposes on its caller. **)
val lemma_flagship_stream_integrity_realized
  (cfg_c:CS.connection_config)
  (certificate_chain credential_identity:B.bytes)
  : Lemma
      (requires
        cfg_c.CS.config_role == CS.ClientEndpoint /\
        WFL.supported_client_config_wire_profile cfg_c /\
        B.length certificate_chain <= Bounds.max_server_certificate_chain_len)
      (ensures
        T.ag SY.tls_sys_step
          STm.stream_integrity_scoped
          (SY.initial_tls_system
            cfg_c
            (CR.server_connection_config certificate_chain credential_identity)))
let lemma_flagship_stream_integrity_realized cfg_c certificate_chain credential_identity =
  let cfg_s = CR.server_connection_config certificate_chain credential_identity in
  // The Pulse constructor's postcondition, at the spec level.
  CR.lemma_server_initial_state_config_valid certificate_chain credential_identity;
  // `CR.server_initial_state chain cred` IS `CS.initial cfg_s`, by definition.
  assert (CR.server_initial_state certificate_chain credential_identity == CS.initial cfg_s);
  lemma_server_config_valid_matches_entry_hypothesis (CS.initial cfg_s);
  assert (SY.server_config_valid_e2e (CS.initial cfg_s));
  // `server_connection_config` fixes `config_role = ServerEndpoint`.
  assert (cfg_s.CS.config_role == CS.ServerEndpoint);
  STm.lemma_flagship_stream_integrity cfg_c cfg_s
