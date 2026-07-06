module TLS13.ConnectionState.ClientCertificateVerifyReachability

(**
  Client-side reachability fact: a client connection that has reached
  application-ready control state (`ControlApplicationData`) must have a
  recorded `hs_certificate_verify` witness in its model handshake state.

  This is the client-side half of the asymmetry documented in
  PAIRING_THEOREM.md's server-only counterexample for
  `TLS13.Impl.Driver.PairingNoTailServerShape.server_no_tail_next_two_events_handshake_installs`.
  The server can locally sign (and thus "witness") a CertificateVerify message
  via `LocalSignCertificateVerify` without ever emitting a network `Sent
  CertificateVerify` event, so a bare role-local server theorem cannot rule
  out the server skipping the wire send.  The client has no such bypass: every
  legal client transition from `HsCertificateValidated` onward to
  `ControlApplicationData` passes through a genuine network `Received
  CertificateVerify` event (`step_handshake_message`, case
  `CL.Received, M.CertificateVerify cv, ControlHandshaking
  HsCertificateValidated`), and `hs_certificate_verify` is never reset once
  set.  This module proves that fact as a reachability invariant over
  `connection_state_consistent`, by lifting a single-step-preserved predicate
  through `FStar.ReflexiveTransitiveClosure.stable_on_closure`, following the
  established proof pattern in `TLS13.ConnectionState.Lemmas.fst` (e.g.
  `lemma_connection_state_consistent_supported_profile_key_schedule_reachable_shape`).
**)

open TLS13.Spec.ConnectionState

(**
  The handshake stages (plus `ControlApplicationData`) at or after which a
  legally-stepping CLIENT connection must already have recorded a
  `hs_certificate_verify` witness.
**)
noextract
let client_certificate_verify_downstream_control
  (control:connection_control_state)
  : prop =
  match control with
  | ControlHandshaking HsCertificateVerifyReceived
  | ControlHandshaking HsCertificateVerifyVerified
  | ControlHandshaking HsServerFinishedReceived
  | ControlHandshaking HsServerFinishedVerified
  | ControlApplicationData -> True
  | _ -> False

(**
  Role-local model invariant: for a CLIENT-configured model, being at or past
  the CertificateVerify-downstream control states implies a certificate
  verify witness has been recorded.
**)
noextract
let client_certificate_verify_reachability_invariant
  (model:connection_model)
  : prop =
  model.model_config.config_role == ClientEndpoint /\
  client_certificate_verify_downstream_control model.model_control ==>
  Some? model.model_handshake.hs_certificate_verify

val lemma_connection_state_consistent_client_certificate_verify_reachability
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures client_certificate_verify_reachability_invariant st.cs_model)

(**
  The headline corollary: a client connection that is consistent, configured
  as a client, and has reached `ControlApplicationData` has recorded a
  `hs_certificate_verify` witness.
**)
val lemma_client_application_ready_certificate_verify_witness
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_control == ControlApplicationData)
      (ensures Some? st.cs_model.model_handshake.hs_certificate_verify)
