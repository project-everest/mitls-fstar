module TLS13.ConnectionState.ClientCertificateVerifyReachability

module CL = TLS13.ConnectionLog
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module RTC = FStar.ReflexiveTransitiveClosure
module T = TLS13.Types

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay

#push-options "--split_queries always"

let lemma_step_handshake_message_client_certificate_verify_reachability
  (model:connection_model)
  (dir:direction)
  (msg:M.handshake_msg)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_reachability_invariant model /\
        legal_handshake_message model dir msg /\
        step_handshake_message model dir msg == Some model')
      (ensures client_certificate_verify_reachability_invariant model')
=
  match dir, msg, model.model_control with
  | CL.Sent, M.ClientHello _, ControlHandshaking HsStarted
  | CL.Received, M.ClientHello _, ControlHandshaking HsAwaitingClientHello
  | CL.Received, M.ServerHello _, ControlHandshaking HsClientHelloSent
  | CL.Sent, M.ServerHello _, ControlHandshaking HsClientHelloReceived
  | CL.Sent, M.EncryptedExtensions _, ControlHandshaking HsServerHelloSent
  | CL.Sent, M.Certificate _, ControlHandshaking HsServerEncryptedFlightSent
  | CL.Sent, M.CertificateVerify _, ControlHandshaking HsServerEncryptedFlightSent
  | CL.Sent, M.Finished _, ControlHandshaking HsServerEncryptedFlightSent
  | CL.Received, M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
  | CL.Received, M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
  | CL.Received, M.HelloRetryRequest, ControlHandshaking HsClientHelloSent ->
    // model'.model_control is not among the CertificateVerify-downstream
    // control states, so the invariant holds vacuously.
    ()
  | CL.Received, M.Finished _, ControlHandshaking HsServerFinishedSent ->
    // Fix 1 (atomic server delivery): the server delivering the client Finished
    // now lands at ControlApplicationData (a CertificateVerify-downstream state).
    // legal_handshake_message forces config_role == ServerEndpoint here, which
    // contradicts the ClientEndpoint antecedent of the (client-local) invariant,
    // so the implication holds vacuously.
    assert (model.model_config.config_role == ServerEndpoint);
    assert (model'.model_config == model.model_config)
  | CL.Received, M.CertificateVerify cv, ControlHandshaking HsCertificateValidated ->
    // The base case: a genuine network receipt of CertificateVerify records
    // the witness directly.
    assert (Some? model'.model_handshake.hs_certificate_verify)
  | CL.Received, M.Finished fin, ControlHandshaking HsCertificateVerifyVerified ->
    // model.model_control is already downstream, so by the (per-step)
    // hypothesis a witness was already recorded; this arm leaves
    // hs_certificate_verify untouched.
    assert (model'.model_handshake.hs_certificate_verify ==
            model.model_handshake.hs_certificate_verify);
    assert (model'.model_config == model.model_config)
  | CL.Sent, M.Finished fin, ControlHandshaking HsServerFinishedVerified ->
    assert (model'.model_handshake.hs_certificate_verify ==
            model.model_handshake.hs_certificate_verify);
    assert (model'.model_config == model.model_config)
  | _, _, _ ->
    assert False

let lemma_step_local_event_client_certificate_verify_reachability
  (model:connection_model)
  (ev:local_event)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_reachability_invariant model /\
        legal_local_event model ev /\
        step_local_event model ev == Some model')
      (ensures client_certificate_verify_reachability_invariant model')
=
  match ev, model.model_control with
  | LocalStartHandshake _, ControlNew
  | LocalStartServer, ControlNew
  | LocalSelectServerParameters _, ControlHandshaking HsClientHelloReceived
  | LocalDeriveSharedSecret _, ControlHandshaking HsServerHelloReceived
  | LocalDeriveSharedSecret _, ControlHandshaking HsClientHelloReceived
  | LocalValidateCertificate _, ControlHandshaking HsCertificateReceived
  | LocalSignCertificateVerify _, ControlHandshaking HsServerEncryptedFlightSent
  | LocalFail _, _ ->
    // model'.model_control is not among the CertificateVerify-downstream
    // control states, so the invariant holds vacuously.
    ()
  | LocalInstallTrafficKeys _, ControlHandshaking _
  | LocalInstallTrafficKeysForRole _, ControlHandshaking _ ->
    // These arms leave model_control and hs_certificate_verify unchanged.
    assert (model'.model_control == model.model_control);
    assert (model'.model_handshake.hs_certificate_verify ==
            model.model_handshake.hs_certificate_verify);
    assert (model'.model_config == model.model_config)
  | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
    // Sets hs_certificate_verify = Some cv directly.
    assert (Some? model'.model_handshake.hs_certificate_verify)
  | LocalVerifyFinished _, ControlHandshaking HsServerFinishedReceived ->
    // hs_certificate_verify is untouched; model.model_control is already
    // downstream, so the per-step hypothesis already gives the witness.
    assert (model'.model_handshake.hs_certificate_verify ==
            model.model_handshake.hs_certificate_verify);
    assert (model'.model_config == model.model_config)
  | LocalVerifyClientFinished _, ControlHandshaking HsClientFinishedReceived ->
    // legal_local_event forces config_role == ServerEndpoint here, which
    // contradicts the ClientEndpoint antecedent of the invariant, so the
    // implication holds vacuously for a client-configured model.
    assert (model.model_config.config_role == ServerEndpoint);
    assert (model'.model_config == model.model_config)
  | LocalDeliverApplicationData _, ControlApplicationData ->
    assert (model'.model_control == model.model_control);
    assert (model'.model_handshake.hs_certificate_verify ==
            model.model_handshake.hs_certificate_verify);
    assert (model'.model_config == model.model_config)
  | _, _ ->
    assert False

let lemma_step_tls_message_client_certificate_verify_reachability
  (model:connection_model)
  (dir:direction)
  (msg:M.tls_message)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_reachability_invariant model /\
        legal_tls_message model dir msg /\
        step_tls_message model dir msg == Some model')
      (ensures client_certificate_verify_reachability_invariant model')
=
  match msg, model.model_control with
  | M.TlsHandshake handshake_msg, _ ->
    lemma_step_handshake_message_client_certificate_verify_reachability
      model
      dir
      handshake_msg
      model'
  | M.TlsKeyUpdate _, ControlApplicationData
  | M.TlsApplicationData _, ControlApplicationData
  | M.TlsIgnoredPostHandshake _, ControlApplicationData
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    assert (model'.model_control == model.model_control);
    assert (model'.model_handshake.hs_certificate_verify ==
            model.model_handshake.hs_certificate_verify);
    assert (model'.model_config == model.model_config)
  | M.TlsAlert _, _ ->
    // These arms move model_control to ControlFailed/ControlClosing/
    // ControlClosed, none of which are CertificateVerify-downstream,
    // regardless of which underlying step_tls_message arm actually fires.
    ()
  | _, _ ->
    assert False

let lemma_step_model_client_certificate_verify_reachability
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_reachability_invariant model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures client_certificate_verify_reachability_invariant model')
=
  match ev with
  | ConnLocalEvent local ->
    lemma_step_local_event_client_certificate_verify_reachability model local model'
  | ConnNetworkEvent msg ->
    lemma_step_tls_message_client_certificate_verify_reachability
      model
      msg.CL.message_direction
      msg.CL.message_value
      model'

let lemma_connection_delta_client_certificate_verify_reachability
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        client_certificate_verify_reachability_invariant st0.cs_model /\
        connection_state_single_step st0 st1)
      (ensures client_certificate_verify_reachability_invariant st1.cs_model)
=
  assert (exists delta. legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      connection_delta
      (fun delta -> legal_connection_delta st0 delta st1) in
  let delta : connection_delta = delta_w in
  assert (legal_connection_delta st0 delta st1);
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_client_certificate_verify_reachability
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_initial_client_certificate_verify_reachability
  (cfg:connection_config)
  : Lemma
      (ensures client_certificate_verify_reachability_invariant (initial cfg).cs_model)
=
  ()

let lemma_connection_state_single_step_client_certificate_verify_reachability
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (client_certificate_verify_reachability_invariant y.cs_model);
            (connection_state_single_step x y)}
          client_certificate_verify_reachability_invariant x.cs_model /\
          connection_state_single_step x y ==>
          client_certificate_verify_reachability_invariant y.cs_model)
=
  introduce forall x y.
    client_certificate_verify_reachability_invariant x.cs_model /\
    connection_state_single_step x y ==>
    client_certificate_verify_reachability_invariant y.cs_model
  with
    introduce _ ==> _ with
    lemma_connection_delta_client_certificate_verify_reachability x y

let lemma_connection_state_consistent_client_certificate_verify_reachability st =
  let p (st:connection_state) : prop =
    client_certificate_verify_reachability_invariant st.cs_model in
  lemma_initial_client_certificate_verify_reachability st.cs_model.model_config;
  lemma_connection_state_single_step_client_certificate_verify_reachability ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_client_application_ready_certificate_verify_witness st =
  lemma_connection_state_consistent_client_certificate_verify_reachability st

#pop-options
