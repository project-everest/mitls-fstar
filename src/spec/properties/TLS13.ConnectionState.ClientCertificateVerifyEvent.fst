module TLS13.ConnectionState.ClientCertificateVerifyEvent

module CL = TLS13.ConnectionLog
module CVR = TLS13.ConnectionState.ClientCertificateVerifyReachability
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module GCV = TLS13.Wire.Generated.CertificateVerify
module RTC = FStar.ReflexiveTransitiveClosure
module T = TLS13.Types

open FStar.List.Tot
open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay

#push-options "--split_queries always --z3rlimit 10"

noextract
let rec contains_received_certificate_verify
  (events:list conn_event)
  : Tot prop
    (decreases events)
=
  match events with
  | [] -> False
  | ev :: rest ->
    (match ev with
     | ConnNetworkEvent msg ->
       msg.CL.message_direction == CL.Received /\
       (match msg.CL.message_value with
        | M.TlsHandshake (M.CertificateVerify _) -> True
        | _ -> False)
     | _ -> False) \/
    contains_received_certificate_verify rest

let rec lemma_contains_received_certificate_verify_append_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (requires contains_received_certificate_verify events)
      (ensures contains_received_certificate_verify (events @ [ev]))
      (decreases events)
=
  match events with
  | [] -> assert False
  | hd :: rest ->
    if contains_received_certificate_verify rest then
      lemma_contains_received_certificate_verify_append_snoc rest ev
    else
      ()

let rec lemma_contains_received_certificate_verify_snoc_intro
  (events:list conn_event)
  (cv:GCV.certificateVerify)
  : Lemma
      (ensures
        contains_received_certificate_verify
          (events @ [ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          }]))
      (decreases events)
=
  match events with
  | [] -> ()
  | _ :: rest ->
    lemma_contains_received_certificate_verify_snoc_intro rest cv

let rec lemma_contains_received_certificate_verify_split
  (events:list conn_event)
  : Lemma
      (requires contains_received_certificate_verify events)
      (ensures
        exists prefix cv suffix.
          events ==
            prefix @
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            } :: suffix))
      (decreases events)
=
  match events with
  | [] ->
    assert False
  | ev :: rest ->
    (match ev with
     | ConnNetworkEvent msg ->
       (match msg.CL.message_direction, msg.CL.message_value with
        | CL.Received, M.TlsHandshake (M.CertificateVerify cv) ->
          introduce exists (prefix:list conn_event)
            (cv':GCV.certificateVerify)
            (suffix:list conn_event).
            events ==
              prefix @
              (ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              } :: suffix)
          with [] cv rest and ()
        | _, _ ->
          assert (contains_received_certificate_verify rest);
          lemma_contains_received_certificate_verify_split rest;
          eliminate exists prefix cv suffix.
            rest ==
              prefix @
              (ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              } :: suffix)
          returns
            exists prefix' cv' suffix'.
              events ==
                prefix' @
                (ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
                } :: suffix')
          with _.
          (
            introduce exists (prefix':list conn_event)
              (cv':GCV.certificateVerify)
              (suffix':list conn_event).
              events ==
                prefix' @
                (ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
                } :: suffix')
            with (ev :: prefix) cv suffix and ()
          ))
     | _ ->
       assert (contains_received_certificate_verify rest);
       lemma_contains_received_certificate_verify_split rest;
       eliminate exists prefix cv suffix.
         rest ==
           prefix @
           (ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
           } :: suffix)
       returns
         exists prefix' cv' suffix'.
           events ==
             prefix' @
             (ConnNetworkEvent {
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
             } :: suffix')
       with _.
       (
         introduce exists (prefix':list conn_event)
           (cv':GCV.certificateVerify)
           (suffix':list conn_event).
           events ==
             prefix' @
             (ConnNetworkEvent {
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
             } :: suffix')
         with (ev :: prefix) cv suffix and ()
       ))

noextract
let client_certificate_verify_event_log_invariant_at
  (model:connection_model)
  (events:list conn_event)
  : prop =
  model.model_config.config_role == ClientEndpoint /\
  CVR.client_certificate_verify_downstream_control model.model_control ==>
  contains_received_certificate_verify events

noextract
let client_certificate_verify_event_log_invariant
  (st:connection_state)
  : prop =
  client_certificate_verify_event_log_invariant_at st.cs_model st.cs_event_log

let lemma_step_handshake_message_client_certificate_verify_event_log
  (model:connection_model)
  (events:list conn_event)
  (dir:direction)
  (msg:M.handshake_msg)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_event_log_invariant_at model events /\
        legal_handshake_message model dir msg /\
        step_handshake_message model dir msg == Some model')
      (ensures
        client_certificate_verify_event_log_invariant_at
          model'
          (events @ [ConnNetworkEvent {
            CL.message_direction = dir;
            CL.message_value = M.TlsHandshake msg;
          }]))
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
    ()
  | CL.Received, M.Finished _, ControlHandshaking HsServerFinishedSent ->
    // Fix 1 (atomic server delivery): now lands at ControlApplicationData (a
    // CertificateVerify-downstream state).  legal_handshake_message forces
    // config_role == ServerEndpoint, contradicting the ClientEndpoint antecedent
    // of the (client-local) invariant, so the implication holds vacuously.
    assert (model.model_config.config_role == ServerEndpoint);
    assert (model'.model_config == model.model_config)
  | CL.Received, M.CertificateVerify cv, ControlHandshaking HsCertificateValidated ->
    lemma_contains_received_certificate_verify_snoc_intro events cv
  | CL.Received, M.Finished _, ControlHandshaking HsCertificateVerifyVerified
  | CL.Sent, M.Finished _, ControlHandshaking HsServerFinishedVerified ->
    assert (CVR.client_certificate_verify_downstream_control model.model_control);
    if model.model_config.config_role == ClientEndpoint then (
      assert (contains_received_certificate_verify events);
      lemma_contains_received_certificate_verify_append_snoc
        events
        (ConnNetworkEvent {
          CL.message_direction = dir;
          CL.message_value = M.TlsHandshake msg;
        })
    )
  | _, _, _ ->
    assert False

let lemma_step_local_event_client_certificate_verify_event_log
  (model:connection_model)
  (events:list conn_event)
  (ev:local_event)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_event_log_invariant_at model events /\
        legal_local_event model ev /\
        step_local_event model ev == Some model')
      (ensures
        client_certificate_verify_event_log_invariant_at
          model'
          (events @ [ConnLocalEvent ev]))
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
    ()
  | LocalInstallTrafficKeys _, ControlHandshaking _
  | LocalInstallTrafficKeysForRole _, ControlHandshaking _ ->
    assert (model'.model_control == model.model_control);
    assert (model'.model_config == model.model_config);
    if model'.model_config.config_role == ClientEndpoint /\
       CVR.client_certificate_verify_downstream_control model'.model_control then (
      assert (CVR.client_certificate_verify_downstream_control model.model_control);
      assert (contains_received_certificate_verify events);
      lemma_contains_received_certificate_verify_append_snoc
        events
        (ConnLocalEvent ev)
    )
  | LocalVerifyCertificateSignature _, ControlHandshaking HsCertificateVerifyReceived
  | LocalVerifyFinished _, ControlHandshaking HsServerFinishedReceived
  | LocalDeliverApplicationData _, ControlApplicationData ->
    assert (CVR.client_certificate_verify_downstream_control model.model_control);
    if model.model_config.config_role == ClientEndpoint then (
      assert (contains_received_certificate_verify events);
      lemma_contains_received_certificate_verify_append_snoc
        events
        (ConnLocalEvent ev)
    )
  | LocalVerifyClientFinished _, ControlHandshaking HsClientFinishedReceived ->
    assert (model.model_config.config_role == ServerEndpoint)
  | _, _ ->
    assert False

let lemma_step_tls_message_client_certificate_verify_event_log
  (model:connection_model)
  (events:list conn_event)
  (dir:direction)
  (msg:M.tls_message)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_event_log_invariant_at model events /\
        legal_tls_message model dir msg /\
        step_tls_message model dir msg == Some model')
      (ensures
        client_certificate_verify_event_log_invariant_at
          model'
          (events @ [ConnNetworkEvent {
            CL.message_direction = dir;
            CL.message_value = msg;
          }]))
=
  match msg, model.model_control with
  | M.TlsHandshake handshake_msg, _ ->
    lemma_step_handshake_message_client_certificate_verify_event_log
      model
      events
      dir
      handshake_msg
      model'
  | M.TlsKeyUpdate _, ControlApplicationData
  | M.TlsApplicationData _, ControlApplicationData
  | M.TlsIgnoredPostHandshake _, ControlApplicationData
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    assert (model'.model_control == model.model_control);
    assert (model'.model_config == model.model_config);
    if model.model_config.config_role == ClientEndpoint /\
       CVR.client_certificate_verify_downstream_control model.model_control then (
      assert (contains_received_certificate_verify events);
      lemma_contains_received_certificate_verify_append_snoc
        events
        (ConnNetworkEvent {
          CL.message_direction = dir;
          CL.message_value = msg;
        })
    )
  | M.TlsAlert _, _ ->
    ()
  | _, _ ->
    assert False

let lemma_step_model_client_certificate_verify_event_log
  (model:connection_model)
  (events:list conn_event)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        client_certificate_verify_event_log_invariant_at model events /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures
        client_certificate_verify_event_log_invariant_at model' (events @ [ev]))
=
  match ev with
  | ConnLocalEvent local ->
    lemma_step_local_event_client_certificate_verify_event_log model events local model'
  | ConnNetworkEvent msg ->
    lemma_step_tls_message_client_certificate_verify_event_log
      model
      events
      msg.CL.message_direction
      msg.CL.message_value
      model'

let lemma_connection_delta_client_certificate_verify_event_log
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        client_certificate_verify_event_log_invariant st0 /\
        connection_state_single_step st0 st1)
      (ensures client_certificate_verify_event_log_invariant st1)
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
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  lemma_step_model_client_certificate_verify_event_log
    st0.cs_model
    st0.cs_event_log
    delta.delta_event
    st1.cs_model

let lemma_initial_client_certificate_verify_event_log
  (cfg:connection_config)
  : Lemma
      (ensures
        client_certificate_verify_event_log_invariant (initial cfg))
=
  ()

let lemma_connection_state_single_step_client_certificate_verify_event_log
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (client_certificate_verify_event_log_invariant y);
            (connection_state_single_step x y)}
          client_certificate_verify_event_log_invariant x /\
          connection_state_single_step x y ==>
          client_certificate_verify_event_log_invariant y)
=
  introduce forall x y.
    client_certificate_verify_event_log_invariant x /\
    connection_state_single_step x y ==>
    client_certificate_verify_event_log_invariant y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_client_certificate_verify_event_log x y

let lemma_connection_state_consistent_client_certificate_verify_event_log st =
  let p (st:connection_state) : prop =
    client_certificate_verify_event_log_invariant st in
  lemma_initial_client_certificate_verify_event_log st.cs_model.model_config;
  lemma_connection_state_single_step_client_certificate_verify_event_log ();
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

let lemma_client_application_ready_received_certificate_verify_event st =
  lemma_connection_state_consistent_client_certificate_verify_event_log st

#pop-options
