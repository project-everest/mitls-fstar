module TLS13.Impl.Driver.PairingNoTailInversion

#lang-pulse

open Pulse.Lib.Pervasives

module CL = TLS13.ConnectionLog
module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module M = TLS13.Messages
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types

let lemma_list_length_pos_cons #a (l:list a) (n:nat)
  : Lemma
      (requires FStar.List.Tot.length l == n + 1)
      (ensures exists hd tl. l == hd :: tl /\ FStar.List.Tot.length tl == n)
=
  match l with
  | [] ->
    assert False
  | hd :: tl ->
    assert (FStar.List.Tot.length l == FStar.List.Tot.length tl + 1);
    assert (FStar.List.Tot.length tl == n)

let rec lemma_conn_events_raw_replay_from_failed_results_failed
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.ControlFailed? model.CS.model_control /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures CS.ControlFailed? final_model.CS.model_control)
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      CS.ControlFailed? final_model.CS.model_control
    with _.
    (
      CSL.lemma_step_model_from_failed_results_failed model ev model1;
      lemma_conn_events_raw_replay_from_failed_results_failed
        model1
        rest
        tail_sent
        tail_received
        final_model
    )

let lemma_control_new_non_alert_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlNew /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnNetworkEvent msg) == None)
=
  match model.CS.model_control with
  | CS.ControlNew ->
    (match msg.CL.message_value with
    | M.TlsAlert _ ->
      assert False
    | M.TlsHandshake hs ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
      | CL.Received ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
    | M.TlsApplicationData _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsChangeCipherSpec ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsIgnoredPostHandshake _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsKeyUpdate _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
  | _ ->
    assert False

let lemma_client_hs_started_non_client_hello_sent_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsStarted /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | M.TlsChangeCipherSpec -> False
         | M.TlsHandshake (M.ClientHello _) -> msg.CL.message_direction == CL.Received
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnNetworkEvent msg) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsStarted ->
    (match msg.CL.message_value with
    | M.TlsAlert _ ->
      assert False
    | M.TlsChangeCipherSpec ->
      assert False
    | M.TlsHandshake hs ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        (match hs with
        | M.ClientHello _ ->
          assert False
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
      | CL.Received ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
    | M.TlsApplicationData _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsIgnoredPostHandshake _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsKeyUpdate _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
  | _ ->
    assert False

let lemma_client_hs_started_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsStarted /\
        (match local with
         | CS.LocalFail _ -> False
         | CS.LocalInstallTrafficKeys _ -> False
         | CS.LocalInstallTrafficKeysForRole _ -> False
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnLocalEvent local) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsStarted ->
    (match local with
    | CS.LocalFail _ -> assert False
    | CS.LocalInstallTrafficKeys _ -> assert False
    | CS.LocalInstallTrafficKeysForRole _ -> assert False
    | CS.LocalStartHandshake _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalStartServer ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalSelectServerParameters _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalDeriveSharedSecret _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalValidateCertificate _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyCertificateSignature _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalSignCertificateVerify _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyFinished _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyClientFinished _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalDeliverApplicationData _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None))
  | _ ->
    assert False

let lemma_client_hs_started_install_traffic_keys_illegal
  (model:CS.connection_model)
  (install:CS.traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsStarted /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures False)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsStarted ->
    (match install.CS.install_epoch with
     | CS.TrafficHandshake -> ()
     | CS.TrafficApplication -> ())
  | _ -> ()

let lemma_client_hs_started_install_traffic_keys_for_role_illegal
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsStarted /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)))
      (ensures False)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsStarted ->
    (match role_install.CS.install_role with
     | CS.ClientEndpoint ->
       (match role_install.CS.install_payload.CS.install_epoch with
        | CS.TrafficHandshake -> ()
        | CS.TrafficApplication -> ())
     | CS.ServerEndpoint ->
       (match role_install.CS.install_payload.CS.install_epoch with
        | CS.TrafficHandshake -> ()
        | CS.TrafficApplication ->
          (match role_install.CS.install_payload.CS.install_direction with
           | CS.TrafficWrite -> ()
           | CS.TrafficRead -> ())))
  | _ -> ()

let lemma_client_hs_client_hello_sent_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
     (requires
       model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent /\
       (match local with
        | CS.LocalFail _ -> False
        | CS.LocalInstallTrafficKeys _ -> False
        | CS.LocalInstallTrafficKeysForRole _ -> False
        | _ -> True))
     (ensures
       CS.step_model model (CS.ConnLocalEvent local) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloSent ->
   (match local with
   | CS.LocalFail _ -> assert False
   | CS.LocalInstallTrafficKeys _ -> assert False
   | CS.LocalInstallTrafficKeysForRole _ -> assert False
   | CS.LocalStartHandshake _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalStartServer ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalSelectServerParameters _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalDeriveSharedSecret _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalValidateCertificate _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalVerifyCertificateSignature _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalSignCertificateVerify _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalVerifyFinished _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalVerifyClientFinished _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
   | CS.LocalDeliverApplicationData _ ->
     assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None))
  | _ ->
   assert False

let lemma_client_hs_client_hello_sent_install_traffic_keys_illegal
  (model:CS.connection_model)
  (install:CS.traffic_key_install)
  : Lemma
     (requires
       model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent /\
       CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
     (ensures False)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloSent ->
   (match install.CS.install_epoch with
    | CS.TrafficHandshake -> ()
    | CS.TrafficApplication -> ())
  | _ -> ()

let lemma_client_hs_client_hello_sent_install_traffic_keys_for_role_illegal
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  : Lemma
     (requires
       model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent /\
       CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)))
     (ensures False)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloSent ->
   (match role_install.CS.install_role with
    | CS.ClientEndpoint ->
      (match role_install.CS.install_payload.CS.install_epoch with
       | CS.TrafficHandshake -> ()
       | CS.TrafficApplication -> ())
    | CS.ServerEndpoint ->
      (match role_install.CS.install_payload.CS.install_epoch with
       | CS.TrafficHandshake -> ()
       | CS.TrafficApplication ->
         (match role_install.CS.install_payload.CS.install_direction with
          | CS.TrafficWrite -> ()
          | CS.TrafficRead -> ())))
  | _ -> ()

let lemma_client_hs_client_hello_sent_non_server_hello_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
     (requires
       model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent /\
       (match msg.CL.message_value with
        | M.TlsAlert _ -> False
        | M.TlsChangeCipherSpec -> False
        | M.TlsHandshake (M.ServerHello _) ->
          msg.CL.message_direction == CL.Sent
        | M.TlsHandshake M.HelloRetryRequest ->
          msg.CL.message_direction == CL.Sent
        | _ -> True))
     (ensures
       CS.step_model model (CS.ConnNetworkEvent msg) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloSent ->
   (match msg.CL.message_value with
    | M.TlsAlert _ ->
      assert False
    | M.TlsChangeCipherSpec ->
      assert False
    | M.TlsHandshake hs ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
      | CL.Received ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert False
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert False))
    | M.TlsApplicationData _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsIgnoredPostHandshake _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsKeyUpdate _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
  | _ ->
   assert False

let lemma_client_hs_server_hello_received_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (match local with
         | CS.LocalFail _ -> False
         | CS.LocalDeriveSharedSecret _ -> False
         | CS.LocalInstallTrafficKeys _ -> False
         | CS.LocalInstallTrafficKeysForRole _ -> False
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnLocalEvent local) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    (match local with
    | CS.LocalFail _ -> assert False
    | CS.LocalDeriveSharedSecret _ -> assert False
    | CS.LocalInstallTrafficKeys _ -> assert False
    | CS.LocalInstallTrafficKeysForRole _ -> assert False
    | CS.LocalStartHandshake _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalStartServer ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalSelectServerParameters _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalValidateCertificate _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyCertificateSignature _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalSignCertificateVerify _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyFinished _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyClientFinished _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalDeliverApplicationData _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None))
  | _ ->
    assert False

let lemma_client_hs_server_hello_received_empty_keys_install_traffic_keys_illegal
  (model:CS.connection_model)
  (install:CS.traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures False)
=
  assert (CS.legal_local_event model (CS.LocalInstallTrafficKeys install));
  let hs = model.CS.model_handshake in
  assert (CS.traffic_install_allowed_at_stage CS.HsServerHelloReceived install);
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    (match install.CS.install_epoch, install.CS.install_direction with
     | CS.TrafficHandshake, CS.TrafficWrite ->
       assert (CS.traffic_install_matches_key_schedule hs install);
       assert (install.CS.install_epoch == CS.TrafficHandshake);
       assert (install.CS.install_direction == CS.TrafficWrite);
       (match hs.CS.hs_keys.CS.ks_handshake_secret with
        | None ->
          assert_norm
            (CS.traffic_label_for_endpoint_direction
              CS.ClientEndpoint
              CS.TrafficWrite == CS.ClientTraffic);
          assert_norm
            (CS.expected_traffic_secret
              hs
              CS.TrafficHandshake
              CS.TrafficWrite == None);
          assert_norm
            (CS.traffic_install_matches_key_schedule hs install == False);
          assert False
        | Some _ ->
          assert False)
     | CS.TrafficHandshake, CS.TrafficRead ->
       assert (CS.traffic_install_matches_key_schedule hs install);
       assert (install.CS.install_epoch == CS.TrafficHandshake);
       assert (install.CS.install_direction == CS.TrafficRead);
       (match hs.CS.hs_keys.CS.ks_handshake_secret with
        | None ->
          assert_norm
            (CS.traffic_label_for_endpoint_direction
              CS.ClientEndpoint
              CS.TrafficRead == CS.ServerTraffic);
          assert_norm
            (CS.expected_traffic_secret
              hs
              CS.TrafficHandshake
              CS.TrafficRead == None);
          assert_norm
            (CS.traffic_install_matches_key_schedule hs install == False);
          assert False
        | Some _ ->
          assert False)
     | CS.TrafficApplication, CS.TrafficWrite ->
       assert (install.CS.install_epoch == CS.TrafficApplication);
       assert_norm
         (CS.traffic_install_allowed_at_stage
           CS.HsServerHelloReceived
           install == False);
       assert False
     | CS.TrafficApplication, CS.TrafficRead ->
       assert (install.CS.install_epoch == CS.TrafficApplication);
       assert_norm
         (CS.traffic_install_allowed_at_stage
           CS.HsServerHelloReceived
           install == False);
       assert False)
  | _ ->
    assert False

let lemma_client_hs_server_hello_received_empty_keys_install_traffic_keys_for_role_illegal
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)))
      (ensures False)
=
  let install = role_install.CS.install_payload in
  assert (CS.legal_local_event model (CS.LocalInstallTrafficKeysForRole role_install));
  assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
  assert (role_install.CS.install_role == CS.ClientEndpoint);
  let hs = model.CS.model_handshake in
  match model.CS.model_control, role_install.CS.install_role with
  | CS.ControlHandshaking CS.HsServerHelloReceived, CS.ClientEndpoint ->
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ClientEndpoint
      CS.HsServerHelloReceived
      install);
    (match install.CS.install_epoch, install.CS.install_direction with
     | CS.TrafficHandshake, CS.TrafficWrite ->
       assert (CS.traffic_install_matches_key_schedule_for_role
         CS.ClientEndpoint
         hs
         install);
       assert (install.CS.install_epoch == CS.TrafficHandshake);
       assert (install.CS.install_direction == CS.TrafficWrite);
       (match hs.CS.hs_keys.CS.ks_handshake_secret with
        | None ->
          assert_norm
            (CS.traffic_label_for_endpoint_direction
              CS.ClientEndpoint
              CS.TrafficWrite == CS.ClientTraffic);
          assert_norm
            (CS.expected_traffic_secret_for_role
              CS.ClientEndpoint
              hs
              CS.TrafficHandshake
              CS.TrafficWrite == None);
          assert_norm
            (CS.traffic_install_matches_key_schedule_for_role
              CS.ClientEndpoint
              hs
              install == False);
          assert False
        | Some _ ->
          assert False)
     | CS.TrafficHandshake, CS.TrafficRead ->
       assert (CS.traffic_install_matches_key_schedule_for_role
         CS.ClientEndpoint
         hs
         install);
       assert (install.CS.install_epoch == CS.TrafficHandshake);
       assert (install.CS.install_direction == CS.TrafficRead);
       (match hs.CS.hs_keys.CS.ks_handshake_secret with
        | None ->
          assert_norm
            (CS.traffic_label_for_endpoint_direction
              CS.ClientEndpoint
              CS.TrafficRead == CS.ServerTraffic);
          assert_norm
            (CS.expected_traffic_secret_for_role
              CS.ClientEndpoint
              hs
              CS.TrafficHandshake
              CS.TrafficRead == None);
          assert_norm
            (CS.traffic_install_matches_key_schedule_for_role
              CS.ClientEndpoint
              hs
              install == False);
          assert False
        | Some _ ->
          assert False)
     | CS.TrafficApplication, CS.TrafficWrite ->
       assert (install.CS.install_epoch == CS.TrafficApplication);
       assert_norm
         (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsServerHelloReceived
           install == False);
       assert False
     | CS.TrafficApplication, CS.TrafficRead ->
       assert (install.CS.install_epoch == CS.TrafficApplication);
       assert_norm
         (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsServerHelloReceived
           install == False);
       assert False)
  | _, _ ->
    assert False

let lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | M.TlsChangeCipherSpec -> False
         | M.TlsHandshake (M.EncryptedExtensions _) ->
           msg.CL.message_direction == CL.Sent
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnNetworkEvent msg) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    (match msg.CL.message_value with
     | M.TlsAlert _ ->
       assert False
     | M.TlsChangeCipherSpec ->
       assert False
     | M.TlsHandshake hs ->
       (match msg.CL.message_direction with
       | CL.Sent ->
         (match hs with
         | M.ClientHello _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.ServerHello _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.EncryptedExtensions _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.Certificate _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.CertificateVerify _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.Finished _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.HelloRetryRequest ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
       | CL.Received ->
         (match hs with
         | M.ClientHello _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.ServerHello _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.EncryptedExtensions _ ->
           assert False
         | M.Certificate _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.CertificateVerify _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.Finished _ ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
         | M.HelloRetryRequest ->
           assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
     | M.TlsApplicationData _ ->
       (match msg.CL.message_direction with
       | CL.Sent ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
       | CL.Received ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
     | M.TlsIgnoredPostHandshake _ ->
       (match msg.CL.message_direction with
       | CL.Sent ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
       | CL.Received ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
     | M.TlsKeyUpdate _ ->
       (match msg.CL.message_direction with
       | CL.Sent ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
       | CL.Received ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
  | _ ->
    assert False

let lemma_client_hs_server_hello_received_empty_keys_encrypted_extensions_illegal
  (model:CS.connection_model)
  (ee:GEE.encryptedExtensions)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        CS.legal_event
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          })))
      (ensures False)
=
  assert (CS.legal_tls_message
    model
    CL.Received
    (M.TlsHandshake (M.EncryptedExtensions ee)));
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    (match model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
     | None ->
       assert_norm (
         CS.legal_event
           model
           (CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
           })) ==
         (model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
          Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
       assert False
     | Some _ ->
       assert False)
  | _ ->
    assert False

let lemma_client_hs_client_hello_sent_empty_keys_progress_rank
  (model:CS.connection_model)
  : Lemma
     (requires
       model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent /\
       model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
       model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
       model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
       model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
       model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
     (ensures client_application_progress_rank model == 12)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloSent ->
   (match
     keys.CS.ks_shared_secret,
     keys.CS.ks_client_handshake_traffic,
     keys.CS.ks_server_handshake_traffic,
     keys.CS.ks_client_application_traffic,
     keys.CS.ks_server_application_traffic
   with
   | None, None, None, None, None ->
     assert (option_missing keys.CS.ks_shared_secret == 1);
     assert (option_missing keys.CS.ks_client_handshake_traffic == 1);
     assert (option_missing keys.CS.ks_server_handshake_traffic == 1);
     assert (client_app_obligation_rank keys == 1);
     assert (client_early_obligation_rank keys == 4);
     assert (client_application_progress_rank model == 12)
   | _, _, _, _, _ ->
     assert False)
  | _ ->
   assert False

let lemma_client_hs_server_hello_received_empty_keys_progress_rank
  (model:CS.connection_model)
  : Lemma
    (requires
      model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
    (ensures client_application_progress_rank model == 11)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
   (match
    keys.CS.ks_shared_secret,
    keys.CS.ks_client_handshake_traffic,
    keys.CS.ks_server_handshake_traffic,
    keys.CS.ks_client_application_traffic,
    keys.CS.ks_server_application_traffic
   with
   | None, None, None, None, None ->
    assert (option_missing keys.CS.ks_shared_secret == 1);
    assert (option_missing keys.CS.ks_client_handshake_traffic == 1);
    assert (option_missing keys.CS.ks_server_handshake_traffic == 1);
    assert (client_app_obligation_rank keys == 1);
    assert (client_early_obligation_rank keys == 4);
    assert (client_application_progress_rank model == 11)
   | _, _, _, _, _ ->
    assert False)
  | _ ->
   assert False

let lemma_client_hs_server_hello_received_derived_no_traffic_progress_rank
  (model:CS.connection_model)
  : Lemma
    (requires
      model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
      Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
      model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
    (ensures client_application_progress_rank model == 10)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    (match
      keys.CS.ks_shared_secret,
      keys.CS.ks_client_handshake_traffic,
      keys.CS.ks_server_handshake_traffic,
      keys.CS.ks_client_application_traffic,
      keys.CS.ks_server_application_traffic
    with
    | Some _, None, None, None, None ->
      assert (option_missing keys.CS.ks_shared_secret == 0);
      assert (option_missing keys.CS.ks_client_handshake_traffic == 1);
      assert (option_missing keys.CS.ks_server_handshake_traffic == 1);
      assert (client_app_obligation_rank keys == 1);
      assert (client_early_obligation_rank keys == 3);
      assert (client_application_progress_rank model == 10)
    | _, _, _, _, _ ->
      assert False)
  | _ ->
    assert False

let lemma_client_application_ready_progress_rank_zero
  (client:CS.connection_state)
  : Lemma
    (requires CD.client_driver_application_ready client)
     (ensures client_application_progress_rank client.CS.cs_model == 0)
=
  let keys = client.CS.cs_model.CS.model_handshake.CS.hs_keys in
  CSL.lemma_client_application_ready_stable_x25519_key_share_projection client;
  assert (TLS13.Spec.StateMachine.Correspondence.stable_client_x25519_key_share_projection client);
  assert (TLS13.Spec.StateMachine.Correspondence.client_x25519_key_share_projection client);
  assert (CS.application_record_keys_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ClientEndpoint
      CS.TrafficWrite == CS.ClientTraffic);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ClientEndpoint
      CS.TrafficRead == CS.ServerTraffic);
  match
    keys.CS.ks_shared_secret,
    keys.CS.ks_client_application_traffic,
    keys.CS.ks_server_application_traffic
  with
  | Some _, Some _, Some _ ->
    ()
  | _, _, _ ->
    assert False

let lemma_client_progress_rank_local_install
  (model:CS.connection_model)
  (install:CS.traffic_key_install)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)) /\
        CS.step_model model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)) == Some model')
      (ensures
        client_application_progress_rank model <=
        client_application_progress_rank model' + 1)
=
  assert (CS.legal_local_event model (CS.LocalInstallTrafficKeys install));
  assert (CS.step_local_event model (CS.LocalInstallTrafficKeys install) == Some model');
  match model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (CS.traffic_install_allowed_at_stage stage install);
    (match stage, install.CS.install_epoch, install.CS.install_direction with
     | CS.HsServerHelloReceived, CS.TrafficHandshake, CS.TrafficWrite ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficWrite == CS.ClientTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | CS.HsServerHelloReceived, CS.TrafficHandshake, CS.TrafficRead ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficRead == CS.ServerTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | CS.HsServerFinishedVerified, CS.TrafficApplication, CS.TrafficWrite ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficWrite == CS.ClientTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | CS.HsServerFinishedVerified, CS.TrafficApplication, CS.TrafficRead ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficRead == CS.ServerTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | _, _, _ ->
       assert False)
  | _ ->
    assert False

let lemma_client_progress_rank_role_install
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) /\
        CS.step_model model (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) == Some model')
      (ensures
        client_application_progress_rank model <=
        client_application_progress_rank model' + 1)
=
  let install = role_install.CS.install_payload in
  assert (CS.legal_local_event model (CS.LocalInstallTrafficKeysForRole role_install));
  assert (role_install.CS.install_role == CS.ClientEndpoint);
  assert (CS.step_local_event model (CS.LocalInstallTrafficKeysForRole role_install) == Some model');
  match model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (CS.traffic_install_allowed_at_stage_for_role
      role_install.CS.install_role
      stage
      install);
    assert (CS.traffic_install_allowed_at_stage stage install);
    (match stage, install.CS.install_epoch, install.CS.install_direction with
     | CS.HsServerHelloReceived, CS.TrafficHandshake, CS.TrafficWrite ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficWrite == CS.ClientTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | CS.HsServerHelloReceived, CS.TrafficHandshake, CS.TrafficRead ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficRead == CS.ServerTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | CS.HsServerFinishedVerified, CS.TrafficApplication, CS.TrafficWrite ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficWrite == CS.ClientTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | CS.HsServerFinishedVerified, CS.TrafficApplication, CS.TrafficRead ->
       assert_norm
         (CS.traffic_label_for_endpoint_direction
           CS.ClientEndpoint
           CS.TrafficRead == CS.ServerTraffic);
       assert (client_application_progress_rank model <=
         client_application_progress_rank model' + 1)
     | _, _, _ ->
       assert False)
  | _ ->
    assert False

let lemma_client_application_progress_rank_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        CS.ControlFailed? model'.CS.model_control \/
        client_application_progress_rank model <=
        client_application_progress_rank model' + 1)
=
  CSL.lemma_step_model_preserves_config model ev model';
  match model'.CS.model_control with
  | CS.ControlFailed _ ->
    ()
  | _ ->
    (match ev with
     | CS.ConnLocalEvent local ->
       assert (CS.legal_local_event model local);
       assert (CS.step_local_event model local == Some model');
       (match local with
        | CS.LocalInstallTrafficKeys install ->
          lemma_client_progress_rank_local_install model install model'
        | CS.LocalInstallTrafficKeysForRole role_install ->
          lemma_client_progress_rank_role_install model role_install model'
        | CS.LocalFail _ ->
          assert False
        | _ ->
          (match model.CS.model_control, local with
           | CS.ControlNew, CS.LocalStartHandshake _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsServerHelloReceived, CS.LocalDeriveSharedSecret _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsCertificateReceived, CS.LocalValidateCertificate _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsCertificateVerifyReceived, CS.LocalVerifyCertificateSignature _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsServerFinishedReceived, CS.LocalVerifyFinished _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlApplicationData, CS.LocalDeliverApplicationData _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | _, _ ->
             assert (CS.step_local_event model local == None);
             assert False))
     | CS.ConnProtectedHandshake step ->
       assert (CS.legal_protected_handshake_step model step);
       assert (CS.step_protected_handshake model step == Some model');
       if step.CS.protected_handshake_buffering
       then
         (* A BUFFERING step sets a record's plaintext aside so a handshake
            message spanning several records can be reassembled.  It delivers
            no message (its [protected_handshake_message] is inert, so the
            control/message dispatch below does not apply to it) and it moves
            only the pending buffer and the record read state.  The control
            and the key schedule -- the only things the rank reads -- are
            untouched, so the rank is unchanged and the bound holds with
            room to spare. *)
         begin
           assert (CS.step_protected_handshake_buffer model step == model');
           assert (model'.CS.model_control == model.CS.model_control);
           assert (model'.CS.model_handshake.CS.hs_keys ==
                     model.CS.model_handshake.CS.hs_keys);
           assert (client_application_progress_rank model ==
             client_application_progress_rank model')
         end
       else
       (match model.CS.model_control, step.CS.protected_handshake_message with
        | CS.ControlHandshaking CS.HsServerHelloReceived,
          M.EncryptedExtensions _ ->
          let keys = model.CS.model_handshake.CS.hs_keys in
          (match keys.CS.ks_server_handshake_traffic with
           | Some _ ->
             assert (client_application_progress_rank model <=
              client_application_progress_rank model' + 1)
           | None ->
             assert False)
        | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived,
          M.Certificate _ ->
          assert (client_application_progress_rank model <=
            client_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsCertificateValidated,
          M.CertificateVerify _ ->
          assert (client_application_progress_rank model <=
            client_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsCertificateVerifyVerified,
          M.Finished _ ->
          assert (client_application_progress_rank model <=
            client_application_progress_rank model' + 1)
        | _, _ ->
          assert False)
     | CS.ConnNetworkEvent msg ->
       assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
       assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == Some model');
       (match msg.CL.message_value with
        | M.TlsAlert alert ->
          (match alert, model.CS.model_control, msg.CL.message_direction with
           | T.Close_notify, CS.ControlApplicationData, CL.Sent ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | T.Close_notify, CS.ControlApplicationData, CL.Received ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | T.Close_notify, CS.ControlClosing, CL.Received ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | _, _, _ ->
             assert False)
        | M.TlsChangeCipherSpec ->
          assert (model' == model);
          assert (client_application_progress_rank model <=
            client_application_progress_rank model' + 1)
        | M.TlsHandshake hs ->
          (match model.CS.model_control, msg.CL.message_direction, hs with
           | CS.ControlHandshaking CS.HsStarted, CL.Sent, M.ClientHello _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsClientHelloSent, CL.Received, M.ServerHello _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsServerHelloReceived, CL.Received, M.EncryptedExtensions _ ->
             let keys = model.CS.model_handshake.CS.hs_keys in
             (match keys.CS.ks_server_handshake_traffic with
             | Some _ ->
               assert (client_application_progress_rank model <=
                 client_application_progress_rank model' + 1)
             | None ->
               assert False)
           | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived, CL.Received, M.Certificate _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsCertificateValidated, CL.Received, M.CertificateVerify _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsCertificateVerifyVerified, CL.Received, M.Finished _ ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | CS.ControlHandshaking CS.HsServerFinishedVerified, CL.Sent, M.Finished _ ->
             let keys = model.CS.model_handshake.CS.hs_keys in
             (match keys.CS.ks_client_handshake_traffic with
             | Some _ ->
               assert (client_application_progress_rank model <=
                 client_application_progress_rank model' + 1)
             | None ->
               assert False)
           | CS.ControlHandshaking CS.HsClientHelloSent, CL.Received, M.HelloRetryRequest ->
             assert False
           | _, _, _ ->
             assert (CS.step_handshake_message model msg.CL.message_direction hs == None);
             assert False)
        | M.TlsApplicationData _ ->
          (match model.CS.model_control with
           | CS.ControlApplicationData ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | _ ->
             assert False)
        | M.TlsIgnoredPostHandshake _ ->
          (match model.CS.model_control, msg.CL.message_direction with
           | CS.ControlApplicationData, CL.Received ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | _, _ ->
             assert False)
        | M.TlsKeyUpdate _ ->
          (* Both directions and both request forms are now legal in
             [ControlApplicationData] (a client may spontaneously send
             [update_requested]), so the arms collapse to one. *)
          (match model.CS.model_control with
           | CS.ControlApplicationData ->
             assert (client_application_progress_rank model <=
               client_application_progress_rank model' + 1)
           | _ ->
             assert False)))

let rec lemma_client_application_progress_rank_replay_lower_bound
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model events raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        client_application_progress_rank final_model == 0)
      (ensures
        client_application_progress_rank model <= FStar.List.Tot.length events)
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      client_application_progress_rank model <= FStar.List.Tot.length (ev :: rest)
    with _.
    (
      lemma_client_application_progress_rank_step model ev model1;
      match model1.CS.model_control with
      | CS.ControlFailed _ ->
        lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model;
        assert (CS.ControlFailed? final_model.CS.model_control);
        assert (final_model.CS.model_control == CS.ControlApplicationData);
        assert (client_application_progress_rank final_model == 0);
        assert False
      | _ ->
        CSL.lemma_step_model_preserves_config model ev model1;
        assert (model1.CS.model_config == model.CS.model_config);
        lemma_client_application_progress_rank_replay_lower_bound
          model1
          rest
          tail_sent
          tail_received
          final_model;
        assert (client_application_progress_rank model <=
          client_application_progress_rank model1 + 1);
        assert (client_application_progress_rank model1 <= FStar.List.Tot.length rest);
        assert (FStar.List.Tot.length (ev :: rest) == FStar.List.Tot.length rest + 1)
    )
