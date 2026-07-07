module TLS13.Impl.Driver.PairingNoTailServerCleartextShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module Seq = FStar.Seq
module SD = TLS13.Impl.Server.Driver
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types

let lemma_server_hs_client_hello_received_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_handshake.CS.hs_server_selection == None /\
        CS.legal_event model (CS.ConnLocalEvent local) /\
        (match local with
         | CS.LocalFail _ -> False
         | CS.LocalSelectServerParameters _ -> False
         | _ -> True))
      (ensures False)
=
  assert (CS.legal_local_event model local);
  match local with
  | CS.LocalFail _ ->
    assert False
  | CS.LocalSelectServerParameters _ ->
    assert False
  | CS.LocalStartHandshake _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalStartServer ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalInstallTrafficKeys install ->
    assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert (model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    assert False
  | CS.LocalInstallTrafficKeysForRole role_install ->
    let install = role_install.CS.install_payload in
    assert (CS.legal_local_event
      model
      (CS.LocalInstallTrafficKeysForRole role_install));
    assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ServerEndpoint
      CS.HsClientHelloReceived
      install);
    (match install.CS.install_epoch with
    | CS.TrafficHandshake ->
      assert (CS.HsClientHelloReceived == CS.HsServerHelloSent);
      assert False
    | CS.TrafficApplication ->
      (match install.CS.install_direction with
      | CS.TrafficWrite ->
        assert (CS.HsClientHelloReceived == CS.HsServerFinishedSent);
        assert False
      | CS.TrafficRead ->
        assert (CS.HsClientHelloReceived == CS.HsClientFinishedReceived);
        assert False))
  | CS.LocalDeriveSharedSecret shared ->
    assert (Some? model.CS.model_handshake.CS.hs_server_selection);
    assert (model.CS.model_handshake.CS.hs_server_selection == None);
    assert False
  | CS.LocalValidateCertificate _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyCertificateSignature _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalSignCertificateVerify _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyFinished _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyClientFinished _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalDeliverApplicationData _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False

let lemma_server_hs_client_hello_received_network_event_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
        CS.legal_event model (CS.ConnNetworkEvent msg) /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | M.TlsChangeCipherSpec -> False
         | _ -> True))
      (ensures False)
=
  assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
  match msg.CL.message_value with
  | M.TlsAlert _ ->
    assert False
  | M.TlsChangeCipherSpec ->
    assert False
  | M.TlsHandshake hs ->
    (match msg.CL.message_direction, hs with
    | CL.Sent, M.ServerHello sh ->
      assert (CS.legal_tls_message
        model
        CL.Sent
        (M.TlsHandshake (M.ServerHello sh)));
      assert (CS.legal_handshake_message
        model
        CL.Sent
        (M.ServerHello sh));
      assert (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
      assert (model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
      assert False
    | _, _ ->
      assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
      assert False)
  | M.TlsApplicationData _ ->
    assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
    assert False
  | M.TlsIgnoredPostHandshake _ ->
    assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
    assert False
  | M.TlsKeyUpdate _ ->
    assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
    assert False

let lemma_server_hs_client_hello_received_selected_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Some? model.CS.model_handshake.CS.hs_server_selection /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
        CS.legal_event model (CS.ConnLocalEvent local) /\
        (match local with
         | CS.LocalFail _ -> False
         | CS.LocalDeriveSharedSecret _ -> False
         | _ -> True))
      (ensures False)
=
  assert (CS.legal_local_event model local);
  match local with
  | CS.LocalFail _ ->
    assert False
  | CS.LocalStartHandshake _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalStartServer ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalSelectServerParameters _ ->
    assert (model.CS.model_handshake.CS.hs_server_selection == None);
    assert False
  | CS.LocalDeriveSharedSecret _ ->
    assert False
  | CS.LocalInstallTrafficKeys install ->
    assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert (model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    assert False
  | CS.LocalInstallTrafficKeysForRole role_install ->
    let install = role_install.CS.install_payload in
    assert (CS.legal_local_event
      model
      (CS.LocalInstallTrafficKeysForRole role_install));
    assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ServerEndpoint
      CS.HsClientHelloReceived
      install);
    (match install.CS.install_epoch with
    | CS.TrafficHandshake ->
      assert (CS.HsClientHelloReceived == CS.HsServerHelloSent);
      assert False
    | CS.TrafficApplication ->
      (match install.CS.install_direction with
      | CS.TrafficWrite ->
        assert (CS.HsClientHelloReceived == CS.HsServerFinishedSent);
        assert False
      | CS.TrafficRead ->
        assert (CS.HsClientHelloReceived == CS.HsClientFinishedReceived);
        assert False))
  | CS.LocalValidateCertificate _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyCertificateSignature _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalSignCertificateVerify _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyFinished _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyClientFinished _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalDeliverApplicationData _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False

let lemma_server_hs_client_hello_received_shared_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        CS.legal_event model (CS.ConnLocalEvent local) /\
        (match local with
         | CS.LocalFail _ -> False
         | _ -> True))
      (ensures False)
=
  assert (CS.legal_local_event model local);
  match local with
  | CS.LocalFail _ ->
    assert False
  | CS.LocalStartHandshake _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalStartServer ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalSelectServerParameters _ ->
    assert (model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
    assert False
  | CS.LocalDeriveSharedSecret _ ->
    assert (model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
    assert False
  | CS.LocalInstallTrafficKeys install ->
    assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert (model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    assert False
  | CS.LocalInstallTrafficKeysForRole role_install ->
    let install = role_install.CS.install_payload in
    assert (CS.legal_local_event
      model
      (CS.LocalInstallTrafficKeysForRole role_install));
    assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ServerEndpoint
      CS.HsClientHelloReceived
      install);
    (match install.CS.install_epoch with
    | CS.TrafficHandshake ->
      assert (CS.HsClientHelloReceived == CS.HsServerHelloSent);
      assert False
    | CS.TrafficApplication ->
      (match install.CS.install_direction with
      | CS.TrafficWrite ->
        assert (CS.HsClientHelloReceived == CS.HsServerFinishedSent);
        assert False
      | CS.TrafficRead ->
        assert (CS.HsClientHelloReceived == CS.HsClientFinishedReceived);
        assert False))
  | CS.LocalValidateCertificate _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyCertificateSignature _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalSignCertificateVerify _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyFinished _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalVerifyClientFinished _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False
  | CS.LocalDeliverApplicationData _ ->
    assert_norm (CS.legal_local_event model local == False);
    assert False

let lemma_server_hs_client_hello_received_shared_network_event_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        CS.legal_event model (CS.ConnNetworkEvent msg) /\
        (match msg.CL.message_direction, msg.CL.message_value with
         | CL.Sent, M.TlsHandshake (M.ServerHello _) -> False
         | _, M.TlsAlert _ -> False
         | _, M.TlsChangeCipherSpec -> False
         | _, _ -> True))
      (ensures False)
=
  assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
  match msg.CL.message_value with
  | M.TlsAlert _ ->
    assert False
  | M.TlsChangeCipherSpec ->
    assert False
  | M.TlsHandshake hs ->
    (match msg.CL.message_direction, hs with
    | CL.Sent, M.ServerHello _ ->
      assert False
    | _, _ ->
      assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
      assert False)
  | M.TlsApplicationData _ ->
    assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
    assert False
  | M.TlsIgnoredPostHandshake _ ->
    assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
    assert False
  | M.TlsKeyUpdate _ ->
    assert_norm (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value == False);
    assert False

let lemma_server_derive_shared_secret_step_model
  (model:CS.connection_model)
  (shared:TLS13.Crypto.Spec.x25519_shared_secret)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived)
      (ensures
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
        Some (CS.derive_shared_secret_model
          model
          model.CS.model_handshake
          shared))
=
  match model.CS.model_control with
  | CS.ControlHandshaking stage ->
    (match stage with
    | CS.HsClientHelloReceived ->
      assert (model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived);
      assert (
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
        Some (CS.derive_shared_secret_model
          model
          model.CS.model_handshake
          shared))
    | _ ->
      assert (model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived);
      assert False)
  | _ ->
    assert (model.CS.model_control ==
      CS.ControlHandshaking CS.HsClientHelloReceived);
    assert False

let lemma_server_hs_client_hello_received_shared_event_server_hello_if_not_ccs
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        CS.conn_events_raw_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model /\
        ~ (exists m.
            ev == CS.ConnNetworkEvent m /\
            m.CL.message_value == M.TlsChangeCipherSpec))
      (ensures
        exists sh.
          ev == CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }))
=
  PWR.lemma_conn_events_raw_replay_head
    model
    ev
    rest
    raw_sent
    raw_received
    final_model;
  eliminate exists
    (model1:CS.connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    CS.legal_event model ev /\
    CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  returns
    exists sh.
      ev == CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      })
  with _.
  (
    match ev with
    | CS.ConnLocalEvent local ->
      (match local with
      | CS.LocalFail err ->
        assert_norm (
          CS.step_model model (CS.ConnLocalEvent (CS.LocalFail err)) ==
          Some (CS.fail_model model err));
        assert (model1 == CS.fail_model model err);
        assert (model1.CS.model_control == CS.ControlFailed err);
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model;
        assert (CS.ControlFailed? final_model.CS.model_control);
        assert (final_model.CS.model_control == CS.ControlApplicationData);
        assert False
      | _ ->
        lemma_server_hs_client_hello_received_shared_local_event_step_none
          model
          local;
        assert False)
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
      | M.TlsAlert alert ->
        assert_norm (
          CS.step_model
            model
            (CS.ConnNetworkEvent msg) ==
          Some (CS.fail_model model (T.AlertError alert)));
        assert (model1 == CS.fail_model model (T.AlertError alert));
        assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model;
        assert (CS.ControlFailed? final_model.CS.model_control);
        assert (final_model.CS.model_control == CS.ControlApplicationData);
        assert False
      | M.TlsChangeCipherSpec ->
        assert (exists m.
          ev == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec);
        assert False
      | M.TlsHandshake (M.ServerHello sh) ->
        (match msg.CL.message_direction with
        | CL.Sent ->
          assert (ev == CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }));
          assert (exists sh0.
            ev == CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ServerHello sh0);
            }))
        | CL.Received ->
          lemma_server_hs_client_hello_received_shared_network_event_step_none
            model
            msg;
          assert False)
      | _ ->
        lemma_server_hs_client_hello_received_shared_network_event_step_none
          model
          msg;
        assert False)
  )

let lemma_server_no_tail_third_event_select_parameters_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists ch e2 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            e2 ::
            rest /\
          ~ (exists m.
              e2 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch selection rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest)
=
  eliminate exists ch e2 rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      e2 ::
      rest /\
    ~ (exists m.
        e2 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec)
  returns
    exists ch0 selection rest0.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch0);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        rest0
  with _.
  (
    assert (ST.server_end_to_end_invariant server);
    assert (CS.connection_state_raw_event_replay_consistent server);
    let initial = CS.initial_model server.CS.cs_model.CS.model_config in
    let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
    let ev1 = CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }) in
    assert (CS.conn_events_raw_replay
      initial
      (ev0 :: ev1 :: e2 :: rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PWR.lemma_conn_events_raw_replay_head
      initial
      ev0
      (ev1 :: e2 :: rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
      CS.legal_event initial ev0 /\
      CS.step_model initial ev0 == Some model1 /\
      CS.event_raw_delta_legal initial ev0 delta0_sent delta0_received /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append delta0_sent tail0_sent) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append delta0_received tail0_received) /\
      CS.conn_events_raw_replay model1 (ev1 :: e2 :: rest) tail0_sent tail0_received server.CS.cs_model
    returns
      exists ch0 selection rest0.
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch0);
          }) ::
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
          rest0
    with _.
    (
      assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
      assert_norm (
        CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
        Some (CS.with_handshake_stage
          initial
          initial.CS.model_handshake
          CS.HsAwaitingClientHello));
      assert (model1.CS.model_control ==
        CS.ControlHandshaking CS.HsAwaitingClientHello);
      assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);
      PWR.lemma_conn_events_raw_replay_head
        model1
        ev1
        (e2 :: rest)
        tail0_sent
        tail0_received
        server.CS.cs_model;
      eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
        CS.legal_event model1 ev1 /\
        CS.step_model model1 ev1 == Some model2 /\
        CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
        Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
        Seq.equal tail0_received (B.append delta1_received tail1_received) /\
        CS.conn_events_raw_replay model2 (e2 :: rest) tail1_sent tail1_received server.CS.cs_model
      returns
        exists ch0 selection rest0.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch0);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest0
      with _.
      (
        assert (model2.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived);
        assert (model2.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert (model2.CS.model_handshake.CS.hs_server_selection == None);
        assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
        PWR.lemma_conn_events_raw_replay_head
          model2
          e2
          rest
          tail1_sent
          tail1_received
          server.CS.cs_model;
        eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
          CS.legal_event model2 e2 /\
          CS.step_model model2 e2 == Some model3 /\
          CS.event_raw_delta_legal model2 e2 delta2_sent delta2_received /\
          Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
          Seq.equal tail1_received (B.append delta2_received tail2_received) /\
          CS.conn_events_raw_replay model3 rest tail2_sent tail2_received server.CS.cs_model
        returns
          exists ch0 selection rest0.
            server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch0);
              }) ::
              CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
              rest0
        with _.
        (
          match e2 with
          | CS.ConnLocalEvent local ->
            (match local with
            | CS.LocalFail err ->
              assert_norm (
                CS.step_model model2 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                Some (CS.fail_model model2 err));
              assert (CS.step_model model2 e2 == Some (CS.fail_model model2 err));
              assert (model3 == CS.fail_model model2 err);
              assert (model3.CS.model_control == CS.ControlFailed err);
              PNI.lemma_conn_events_raw_replay_from_failed_results_failed
                model3
                rest
                tail2_sent
                tail2_received
                server.CS.cs_model;
              assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert False
            | CS.LocalSelectServerParameters selection ->
              assert (e2 == CS.ConnLocalEvent (CS.LocalSelectServerParameters selection));
              assert (exists ch0 selection0 rest0.
                server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                  rest0)
            | _ ->
              lemma_server_hs_client_hello_received_local_event_step_none model2 local;
              assert False)
          | CS.ConnNetworkEvent msg ->
            (match msg.CL.message_value with
            | M.TlsAlert alert ->
              assert_norm (
                CS.step_model
                  model2
                  (CS.ConnNetworkEvent msg) ==
                Some (CS.fail_model model2 (T.AlertError alert)));
              assert (model3 == CS.fail_model model2 (T.AlertError alert));
              assert (model3.CS.model_control == CS.ControlFailed (T.AlertError alert));
              PNI.lemma_conn_events_raw_replay_from_failed_results_failed
                model3
                rest
                tail2_sent
                tail2_received
                server.CS.cs_model;
              assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert False
            | M.TlsChangeCipherSpec ->
              assert (exists m.
                e2 == CS.ConnNetworkEvent m /\
                m.CL.message_value == M.TlsChangeCipherSpec);
              assert False
            | _ ->
              lemma_server_hs_client_hello_received_network_event_step_none model2 msg;
              assert False)
        )
      )
    )
  )

let lemma_server_no_tail_fourth_event_derive_shared_secret_if_not_ccs16
        (server:CS.connection_state)
        : Lemma
            (requires
              SD.server_driver_application_ready server /\
              FStar.List.Tot.length server.CS.cs_event_log == 16 /\
              (exists ch selection e3 rest.
                server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                  e3 ::
                  rest /\
                ~ (exists m.
                    e3 == CS.ConnNetworkEvent m /\
                    m.CL.message_value == M.TlsChangeCipherSpec)))
            (ensures
              exists ch selection server_shared rest.
                server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                  rest)
=
        eliminate exists ch selection e3 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            e3 ::
            rest /\
          ~ (exists m.
              e3 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)
        returns
          exists ch0 selection0 server_shared rest0.
            server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch0);
              }) ::
              CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
              rest0
        with _.
        (
          assert (ST.server_end_to_end_invariant server);
          assert (CS.connection_state_raw_event_replay_consistent server);
          let initial = CS.initial_model server.CS.cs_model.CS.model_config in
          let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
          let ev1 = CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) in
          let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
          assert (CS.conn_events_raw_replay
            initial
            (ev0 :: ev1 :: ev2 :: e3 :: rest)
            server.CS.cs_wire_log.CL.raw_sent
            server.CS.cs_wire_log.CL.raw_received
            server.CS.cs_model);
          PWR.lemma_conn_events_raw_replay_head
            initial
            ev0
            (ev1 :: ev2 :: e3 :: rest)
            server.CS.cs_wire_log.CL.raw_sent
            server.CS.cs_wire_log.CL.raw_received
            server.CS.cs_model;
          eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
            CS.legal_event initial ev0 /\
            CS.step_model initial ev0 == Some model1 /\
            CS.event_raw_delta_legal initial ev0 delta0_sent delta0_received /\
            Seq.equal
              server.CS.cs_wire_log.CL.raw_sent
              (B.append delta0_sent tail0_sent) /\
            Seq.equal
              server.CS.cs_wire_log.CL.raw_received
              (B.append delta0_received tail0_received) /\
            CS.conn_events_raw_replay model1 (ev1 :: ev2 :: e3 :: rest) tail0_sent tail0_received server.CS.cs_model
          returns
            exists ch0 selection0 server_shared rest0.
              server.CS.cs_event_log ==
                CS.ConnLocalEvent CS.LocalStartServer ::
                CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                }) ::
                CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                rest0
          with _.
          (
            assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
            assert_norm (
              CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
              Some (CS.with_handshake_stage
                initial
                initial.CS.model_handshake
                CS.HsAwaitingClientHello));
            assert (model1.CS.model_control ==
              CS.ControlHandshaking CS.HsAwaitingClientHello);
            assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);
            PWR.lemma_conn_events_raw_replay_head
              model1
              ev1
              (ev2 :: e3 :: rest)
              tail0_sent
              tail0_received
              server.CS.cs_model;
            eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
              CS.legal_event model1 ev1 /\
              CS.step_model model1 ev1 == Some model2 /\
              CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
              Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
              Seq.equal tail0_received (B.append delta1_received tail1_received) /\
              CS.conn_events_raw_replay model2 (ev2 :: e3 :: rest) tail1_sent tail1_received server.CS.cs_model
            returns
              exists ch0 selection0 server_shared rest0.
                server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                  rest0
            with _.
            (
              assert (model2.CS.model_control ==
                CS.ControlHandshaking CS.HsClientHelloReceived);
              assert (model2.CS.model_config.CS.config_role == CS.ServerEndpoint);
              assert (model2.CS.model_handshake.CS.hs_server_selection == None);
              assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
              PWR.lemma_conn_events_raw_replay_head
                model2
                ev2
                (e3 :: rest)
                tail1_sent
                tail1_received
                server.CS.cs_model;
              eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
                CS.legal_event model2 ev2 /\
                CS.step_model model2 ev2 == Some model3 /\
                CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
                Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
                Seq.equal tail1_received (B.append delta2_received tail2_received) /\
                CS.conn_events_raw_replay model3 (e3 :: rest) tail2_sent tail2_received server.CS.cs_model
              returns
                exists ch0 selection0 server_shared rest0.
                  server.CS.cs_event_log ==
                    CS.ConnLocalEvent CS.LocalStartServer ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                    rest0
              with _.
              (
                assert (CS.step_model model2 ev2 ==
                  CS.step_model
                    model2
                    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)));
                assert_norm (
                  CS.step_model
                    model2
                    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
                  Some (CS.with_handshake_stage
                    model2
                    { model2.CS.model_handshake with
                        CS.hs_server_selection = Some selection;
                        CS.hs_client_hello =
                          Some selection.CS.server_selected_client_hello;
                    }
                    CS.HsClientHelloReceived));
                assert (model3.CS.model_control ==
                  CS.ControlHandshaking CS.HsClientHelloReceived);
                assert (model3.CS.model_config.CS.config_role == CS.ServerEndpoint);
                assert (Some? model3.CS.model_handshake.CS.hs_server_selection);
                assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
                PWR.lemma_conn_events_raw_replay_head
                  model3
                  e3
                  rest
                  tail2_sent
                  tail2_received
                  server.CS.cs_model;
                eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
                  CS.legal_event model3 e3 /\
                  CS.step_model model3 e3 == Some model4 /\
                  CS.event_raw_delta_legal model3 e3 delta3_sent delta3_received /\
                  Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
                  Seq.equal tail2_received (B.append delta3_received tail3_received) /\
                  CS.conn_events_raw_replay model4 rest tail3_sent tail3_received server.CS.cs_model
                returns
                  exists ch0 selection0 server_shared rest0.
                    server.CS.cs_event_log ==
                      CS.ConnLocalEvent CS.LocalStartServer ::
                      CS.ConnNetworkEvent ({
                        CL.message_direction = CL.Received;
                        CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                      }) ::
                      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                      rest0
                with _.
                (
                  match e3 with
                  | CS.ConnLocalEvent local ->
                    (match local with
                    | CS.LocalFail err ->
                      assert_norm (
                        CS.step_model model3 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                        Some (CS.fail_model model3 err));
                      assert (model4 == CS.fail_model model3 err);
                      assert (model4.CS.model_control == CS.ControlFailed err);
                      PNI.lemma_conn_events_raw_replay_from_failed_results_failed
                        model4
                        rest
                        tail3_sent
                        tail3_received
                        server.CS.cs_model;
                      assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                      assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                      assert False
                    | CS.LocalDeriveSharedSecret server_shared ->
                      assert (e3 == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared));
                      assert (exists ch0 selection0 server_shared0 rest0.
                        server.CS.cs_event_log ==
                          CS.ConnLocalEvent CS.LocalStartServer ::
                          CS.ConnNetworkEvent ({
                            CL.message_direction = CL.Received;
                            CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                          }) ::
                          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
                          rest0)
                    | _ ->
                      lemma_server_hs_client_hello_received_selected_local_event_step_none
                        model3
                        local;
                      assert False)
                  | CS.ConnNetworkEvent msg ->
                    (match msg.CL.message_value with
                    | M.TlsAlert alert ->
                      assert_norm (
                        CS.step_model
                          model3
                          (CS.ConnNetworkEvent msg) ==
                        Some (CS.fail_model model3 (T.AlertError alert)));
                      assert (model4 == CS.fail_model model3 (T.AlertError alert));
                      assert (model4.CS.model_control == CS.ControlFailed (T.AlertError alert));
                      PNI.lemma_conn_events_raw_replay_from_failed_results_failed
                        model4
                        rest
                        tail3_sent
                        tail3_received
                        server.CS.cs_model;
                      assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                      assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                      assert False
                    | M.TlsChangeCipherSpec ->
                      assert (exists m.
                        e3 == CS.ConnNetworkEvent m /\
                        m.CL.message_value == M.TlsChangeCipherSpec);
                      assert False
                    | _ ->
                      lemma_server_hs_client_hello_received_network_event_step_none
                        model3
                        msg;
                      assert False)
                )
              )
            )
          )
        )

let lemma_server_no_tail_fifth_event_server_hello_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists ch selection server_shared e4 rest.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           e4 ::
           rest /\
         ~ (exists m.
             e4 == CS.ConnNetworkEvent m /\
             m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch selection server_shared sh rest.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) ::
           rest)
=
  eliminate exists ch selection server_shared e4 rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
      e4 ::
      rest /\
    ~ (exists m.
        e4 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec)
  returns
    exists ch0 selection0 server_shared0 sh rest0.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello ch0);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
        CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }) ::
        rest0
  with _.
  (
    assert (ST.server_end_to_end_invariant server);
    assert (CS.connection_state_raw_event_replay_consistent server);
    let initial = CS.initial_model server.CS.cs_model.CS.model_config in
    let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
    let ev1 = CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }) in
    let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
    let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
    assert (CS.conn_events_raw_replay
      initial
      (ev0 :: ev1 :: ev2 :: ev3 :: e4 :: rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PWR.lemma_conn_events_raw_replay_head
      initial
      ev0
      (ev1 :: ev2 :: ev3 :: e4 :: rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists model1 delta0_sent delta0_received tail0_sent tail0_received.
      CS.legal_event initial ev0 /\
      CS.step_model initial ev0 == Some model1 /\
      CS.event_raw_delta_legal initial ev0 delta0_sent delta0_received /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append delta0_sent tail0_sent) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append delta0_received tail0_received) /\
      CS.conn_events_raw_replay
        model1
        (ev1 :: ev2 :: ev3 :: e4 :: rest)
        tail0_sent
        tail0_received
        server.CS.cs_model
    returns
      exists ch0 selection0 server_shared0 sh rest0.
        server.CS.cs_event_log ==
         CS.ConnLocalEvent CS.LocalStartServer ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.ClientHello ch0);
         }) ::
         CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
         CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.ServerHello sh);
         }) ::
         rest0
    with _.
    (
      assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
      assert_norm (
        CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
        Some (CS.with_handshake_stage
         initial
         initial.CS.model_handshake
         CS.HsAwaitingClientHello));
      assert (model1.CS.model_control ==
        CS.ControlHandshaking CS.HsAwaitingClientHello);
      assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);
      PWR.lemma_conn_events_raw_replay_head
        model1
        ev1
        (ev2 :: ev3 :: e4 :: rest)
        tail0_sent
        tail0_received
        server.CS.cs_model;
      eliminate exists model2 delta1_sent delta1_received tail1_sent tail1_received.
        CS.legal_event model1 ev1 /\
        CS.step_model model1 ev1 == Some model2 /\
        CS.event_raw_delta_legal model1 ev1 delta1_sent delta1_received /\
        Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
        Seq.equal tail0_received (B.append delta1_received tail1_received) /\
        CS.conn_events_raw_replay
         model2
         (ev2 :: ev3 :: e4 :: rest)
         tail1_sent
         tail1_received
         server.CS.cs_model
      returns
        exists ch0 selection0 server_shared0 sh rest0.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch0);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) ::
           rest0
      with _.
      (
        assert (model2.CS.model_control ==
         CS.ControlHandshaking CS.HsClientHelloReceived);
        assert (model2.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert (model2.CS.model_handshake.CS.hs_server_selection == None);
        assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
        PWR.lemma_conn_events_raw_replay_head
         model2
         ev2
         (ev3 :: e4 :: rest)
         tail1_sent
         tail1_received
         server.CS.cs_model;
        eliminate exists model3 delta2_sent delta2_received tail2_sent tail2_received.
         CS.legal_event model2 ev2 /\
         CS.step_model model2 ev2 == Some model3 /\
         CS.event_raw_delta_legal model2 ev2 delta2_sent delta2_received /\
         Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
         Seq.equal tail1_received (B.append delta2_received tail2_received) /\
         CS.conn_events_raw_replay
           model3
           (ev3 :: e4 :: rest)
           tail2_sent
           tail2_received
           server.CS.cs_model
        returns
         exists ch0 selection0 server_shared0 sh rest0.
           server.CS.cs_event_log ==
             CS.ConnLocalEvent CS.LocalStartServer ::
             CS.ConnNetworkEvent ({
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake (M.ClientHello ch0);
             }) ::
             CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
             CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
             CS.ConnNetworkEvent ({
               CL.message_direction = CL.Sent;
               CL.message_value = M.TlsHandshake (M.ServerHello sh);
             }) ::
             rest0
        with _.
        (
         assert (CS.step_model model2 ev2 ==
           CS.step_model
             model2
             (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)));
         assert_norm (
           CS.step_model
             model2
             (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
           Some (CS.with_handshake_stage
             model2
             { model2.CS.model_handshake with
                 CS.hs_server_selection = Some selection;
                 CS.hs_client_hello =
                   Some selection.CS.server_selected_client_hello;
             }
             CS.HsClientHelloReceived));
         assert (model3.CS.model_control ==
           CS.ControlHandshaking CS.HsClientHelloReceived);
         assert (model3.CS.model_config.CS.config_role == CS.ServerEndpoint);
         assert (Some? model3.CS.model_handshake.CS.hs_server_selection);
         assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
         PWR.lemma_conn_events_raw_replay_head
           model3
           ev3
           (e4 :: rest)
           tail2_sent
           tail2_received
           server.CS.cs_model;
         eliminate exists model4 delta3_sent delta3_received tail3_sent tail3_received.
           CS.legal_event model3 ev3 /\
           CS.step_model model3 ev3 == Some model4 /\
           CS.event_raw_delta_legal model3 ev3 delta3_sent delta3_received /\
           Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
           Seq.equal tail2_received (B.append delta3_received tail3_received) /\
           CS.conn_events_raw_replay
             model4
             (e4 :: rest)
             tail3_sent
             tail3_received
             server.CS.cs_model
         returns
           exists ch0 selection0 server_shared0 sh rest0.
             server.CS.cs_event_log ==
               CS.ConnLocalEvent CS.LocalStartServer ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.ClientHello ch0);
               }) ::
               CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
               CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.ServerHello sh);
               }) ::
               rest0
         with _.
         (
           assert (CS.step_model model3 ev3 ==
             CS.step_model
               model3
               (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)));
           lemma_server_derive_shared_secret_step_model model3 server_shared;
           assert (model4 == CS.derive_shared_secret_model
             model3
             model3.CS.model_handshake
             server_shared);
           assert (model4.CS.model_control ==
             CS.ControlHandshaking CS.HsClientHelloReceived);
           assert (model4.CS.model_config.CS.config_role == CS.ServerEndpoint);
           assert (Some? model4.CS.model_handshake.CS.hs_server_selection);
           assert (Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
           assert (CS.conn_events_raw_replay
             model4
             (e4 :: rest)
             tail3_sent
             tail3_received
             server.CS.cs_model);
           lemma_server_hs_client_hello_received_shared_event_server_hello_if_not_ccs
             model4
             e4
             rest
             tail3_sent
             tail3_received
             server.CS.cs_model;
           eliminate exists (sh:M.server_hello).
             e4 == CS.ConnNetworkEvent ({
               CL.message_direction = CL.Sent;
               CL.message_value = M.TlsHandshake (M.ServerHello sh);
             })
           returns
             exists ch0 selection0 server_shared0 sh rest0.
               server.CS.cs_event_log ==
                 CS.ConnLocalEvent CS.LocalStartServer ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                 }) ::
                 CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ServerHello sh);
                 }) ::
                 rest0
           with _.
           (
             assert (server.CS.cs_event_log ==
               CS.ConnLocalEvent CS.LocalStartServer ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.ClientHello ch);
               }) ::
               CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
               CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.ServerHello sh);
               }) ::
               rest);
             assert (exists ch0 selection0 server_shared0 sh0 rest0.
               server.CS.cs_event_log ==
                 CS.ConnLocalEvent CS.LocalStartServer ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                 }) ::
                 CS.ConnLocalEvent (CS.LocalSelectServerParameters selection0) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared0) ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ServerHello sh0);
                 }) ::
                 rest0)
           )
         )
        )
      )
    )
  )
