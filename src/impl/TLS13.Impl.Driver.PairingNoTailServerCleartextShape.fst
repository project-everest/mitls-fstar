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
