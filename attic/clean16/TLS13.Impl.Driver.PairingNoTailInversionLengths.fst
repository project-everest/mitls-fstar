module TLS13.Impl.Driver.PairingNoTailInversionLengths

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
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
open TLS13.Impl.Driver.PairingNoTailInversion

let lemma_client_post_derive_next_event_handshake_traffic_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 11)
      (ensures client_no_tail_handshake_traffic_install_event ev)
=
  lemma_client_hs_server_hello_received_derived_no_traffic_progress_rank model;
  assert (client_application_progress_rank model == 12);
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
  with
  (
    CSL.lemma_step_model_preserves_config model ev model1;
    assert (model1.CS.model_config == model.CS.model_config);
    match ev with
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalFail err ->
         assert (model1.CS.model_control == CS.ControlFailed err);
         lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (CS.ControlFailed? final_model.CS.model_control);
         assert (final_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | CS.LocalDeriveSharedSecret shared ->
         assert (ev == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared));
         assert (
           CS.step_model model (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
           Some (CS.derive_shared_secret_model model model.CS.model_handshake shared));
         assert (model1 == CS.derive_shared_secret_model model model.CS.model_handshake shared);
         assert (model1.CS.model_config == model.CS.model_config);
         assert (model1.CS.model_config.CS.config_role == CS.ClientEndpoint);
         assert (model1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
         assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
         assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
         assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
         assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
         assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
         lemma_client_hs_server_hello_received_derived_no_traffic_progress_rank model1;
         lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (client_application_progress_rank model1 == 12);
         assert (client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (FStar.List.Tot.length rest == 11);
         assert (12 <= 11);
         assert False
       | CS.LocalInstallTrafficKeys install ->
         assert (ev == CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install));
         assert (CS.legal_local_event model local);
         assert (CS.traffic_install_allowed_at_stage CS.HsServerHelloReceived install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake ->
            assert (client_no_tail_handshake_traffic_install_event ev)
          | CS.TrafficApplication ->
            assert_norm (CS.traffic_install_allowed_at_stage
              CS.HsServerHelloReceived
              install == False);
            assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (ev == CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install));
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsServerHelloReceived
           role_install.CS.install_payload);
         (match role_install.CS.install_payload.CS.install_epoch with
          | CS.TrafficHandshake ->
            assert (client_no_tail_handshake_traffic_install_event ev)
          | CS.TrafficApplication ->
            assert_norm (CS.traffic_install_allowed_at_stage_for_role
              CS.ClientEndpoint
              CS.HsServerHelloReceived
              role_install.CS.install_payload == False);
            assert False)
       | _ ->
         lemma_client_hs_server_hello_received_local_event_step_none model local;
         assert (CS.step_model model ev == None);
         assert False)
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsAlert alert ->
         assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
         lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (CS.ControlFailed? final_model.CS.model_control);
         assert (final_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | M.TlsChangeCipherSpec ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == Some model);
         assert (model1 == model);
         lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (client_application_progress_rank model1 == 12);
         assert (client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (FStar.List.Tot.length rest == 11);
         assert (12 <= 11);
         assert False
       | M.TlsHandshake handshake_msg ->
         (match msg.CL.message_direction, handshake_msg with
          | CL.Received, M.EncryptedExtensions ee ->
            lemma_client_hs_server_hello_received_empty_keys_encrypted_extensions_illegal
              model
              ee;
            assert False
          | _, _ ->
            lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
              model
              msg;
            assert (CS.step_model model ev == None);
            assert False)
       | M.TlsApplicationData _ ->
         lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False
       | M.TlsIgnoredPostHandshake _ ->
         lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False
       | M.TlsKeyUpdate _ ->
         lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False)
  )

let lemma_client_no_tail_log_spine
  (client:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length client.CS.cs_event_log == 15)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
          client.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
=
  lemma_list_length_pos_cons client.CS.cs_event_log 14;
  eliminate exists e0 tl0.
    client.CS.cs_event_log == e0 :: tl0 /\
    FStar.List.Tot.length tl0 == 14
  with
  (
  lemma_list_length_pos_cons tl0 13;
  eliminate exists e1 tl1.
    tl0 == e1 :: tl1 /\
    FStar.List.Tot.length tl1 == 13
  with
  (
  lemma_list_length_pos_cons tl1 12;
  eliminate exists e2 tl2.
    tl1 == e2 :: tl2 /\
    FStar.List.Tot.length tl2 == 12
  with
  (
  lemma_list_length_pos_cons tl2 11;
  eliminate exists e3 tl3.
    tl2 == e3 :: tl3 /\
    FStar.List.Tot.length tl3 == 11
  with
  (
  lemma_list_length_pos_cons tl3 10;
  eliminate exists e4 tl4.
    tl3 == e4 :: tl4 /\
    FStar.List.Tot.length tl4 == 10
  with
  (
  lemma_list_length_pos_cons tl4 9;
  eliminate exists e5 tl5.
    tl4 == e5 :: tl5 /\
    FStar.List.Tot.length tl5 == 9
  with
  (
  lemma_list_length_pos_cons tl5 8;
  eliminate exists e6 tl6.
    tl5 == e6 :: tl6 /\
    FStar.List.Tot.length tl6 == 8
  with
  (
  lemma_list_length_pos_cons tl6 7;
  eliminate exists e7 tl7.
    tl6 == e7 :: tl7 /\
    FStar.List.Tot.length tl7 == 7
  with
  (
  lemma_list_length_pos_cons tl7 6;
  eliminate exists e8 tl8.
    tl7 == e8 :: tl8 /\
    FStar.List.Tot.length tl8 == 6
  with
  (
  lemma_list_length_pos_cons tl8 5;
  eliminate exists e9 tl9.
    tl8 == e9 :: tl9 /\
    FStar.List.Tot.length tl9 == 5
  with
  (
  lemma_list_length_pos_cons tl9 4;
  eliminate exists e10 tl10.
    tl9 == e10 :: tl10 /\
    FStar.List.Tot.length tl10 == 4
  with
  (
  lemma_list_length_pos_cons tl10 3;
  eliminate exists e11 tl11.
    tl10 == e11 :: tl11 /\
    FStar.List.Tot.length tl11 == 3
  with
  (
  lemma_list_length_pos_cons tl11 2;
  eliminate exists e12 tl12.
    tl11 == e12 :: tl12 /\
    FStar.List.Tot.length tl12 == 2
  with
  (
  lemma_list_length_pos_cons tl12 1;
  eliminate exists e13 tl13.
    tl12 == e13 :: tl13 /\
    FStar.List.Tot.length tl13 == 1
  with
  (
  lemma_list_length_pos_cons tl13 0;
  eliminate exists e14 tl14.
    tl13 == e14 :: tl14 /\
    FStar.List.Tot.length tl14 == 0
  with
  (
    match tl14 with
    | [] -> ()
    | _ :: _ -> assert False
  )))))))))))))))

let lemma_server_no_tail_log_spine
  (server:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
          server.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
=
  lemma_client_no_tail_log_spine server

let lemma_client_no_tail_log_spine16
  (client:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
          client.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
=
  lemma_list_length_pos_cons client.CS.cs_event_log 15;
  eliminate exists e0 tl0.
    client.CS.cs_event_log == e0 :: tl0 /\
    FStar.List.Tot.length tl0 == 15
  with
  (
    let tail_client = { client with CS.cs_event_log = tl0 } in
    lemma_client_no_tail_log_spine tail_client;
    eliminate exists e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
      tail_client.CS.cs_event_log ==
        [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
    with
    (
      assert (tl0 == [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (client.CS.cs_event_log ==
        [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
    )
  )

let lemma_server_no_tail_log_spine16
  (server:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length server.CS.cs_event_log == 16)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
          server.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
=
  lemma_client_no_tail_log_spine16 server

let lemma_client_no_tail_first_event_start
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) :: rest)
=
  lemma_client_no_tail_log_spine16 client;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    client.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
  with
  (
    assert (CT.client_end_to_end_invariant client);
    assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client);
    let initial = CS.initial_model client.CS.cs_model.CS.model_config in
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      client.CS.cs_event_log
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model);
    assert (client.CS.cs_event_log ==
      e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model);
    assert_norm (
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        initial
        (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event initial e0 /\
        CS.step_model initial e0 == Some model1 /\
        CS.event_raw_delta_legal initial e0 delta_sent delta_received /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append delta_sent tail_sent) /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append delta_received tail_received) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model1
          [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
          tail_sent
          tail_received
          client.CS.cs_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event initial e0 /\
      CS.step_model initial e0 == Some model1 /\
      CS.event_raw_delta_legal initial e0 delta_sent delta_received /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        (B.append delta_sent tail_sent) /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_received
        (B.append delta_received tail_received) /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        model1
        [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
        tail_sent
        tail_received
        client.CS.cs_model
    with
    (
      assert (initial.CS.model_control == CS.ControlNew);
      assert (initial.CS.model_config.CS.config_role == CS.ClientEndpoint);
      match e0 with
      | CS.ConnLocalEvent local ->
        (match local with
        | CS.LocalStartHandshake start ->
          ()
        | CS.LocalFail err ->
          assert (model1.CS.model_control == CS.ControlFailed err);
          lemma_conn_events_raw_replay_from_failed_results_failed
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent
            tail_received
            client.CS.cs_model;
          assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
          assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          assert False
        | CS.LocalStartServer ->
          assert_norm (CS.legal_event initial e0 == False);
          assert False
        | _ ->
          assert_norm (CS.step_model initial e0 == None);
          assert False)
      | CS.ConnNetworkEvent msg ->
        (match msg.CL.message_value with
        | M.TlsAlert alert ->
          assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
          lemma_conn_events_raw_replay_from_failed_results_failed
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent
            tail_received
            client.CS.cs_model;
          assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
          assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
          assert False
        | M.TlsHandshake _ ->
          lemma_control_new_non_alert_network_step_none initial msg;
          assert (CS.step_model initial e0 == None);
          assert False
        | M.TlsApplicationData _ ->
          lemma_control_new_non_alert_network_step_none initial msg;
          assert (CS.step_model initial e0 == None);
          assert False
        | M.TlsChangeCipherSpec ->
          lemma_control_new_non_alert_network_step_none initial msg;
          assert (CS.step_model initial e0 == None);
          assert False
        | M.TlsIgnoredPostHandshake _ ->
          lemma_control_new_non_alert_network_step_none initial msg;
          assert (CS.step_model initial e0 == None);
          assert False
        | M.TlsKeyUpdate _ ->
          lemma_control_new_non_alert_network_step_none initial msg;
          assert (CS.step_model initial e0 == None);
          assert False)
    )
  )

let lemma_server_no_tail_first_event_start
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server /\
       FStar.List.Tot.length server.CS.cs_event_log == 15)
     (ensures
       exists rest.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer :: rest)
=
  lemma_server_no_tail_log_spine server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
   server.CS.cs_event_log ==
     [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  with
  (
   assert (ST.server_end_to_end_invariant server);
   assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent server);
   let initial = CS.initial_model server.CS.cs_model.CS.model_config in
   assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
     initial
     server.CS.cs_event_log
     server.CS.cs_wire_log.CL.raw_sent
     server.CS.cs_wire_log.CL.raw_received
     server.CS.cs_model);
   assert (server.CS.cs_event_log ==
     e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
   assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
     initial
     (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
     server.CS.cs_wire_log.CL.raw_sent
     server.CS.cs_wire_log.CL.raw_received
     server.CS.cs_model);
   assert_norm (
     TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
       initial
       (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
       server.CS.cs_wire_log.CL.raw_sent
       server.CS.cs_wire_log.CL.raw_received
       server.CS.cs_model ==
     (exists model1 delta_sent delta_received tail_sent tail_received.
       CS.legal_event initial e0 /\
       CS.step_model initial e0 == Some model1 /\
       CS.event_raw_delta_legal initial e0 delta_sent delta_received /\
       Seq.equal
         server.CS.cs_wire_log.CL.raw_sent
         (B.append delta_sent tail_sent) /\
       Seq.equal
         server.CS.cs_wire_log.CL.raw_received
         (B.append delta_received tail_received) /\
       TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
         model1
         [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
         tail_sent
         tail_received
         server.CS.cs_model));
   eliminate exists model1 delta_sent delta_received tail_sent tail_received.
     CS.legal_event initial e0 /\
     CS.step_model initial e0 == Some model1 /\
     CS.event_raw_delta_legal initial e0 delta_sent delta_received /\
     Seq.equal
       server.CS.cs_wire_log.CL.raw_sent
       (B.append delta_sent tail_sent) /\
     Seq.equal
       server.CS.cs_wire_log.CL.raw_received
       (B.append delta_received tail_received) /\
     TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
       model1
       [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
       tail_sent
       tail_received
       server.CS.cs_model
   with
   (
     assert (initial.CS.model_control == CS.ControlNew);
     assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
     match e0 with
     | CS.ConnLocalEvent local ->
       (match local with
       | CS.LocalStartServer ->
         ()
       | CS.LocalFail err ->
         assert (model1.CS.model_control == CS.ControlFailed err);
         lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
           tail_sent
           tail_received
           server.CS.cs_model;
         assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
         assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | CS.LocalStartHandshake _ ->
         assert_norm (CS.legal_event initial e0 == False);
         assert False
       | _ ->
         assert_norm (CS.step_model initial e0 == None);
         assert False)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_value with
       | M.TlsAlert alert ->
         assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
         lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
           tail_sent
           tail_received
           server.CS.cs_model;
         assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
         assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | M.TlsHandshake _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsApplicationData _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsChangeCipherSpec ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsIgnoredPostHandshake _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsKeyUpdate _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False)
   )
  )

let lemma_server_no_tail_first_event_start16
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server /\
       FStar.List.Tot.length server.CS.cs_event_log == 16)
     (ensures
       exists rest.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer :: rest)
=
  lemma_server_no_tail_log_spine16 server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
   server.CS.cs_event_log ==
     [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
  with
  (
   assert (ST.server_end_to_end_invariant server);
   assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent server);
   let initial = CS.initial_model server.CS.cs_model.CS.model_config in
   assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
     initial
     server.CS.cs_event_log
     server.CS.cs_wire_log.CL.raw_sent
     server.CS.cs_wire_log.CL.raw_received
     server.CS.cs_model);
   assert (server.CS.cs_event_log ==
     e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
   assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
     initial
     (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
     server.CS.cs_wire_log.CL.raw_sent
     server.CS.cs_wire_log.CL.raw_received
     server.CS.cs_model);
   assert_norm (
     TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
       initial
       (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
       server.CS.cs_wire_log.CL.raw_sent
       server.CS.cs_wire_log.CL.raw_received
       server.CS.cs_model ==
     (exists model1 delta_sent delta_received tail_sent tail_received.
       CS.legal_event initial e0 /\
       CS.step_model initial e0 == Some model1 /\
       CS.event_raw_delta_legal initial e0 delta_sent delta_received /\
       Seq.equal
         server.CS.cs_wire_log.CL.raw_sent
         (B.append delta_sent tail_sent) /\
       Seq.equal
         server.CS.cs_wire_log.CL.raw_received
         (B.append delta_received tail_received) /\
       TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
         model1
         [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
         tail_sent
         tail_received
         server.CS.cs_model));
   eliminate exists model1 delta_sent delta_received tail_sent tail_received.
     CS.legal_event initial e0 /\
     CS.step_model initial e0 == Some model1 /\
     CS.event_raw_delta_legal initial e0 delta_sent delta_received /\
     Seq.equal
       server.CS.cs_wire_log.CL.raw_sent
       (B.append delta_sent tail_sent) /\
     Seq.equal
       server.CS.cs_wire_log.CL.raw_received
       (B.append delta_received tail_received) /\
     TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
       model1
       [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
       tail_sent
       tail_received
       server.CS.cs_model
   with
   (
     assert (initial.CS.model_control == CS.ControlNew);
     assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
     match e0 with
     | CS.ConnLocalEvent local ->
       (match local with
       | CS.LocalStartServer ->
         ()
       | CS.LocalFail err ->
         assert (model1.CS.model_control == CS.ControlFailed err);
         lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
           tail_sent
           tail_received
           server.CS.cs_model;
         assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
         assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | CS.LocalStartHandshake _ ->
         assert_norm (CS.legal_event initial e0 == False);
         assert False
       | _ ->
         assert_norm (CS.step_model initial e0 == None);
         assert False)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_value with
       | M.TlsAlert alert ->
         assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
         lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
           tail_sent
           tail_received
           server.CS.cs_model;
         assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
         assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | M.TlsHandshake _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsApplicationData _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsChangeCipherSpec ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsIgnoredPostHandshake _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False
       | M.TlsKeyUpdate _ ->
         lemma_control_new_non_alert_network_step_none initial msg;
         assert (CS.step_model initial e0 == None);
         assert False)
   )
  )

let lemma_client_no_tail_second_event_client_hello
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        (exists start e1 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists start ch rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)
=
  lemma_client_no_tail_log_spine16 client;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    client.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
  with
  (
    eliminate exists start e1' rest'.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1' :: rest' /\
      ~ (exists m.
          e1' == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec)
    with
    (
      assert (client.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1' :: rest');
      assert (e0 == CS.ConnLocalEvent (CS.LocalStartHandshake start));
      assert (e1 == e1');
      assert (rest' == [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (~ (exists m.
        e1 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec));

      assert (CT.client_end_to_end_invariant client);
      assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client);
      let initial = CS.initial_model client.CS.cs_model.CS.model_config in
      assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        initial
        client.CS.cs_event_log
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model);
      assert (client.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert_norm (
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          initial
          (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
          client.CS.cs_wire_log.CL.raw_sent
          client.CS.cs_wire_log.CL.raw_received
          client.CS.cs_model ==
        (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            client.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            client.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent0
            tail_received0
            client.CS.cs_model));
      eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
        CS.legal_event initial e0 /\
        CS.step_model initial e0 == Some model1 /\
        CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append delta_sent0 tail_sent0) /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append delta_received0 tail_received0) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model1
          [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
          tail_sent0
          tail_received0
          client.CS.cs_model
      with
      (
        assert (initial.CS.model_control == CS.ControlNew);
        assert (initial.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert_norm (
          CS.step_model initial (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
          Some (CS.with_handshake_stage
            initial
            ({ initial.CS.model_handshake with CS.hs_start = Some start })
            CS.HsStarted));
        assert (CS.step_model initial e0 ==
          Some (CS.with_handshake_stage
            initial
            ({ initial.CS.model_handshake with CS.hs_start = Some start })
            CS.HsStarted));
        assert (model1 ==
          CS.with_handshake_stage
            initial
            ({ initial.CS.model_handshake with CS.hs_start = Some start })
            CS.HsStarted);
        assert (model1.CS.model_control == CS.ControlHandshaking CS.HsStarted);
        assert (model1.CS.model_config == initial.CS.model_config);

        assert_norm (
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent0
            tail_received0
            client.CS.cs_model ==
          (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent1
              tail_received1
              client.CS.cs_model));
        eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
          CS.legal_event model1 e1 /\
          CS.step_model model1 e1 == Some model2 /\
          CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
          Seq.equal
            tail_sent0
            (B.append delta_sent1 tail_sent1) /\
          Seq.equal
            tail_received0
            (B.append delta_received1 tail_received1) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model2
            [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent1
            tail_received1
            client.CS.cs_model
        with
        (
          match e1 with
          | CS.ConnLocalEvent local ->
            (match local with
             | CS.LocalFail err ->
               assert (e1 == CS.ConnLocalEvent (CS.LocalFail err));
               assert_norm (
                 CS.step_model model1 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                 Some (CS.fail_model model1 err));
               assert (model2.CS.model_control == CS.ControlFailed err);
               lemma_conn_events_raw_replay_from_failed_results_failed
                 model2
                 [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                 tail_sent1
                 tail_received1
                 client.CS.cs_model;
               assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
               assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
               assert False
             | CS.LocalInstallTrafficKeys install ->
               lemma_client_hs_started_install_traffic_keys_illegal model1 install;
               assert False
             | CS.LocalInstallTrafficKeysForRole role_install ->
               lemma_client_hs_started_install_traffic_keys_for_role_illegal model1 role_install;
               assert False
             | _ ->
               lemma_client_hs_started_local_event_step_none model1 local;
               assert (CS.step_model model1 e1 == None);
               assert False)
          | CS.ConnNetworkEvent msg ->
            (match msg.CL.message_value with
             | M.TlsAlert alert ->
               assert (model2.CS.model_control == CS.ControlFailed (T.AlertError alert));
               lemma_conn_events_raw_replay_from_failed_results_failed
                 model2
                 [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                 tail_sent1
                 tail_received1
                 client.CS.cs_model;
               assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
               assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
               assert False
             | M.TlsChangeCipherSpec ->
               assert (e1 == CS.ConnNetworkEvent msg);
               assert (exists m.
                 e1 == CS.ConnNetworkEvent m /\
                 m.CL.message_value == M.TlsChangeCipherSpec);
               assert False
             | M.TlsHandshake handshake_msg ->
               (match msg.CL.message_direction, handshake_msg with
                | CL.Sent, M.ClientHello ch ->
                  assert (e1 == CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }));
                  assert (client.CS.cs_event_log ==
                    CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch);
                    }) ::
                    [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
                | CL.Received, M.ClientHello _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Sent, M.ServerHello _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Received, M.ServerHello _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Sent, M.EncryptedExtensions _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Received, M.EncryptedExtensions _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Sent, M.Certificate _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Received, M.Certificate _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Sent, M.CertificateVerify _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Received, M.CertificateVerify _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Sent, M.Finished _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Received, M.Finished _ ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Sent, M.HelloRetryRequest ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False
                | CL.Received, M.HelloRetryRequest ->
                  lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
                  assert (CS.step_model model1 e1 == None);
                  assert False)
             | M.TlsApplicationData _ ->
               lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
               assert (CS.step_model model1 e1 == None);
               assert False
             | M.TlsIgnoredPostHandshake _ ->
               lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
               assert (CS.step_model model1 e1 == None);
               assert False
             | M.TlsKeyUpdate _ ->
               lemma_client_hs_started_non_client_hello_sent_network_step_none model1 msg;
               assert (CS.step_model model1 e1 == None);
               assert False)
         )
       )
     )
   )

let lemma_client_no_tail_second_event_not_ccs
    (client:CS.connection_state)
    : Lemma
        (requires
          CD.client_driver_application_ready client /\
          FStar.List.Tot.length client.CS.cs_event_log == 16)
        (ensures
          exists start e1 rest.
            client.CS.cs_event_log ==
              CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1 :: rest /\
            ~ (exists m.
                e1 == CS.ConnNetworkEvent m /\
                m.CL.message_value == M.TlsChangeCipherSpec))
=
    lemma_client_no_tail_log_spine16 client;
    lemma_client_no_tail_first_event_start client;
    eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
      client.CS.cs_event_log ==
        [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
    with
    (
      eliminate exists start rest0.
        client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) :: rest0
      with
      (
        assert (client.CS.cs_event_log ==
          e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
        assert (client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) :: rest0);
        assert (e0 == CS.ConnLocalEvent (CS.LocalStartHandshake start));
        assert (rest0 == [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);

        match e1 with
        | CS.ConnLocalEvent _ ->
          ()
        | CS.ConnNetworkEvent msg ->
          (match msg.CL.message_value with
           | M.TlsChangeCipherSpec ->
             assert (CT.client_end_to_end_invariant client);
             assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client);
             lemma_client_application_ready_progress_rank_zero client;
             let initial = CS.initial_model client.CS.cs_model.CS.model_config in
             assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
               initial
               client.CS.cs_event_log
               client.CS.cs_wire_log.CL.raw_sent
               client.CS.cs_wire_log.CL.raw_received
               client.CS.cs_model);
             assert (client.CS.cs_event_log ==
               e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
             assert_norm (
               TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                 initial
                 (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
                 client.CS.cs_wire_log.CL.raw_sent
                 client.CS.cs_wire_log.CL.raw_received
                 client.CS.cs_model ==
               (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
                 CS.legal_event initial e0 /\
                 CS.step_model initial e0 == Some model1 /\
                 CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
                 Seq.equal
                   client.CS.cs_wire_log.CL.raw_sent
                   (B.append delta_sent0 tail_sent0) /\
                 Seq.equal
                   client.CS.cs_wire_log.CL.raw_received
                   (B.append delta_received0 tail_received0) /\
                 TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                   model1
                   [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                   tail_sent0
                   tail_received0
                   client.CS.cs_model));
             eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
               CS.legal_event initial e0 /\
               CS.step_model initial e0 == Some model1 /\
               CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
               Seq.equal
                 client.CS.cs_wire_log.CL.raw_sent
                 (B.append delta_sent0 tail_sent0) /\
               Seq.equal
                 client.CS.cs_wire_log.CL.raw_received
                 (B.append delta_received0 tail_received0) /\
               TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                 model1
                 [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                 tail_sent0
                 tail_received0
                 client.CS.cs_model
             with
             (
               assert (initial.CS.model_control == CS.ControlNew);
               assert (initial.CS.model_config.CS.config_role == CS.ClientEndpoint);
               assert_norm (
                 CS.step_model initial (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
                 Some (CS.with_handshake_stage
                   initial
                   ({ initial.CS.model_handshake with CS.hs_start = Some start })
                   CS.HsStarted));
               assert (CS.step_model initial e0 ==
                 Some (CS.with_handshake_stage
                   initial
                   ({ initial.CS.model_handshake with CS.hs_start = Some start })
                   CS.HsStarted));
               assert (model1 ==
                 CS.with_handshake_stage
                   initial
                   ({ initial.CS.model_handshake with CS.hs_start = Some start })
                   CS.HsStarted);
               assert (model1.CS.model_control == CS.ControlHandshaking CS.HsStarted);
               assert (model1.CS.model_config == initial.CS.model_config);
               assert_norm (
                 TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                   model1
                   [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                   tail_sent0
                   tail_received0
                   client.CS.cs_model ==
                 (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
                   CS.legal_event model1 e1 /\
                   CS.step_model model1 e1 == Some model2 /\
                   CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
                   Seq.equal
                     tail_sent0
                     (B.append delta_sent1 tail_sent1) /\
                   Seq.equal
                     tail_received0
                     (B.append delta_received1 tail_received1) /\
                   TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                     model2
                     [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                     tail_sent1
                     tail_received1
                     client.CS.cs_model));
               eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
                 CS.legal_event model1 e1 /\
                 CS.step_model model1 e1 == Some model2 /\
                 CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
                 Seq.equal
                   tail_sent0
                   (B.append delta_sent1 tail_sent1) /\
                 Seq.equal
                   tail_received0
                   (B.append delta_received1 tail_received1) /\
                 TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                   model2
                   [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                   tail_sent1
                   tail_received1
                   client.CS.cs_model
               with
               (
                 assert (e1 == CS.ConnNetworkEvent msg);
                 assert (msg.CL.message_value == M.TlsChangeCipherSpec);
                 assert_norm (CS.step_model model1 e1 == Some model1);
                 assert (model2 == model1);
                 assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                 assert (client_application_progress_rank client.CS.cs_model == 0);
                 lemma_client_application_progress_rank_replay_lower_bound
                   model2
                   [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                   tail_sent1
                   tail_received1
                   client.CS.cs_model;
                 assert (client_application_progress_rank model2 == 15);
                 assert (FStar.List.Tot.length
                   [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15] == 14);
                 assert False
               )
             )
           | _ ->
             ());
        assert (~ (exists m.
          e1 == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec));
        assert (client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          e1 ::
          [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
      )
    )

let lemma_client_no_tail_second_event_client_hello_clean
    (client:CS.connection_state)
    : Lemma
        (requires
          CD.client_driver_application_ready client /\
          FStar.List.Tot.length client.CS.cs_event_log == 16)
        (ensures
          exists start ch rest.
            client.CS.cs_event_log ==
              CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              rest)
=
    lemma_client_no_tail_second_event_not_ccs client;
    lemma_client_no_tail_second_event_client_hello client

let lemma_client_no_tail_third_event_server_hello_clean
    (client:CS.connection_state)
    : Lemma
        (requires
          CD.client_driver_application_ready client /\
          FStar.List.Tot.length client.CS.cs_event_log == 16)
        (ensures
          exists start ch sh rest.
            client.CS.cs_event_log ==
              CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ServerHello sh);
              }) ::
              rest)
=
    lemma_client_no_tail_log_spine16 client;
    lemma_client_no_tail_second_event_client_hello_clean client;
    eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
      client.CS.cs_event_log ==
        [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
    with
    (
      eliminate exists start ch rest_after_ch.
        client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          rest_after_ch
      with
      (
        assert (client.CS.cs_event_log ==
          e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
        assert (client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          rest_after_ch);
        assert (e0 == CS.ConnLocalEvent (CS.LocalStartHandshake start));
        assert (e1 == CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }));
        assert (rest_after_ch == [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);

        assert (CT.client_end_to_end_invariant client);
        assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client);
        lemma_client_application_ready_progress_rank_zero client;
        let initial = CS.initial_model client.CS.cs_model.CS.model_config in
        assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          initial
          client.CS.cs_event_log
          client.CS.cs_wire_log.CL.raw_sent
          client.CS.cs_wire_log.CL.raw_received
          client.CS.cs_model);
        assert (client.CS.cs_event_log ==
          e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
        assert_norm (
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            initial
            (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
            client.CS.cs_wire_log.CL.raw_sent
            client.CS.cs_wire_log.CL.raw_received
            client.CS.cs_model ==
          (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
            CS.legal_event initial e0 /\
            CS.step_model initial e0 == Some model1 /\
            CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
            Seq.equal
              client.CS.cs_wire_log.CL.raw_sent
              (B.append delta_sent0 tail_sent0) /\
            Seq.equal
              client.CS.cs_wire_log.CL.raw_received
              (B.append delta_received0 tail_received0) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model1
              [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent0
              tail_received0
              client.CS.cs_model));
        eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            client.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            client.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent0
            tail_received0
            client.CS.cs_model
        with
        (
          assert (initial.CS.model_control == CS.ControlNew);
          assert (initial.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert_norm (
            CS.step_model initial (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
            Some (CS.with_handshake_stage
              initial
              ({ initial.CS.model_handshake with CS.hs_start = Some start })
              CS.HsStarted));
          assert (CS.step_model initial e0 ==
            Some (CS.with_handshake_stage
              initial
              ({ initial.CS.model_handshake with CS.hs_start = Some start })
              CS.HsStarted));
          assert (model1 ==
            CS.with_handshake_stage
              initial
              ({ initial.CS.model_handshake with CS.hs_start = Some start })
              CS.HsStarted);
          assert (model1.CS.model_control == CS.ControlHandshaking CS.HsStarted);
          assert (model1.CS.model_config == initial.CS.model_config);

          assert_norm (
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model1
              [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent0
              tail_received0
              client.CS.cs_model ==
            (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
              CS.legal_event model1 e1 /\
              CS.step_model model1 e1 == Some model2 /\
              CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
              Seq.equal
                tail_sent0
                (B.append delta_sent1 tail_sent1) /\
              Seq.equal
                tail_received0
                (B.append delta_received1 tail_received1) /\
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent1
                tail_received1
                client.CS.cs_model));
          eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent1
              tail_received1
              client.CS.cs_model
          with
          (
            assert_norm (
              CS.step_model
                model1
                (CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                })) ==
              Some (CS.with_handshake_stage
                model1
                (CS.append_handshake_to_transcript
                  ({ model1.CS.model_handshake with
                      CS.hs_client_hello = Some ch;
                      CS.hs_buffers =
                        { model1.CS.model_handshake.CS.hs_buffers with
                            CS.hb_client_hello_bytes =
                              TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                        };
                  })
                  (M.ClientHello ch))
                CS.HsClientHelloSent));
            assert (CS.step_model model1 e1 ==
              Some (CS.with_handshake_stage
                model1
                (CS.append_handshake_to_transcript
                  ({ model1.CS.model_handshake with
                      CS.hs_client_hello = Some ch;
                      CS.hs_buffers =
                        { model1.CS.model_handshake.CS.hs_buffers with
                            CS.hb_client_hello_bytes =
                              TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                        };
                  })
                  (M.ClientHello ch))
                CS.HsClientHelloSent));
            assert (model2 ==
              CS.with_handshake_stage
                model1
                (CS.append_handshake_to_transcript
                  ({ model1.CS.model_handshake with
                      CS.hs_client_hello = Some ch;
                      CS.hs_buffers =
                        { model1.CS.model_handshake.CS.hs_buffers with
                            CS.hb_client_hello_bytes =
                              TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                        };
                  })
                  (M.ClientHello ch))
                CS.HsClientHelloSent);
            assert (model2.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent);
            assert (model2.CS.model_config == model1.CS.model_config);
            assert (model2.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert (model2.CS.model_handshake.CS.hs_keys ==
              model1.CS.model_handshake.CS.hs_keys);
            assert (model1.CS.model_handshake.CS.hs_keys ==
              initial.CS.model_handshake.CS.hs_keys);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
            lemma_client_hs_client_hello_sent_empty_keys_progress_rank model2;
            assert (client_application_progress_rank model2 == 14);

            assert_norm (
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent1
                tail_received1
                client.CS.cs_model ==
              (exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
                CS.legal_event model2 e2 /\
                CS.step_model model2 e2 == Some model3 /\
                CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
                Seq.equal
                  tail_sent1
                  (B.append delta_sent2 tail_sent2) /\
                Seq.equal
                  tail_received1
                  (B.append delta_received2 tail_received2) /\
                TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                  model3
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                  tail_sent2
                  tail_received2
                  client.CS.cs_model));
            eliminate exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
              CS.legal_event model2 e2 /\
              CS.step_model model2 e2 == Some model3 /\
              CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
              Seq.equal
                tail_sent1
                (B.append delta_sent2 tail_sent2) /\
              Seq.equal
                tail_received1
                (B.append delta_received2 tail_received2) /\
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model3
                [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent2
                tail_received2
                client.CS.cs_model
            with
            (
              match e2 with
              | CS.ConnLocalEvent local ->
                (match local with
                 | CS.LocalFail err ->
                   assert (e2 == CS.ConnLocalEvent (CS.LocalFail err));
                   assert_norm (
                     CS.step_model model2 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                     Some (CS.fail_model model2 err));
                   assert (model3.CS.model_control == CS.ControlFailed err);
                   lemma_conn_events_raw_replay_from_failed_results_failed
                     model3
                     [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                     tail_sent2
                     tail_received2
                     client.CS.cs_model;
                   assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
                   assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert False
                 | CS.LocalInstallTrafficKeys install ->
                   lemma_client_hs_client_hello_sent_install_traffic_keys_illegal model2 install;
                   assert False
                 | CS.LocalInstallTrafficKeysForRole role_install ->
                   lemma_client_hs_client_hello_sent_install_traffic_keys_for_role_illegal model2 role_install;
                   assert False
                 | _ ->
                   lemma_client_hs_client_hello_sent_local_event_step_none model2 local;
                   assert (CS.step_model model2 e2 == None);
                   assert False)
              | CS.ConnNetworkEvent msg ->
                (match msg.CL.message_value with
                 | M.TlsAlert alert ->
                   assert (e2 == CS.ConnNetworkEvent msg);
                   assert_norm (
                     CS.step_model model2 (CS.ConnNetworkEvent msg) ==
                     Some (CS.fail_model model2 (T.AlertError alert)));
                   assert (CS.step_model model2 e2 ==
                     Some (CS.fail_model model2 (T.AlertError alert)));
                   assert (model3.CS.model_control == CS.ControlFailed (T.AlertError alert));
                   lemma_conn_events_raw_replay_from_failed_results_failed
                     model3
                     [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                     tail_sent2
                     tail_received2
                     client.CS.cs_model;
                   assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
                   assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert False
                 | M.TlsChangeCipherSpec ->
                   assert (e2 == CS.ConnNetworkEvent msg);
                   assert (msg.CL.message_value == M.TlsChangeCipherSpec);
                   assert_norm (CS.step_model model2 (CS.ConnNetworkEvent msg) == Some model2);
                   assert (CS.step_model model2 e2 == Some model2);
                   assert (model3 == model2);
                   assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert (client_application_progress_rank client.CS.cs_model == 0);
                   lemma_client_application_progress_rank_replay_lower_bound
                     model3
                     [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                     tail_sent2
                     tail_received2
                     client.CS.cs_model;
                   assert (client_application_progress_rank model3 == 14);
                   assert_norm (FStar.List.Tot.length
                     [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15] == 13);
                   assert False
                 | M.TlsHandshake handshake_msg ->
                   (match msg.CL.message_direction, handshake_msg with
                    | CL.Received, M.ServerHello sh ->
                      assert (e2 == CS.ConnNetworkEvent ({
                        CL.message_direction = CL.Received;
                        CL.message_value = M.TlsHandshake (M.ServerHello sh);
                      }));
                      assert (client.CS.cs_event_log ==
                        CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                        CS.ConnNetworkEvent ({
                          CL.message_direction = CL.Sent;
                          CL.message_value = M.TlsHandshake (M.ClientHello ch);
                        }) ::
                        CS.ConnNetworkEvent ({
                          CL.message_direction = CL.Received;
                          CL.message_value = M.TlsHandshake (M.ServerHello sh);
                        }) ::
                        [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
                    | CL.Received, M.HelloRetryRequest ->
                      assert (e2 == CS.ConnNetworkEvent msg);
                      assert (msg.CL.message_direction == CL.Received);
                      assert (msg.CL.message_value == M.TlsHandshake M.HelloRetryRequest);
                      assert (msg == {
                        CL.message_direction = CL.Received;
                        CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                      });
                      assert_norm (
                        CS.step_model
                          model2
                          (CS.ConnNetworkEvent ({
                            CL.message_direction = CL.Received;
                            CL.message_value = M.TlsHandshake M.HelloRetryRequest;
                          })) ==
                        Some (CS.fail_model model2 T.HelloRetryRequestRejected));
                      assert (CS.step_model model2 e2 ==
                        Some (CS.fail_model model2 T.HelloRetryRequestRejected));
                      assert (model3.CS.model_control == CS.ControlFailed T.HelloRetryRequestRejected);
                      lemma_conn_events_raw_replay_from_failed_results_failed
                        model3
                        [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                        tail_sent2
                        tail_received2
                        client.CS.cs_model;
                      assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
                      assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                      assert False
                    | _, _ ->
                      lemma_client_hs_client_hello_sent_non_server_hello_network_step_none model2 msg;
                      assert (CS.step_model model2 e2 == None);
                      assert False)
                 | M.TlsApplicationData _ ->
                   lemma_client_hs_client_hello_sent_non_server_hello_network_step_none model2 msg;
                   assert (CS.step_model model2 e2 == None);
                   assert False
                 | M.TlsIgnoredPostHandshake _ ->
                   lemma_client_hs_client_hello_sent_non_server_hello_network_step_none model2 msg;
                   assert (CS.step_model model2 e2 == None);
                   assert False
                 | M.TlsKeyUpdate _ ->
                   lemma_client_hs_client_hello_sent_non_server_hello_network_step_none model2 msg;
                   assert (CS.step_model model2 e2 == None);
                   assert False)
            )
           )
         )
       )
     )

let lemma_client_no_tail_fourth_event_derive_shared_secret_clean
    (client:CS.connection_state)
    : Lemma
        (requires
          CD.client_driver_application_ready client /\
          FStar.List.Tot.length client.CS.cs_event_log == 16)
        (ensures
          exists start ch sh client_shared rest.
            client.CS.cs_event_log ==
              CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ServerHello sh);
              }) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
              rest)
=
    lemma_client_no_tail_log_spine16 client;
    lemma_client_no_tail_third_event_server_hello_clean client;
    eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
      client.CS.cs_event_log ==
        [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
    with
    (
      eliminate exists start ch sh rest_after_sh.
        client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) ::
          rest_after_sh
      with
      (
        assert (client.CS.cs_event_log ==
          e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
        assert (client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) ::
          rest_after_sh);
        assert (e0 == CS.ConnLocalEvent (CS.LocalStartHandshake start));
        assert (e1 == CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }));
        assert (e2 == CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }));
        assert (rest_after_sh == [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);

        assert (CT.client_end_to_end_invariant client);
        assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client);
        lemma_client_application_ready_progress_rank_zero client;
        let initial = CS.initial_model client.CS.cs_model.CS.model_config in
        assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          initial
          client.CS.cs_event_log
          client.CS.cs_wire_log.CL.raw_sent
          client.CS.cs_wire_log.CL.raw_received
          client.CS.cs_model);
        assert_norm (
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            initial
            (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
            client.CS.cs_wire_log.CL.raw_sent
            client.CS.cs_wire_log.CL.raw_received
            client.CS.cs_model ==
          (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
            CS.legal_event initial e0 /\
            CS.step_model initial e0 == Some model1 /\
            CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
            Seq.equal
              client.CS.cs_wire_log.CL.raw_sent
              (B.append delta_sent0 tail_sent0) /\
            Seq.equal
              client.CS.cs_wire_log.CL.raw_received
              (B.append delta_received0 tail_received0) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model1
              [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent0
              tail_received0
              client.CS.cs_model));
        eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            client.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            client.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent0
            tail_received0
            client.CS.cs_model
        with
        (
          assert (initial.CS.model_control == CS.ControlNew);
          assert (initial.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert_norm (
            CS.step_model initial (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
            Some (CS.with_handshake_stage
              initial
              ({ initial.CS.model_handshake with CS.hs_start = Some start })
              CS.HsStarted));
          assert (CS.step_model initial e0 ==
            Some (CS.with_handshake_stage
              initial
              ({ initial.CS.model_handshake with CS.hs_start = Some start })
              CS.HsStarted));
          assert (model1 ==
            CS.with_handshake_stage
              initial
              ({ initial.CS.model_handshake with CS.hs_start = Some start })
              CS.HsStarted);
          assert (model1.CS.model_control == CS.ControlHandshaking CS.HsStarted);
          assert (model1.CS.model_config == initial.CS.model_config);

          assert_norm (
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model1
              [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent0
              tail_received0
              client.CS.cs_model ==
            (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
              CS.legal_event model1 e1 /\
              CS.step_model model1 e1 == Some model2 /\
              CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
              Seq.equal
                tail_sent0
                (B.append delta_sent1 tail_sent1) /\
              Seq.equal
                tail_received0
                (B.append delta_received1 tail_received1) /\
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent1
                tail_received1
                client.CS.cs_model));
          eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent1
              tail_received1
              client.CS.cs_model
          with
          (
            assert_norm (
              CS.step_model
                model1
                (CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                })) ==
              Some (CS.with_handshake_stage
                model1
                (CS.append_handshake_to_transcript
                  ({ model1.CS.model_handshake with
                      CS.hs_client_hello = Some ch;
                      CS.hs_buffers =
                        { model1.CS.model_handshake.CS.hs_buffers with
                            CS.hb_client_hello_bytes =
                              TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                        };
                  })
                  (M.ClientHello ch))
                CS.HsClientHelloSent));
            assert (CS.step_model model1 e1 ==
              Some (CS.with_handshake_stage
                model1
                (CS.append_handshake_to_transcript
                  ({ model1.CS.model_handshake with
                      CS.hs_client_hello = Some ch;
                      CS.hs_buffers =
                        { model1.CS.model_handshake.CS.hs_buffers with
                            CS.hb_client_hello_bytes =
                              TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                        };
                  })
                  (M.ClientHello ch))
                CS.HsClientHelloSent));
            assert (model2 ==
              CS.with_handshake_stage
                model1
                (CS.append_handshake_to_transcript
                  ({ model1.CS.model_handshake with
                      CS.hs_client_hello = Some ch;
                      CS.hs_buffers =
                        { model1.CS.model_handshake.CS.hs_buffers with
                            CS.hb_client_hello_bytes =
                              TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                        };
                  })
                  (M.ClientHello ch))
                CS.HsClientHelloSent);
            assert (model2.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent);
            assert (model2.CS.model_config == model1.CS.model_config);
            assert (model2.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert (model2.CS.model_handshake.CS.hs_keys ==
              model1.CS.model_handshake.CS.hs_keys);
            assert (model1.CS.model_handshake.CS.hs_keys ==
              initial.CS.model_handshake.CS.hs_keys);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_master_secret == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
            assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);

            assert_norm (
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent1
                tail_received1
                client.CS.cs_model ==
              (exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
                CS.legal_event model2 e2 /\
                CS.step_model model2 e2 == Some model3 /\
                CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
                Seq.equal
                  tail_sent1
                  (B.append delta_sent2 tail_sent2) /\
                Seq.equal
                  tail_received1
                  (B.append delta_received2 tail_received2) /\
                TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                  model3
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                  tail_sent2
                  tail_received2
                  client.CS.cs_model));
            eliminate exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
              CS.legal_event model2 e2 /\
              CS.step_model model2 e2 == Some model3 /\
              CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
              Seq.equal
                tail_sent1
                (B.append delta_sent2 tail_sent2) /\
              Seq.equal
                tail_received1
                (B.append delta_received2 tail_received2) /\
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model3
                [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent2
                tail_received2
                client.CS.cs_model
            with
            (
              assert_norm (
                CS.step_model
                  model2
                  (CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  })) ==
                Some (CS.with_handshake_stage
                  model2
                  (CS.append_handshake_to_transcript
                    ({ model2.CS.model_handshake with
                        CS.hs_server_hello = Some sh;
                        CS.hs_buffers =
                          { model2.CS.model_handshake.CS.hs_buffers with
                              CS.hb_server_hello_bytes =
                                TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh);
                          };
                    })
                    (M.ServerHello sh))
                  CS.HsServerHelloReceived));
              assert (CS.step_model model2 e2 ==
                Some (CS.with_handshake_stage
                  model2
                  (CS.append_handshake_to_transcript
                    ({ model2.CS.model_handshake with
                        CS.hs_server_hello = Some sh;
                        CS.hs_buffers =
                          { model2.CS.model_handshake.CS.hs_buffers with
                              CS.hb_server_hello_bytes =
                                TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh);
                          };
                    })
                    (M.ServerHello sh))
                  CS.HsServerHelloReceived));
              assert (model3 ==
                CS.with_handshake_stage
                  model2
                  (CS.append_handshake_to_transcript
                    ({ model2.CS.model_handshake with
                        CS.hs_server_hello = Some sh;
                        CS.hs_buffers =
                          { model2.CS.model_handshake.CS.hs_buffers with
                              CS.hb_server_hello_bytes =
                                TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh);
                          };
                    })
                    (M.ServerHello sh))
                  CS.HsServerHelloReceived);
              assert (model3.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
              assert (model3.CS.model_config == model2.CS.model_config);
              assert (model3.CS.model_config.CS.config_role == CS.ClientEndpoint);
              assert (model3.CS.model_handshake.CS.hs_keys ==
                model2.CS.model_handshake.CS.hs_keys);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_master_secret == None);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
              assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
              lemma_client_hs_server_hello_received_empty_keys_progress_rank model3;
              assert (client_application_progress_rank model3 == 13);

              assert_norm (
                TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                  model3
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                  tail_sent2
                  tail_received2
                  client.CS.cs_model ==
                (exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
                  CS.legal_event model3 e3 /\
                  CS.step_model model3 e3 == Some model4 /\
                  CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
                  Seq.equal
                    tail_sent2
                    (B.append delta_sent3 tail_sent3) /\
                  Seq.equal
                    tail_received2
                    (B.append delta_received3 tail_received3) /\
                  TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                    model4
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                    tail_sent3
                    tail_received3
                    client.CS.cs_model));
              eliminate exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
                CS.legal_event model3 e3 /\
                CS.step_model model3 e3 == Some model4 /\
                CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
                Seq.equal
                  tail_sent2
                  (B.append delta_sent3 tail_sent3) /\
                Seq.equal
                  tail_received2
                  (B.append delta_received3 tail_received3) /\
                TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                  model4
                  [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                  tail_sent3
                  tail_received3
                  client.CS.cs_model
              with
              (
                match e3 with
                | CS.ConnLocalEvent local ->
                  (match local with
                   | CS.LocalFail err ->
                     assert (e3 == CS.ConnLocalEvent (CS.LocalFail err));
                     assert_norm (
                       CS.step_model model3 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                       Some (CS.fail_model model3 err));
                     assert (model4.CS.model_control == CS.ControlFailed err);
                     lemma_conn_events_raw_replay_from_failed_results_failed
                       model4
                       [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                       tail_sent3
                       tail_received3
                       client.CS.cs_model;
                     assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
                     assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                     assert False
                   | CS.LocalDeriveSharedSecret client_shared ->
                     assert (e3 == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared));
                     assert (client.CS.cs_event_log ==
                       CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                       CS.ConnNetworkEvent ({
                         CL.message_direction = CL.Sent;
                         CL.message_value = M.TlsHandshake (M.ClientHello ch);
                       }) ::
                       CS.ConnNetworkEvent ({
                         CL.message_direction = CL.Received;
                         CL.message_value = M.TlsHandshake (M.ServerHello sh);
                       }) ::
                       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
                       [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
                   | CS.LocalInstallTrafficKeys install ->
                     lemma_client_hs_server_hello_received_empty_keys_install_traffic_keys_illegal
                       model3
                       install;
                     assert False
                   | CS.LocalInstallTrafficKeysForRole role_install ->
                     lemma_client_hs_server_hello_received_empty_keys_install_traffic_keys_for_role_illegal
                       model3
                       role_install;
                     assert False
                   | _ ->
                     lemma_client_hs_server_hello_received_local_event_step_none model3 local;
                     assert (CS.step_model model3 e3 == None);
                     assert False)
                | CS.ConnNetworkEvent msg ->
                  (match msg.CL.message_value with
                   | M.TlsAlert alert ->
                     assert (e3 == CS.ConnNetworkEvent msg);
                     assert_norm (
                       CS.step_model model3 (CS.ConnNetworkEvent msg) ==
                       Some (CS.fail_model model3 (T.AlertError alert)));
                     assert (CS.step_model model3 e3 ==
                       Some (CS.fail_model model3 (T.AlertError alert)));
                     assert (model4.CS.model_control == CS.ControlFailed (T.AlertError alert));
                     lemma_conn_events_raw_replay_from_failed_results_failed
                       model4
                       [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                       tail_sent3
                       tail_received3
                       client.CS.cs_model;
                     assert (CS.ControlFailed? client.CS.cs_model.CS.model_control);
                     assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                     assert False
                   | M.TlsChangeCipherSpec ->
                     assert (e3 == CS.ConnNetworkEvent msg);
                     assert (msg.CL.message_value == M.TlsChangeCipherSpec);
                     assert_norm (CS.step_model model3 (CS.ConnNetworkEvent msg) == Some model3);
                     assert (CS.step_model model3 e3 == Some model3);
                     assert (model4 == model3);
                     assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                     assert (client_application_progress_rank client.CS.cs_model == 0);
                     lemma_client_application_progress_rank_replay_lower_bound
                       model4
                       [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                       tail_sent3
                       tail_received3
                       client.CS.cs_model;
                     assert (client_application_progress_rank model4 == 13);
                     assert_norm (FStar.List.Tot.length
                       [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15] == 12);
                     assert False
                   | M.TlsHandshake handshake_msg ->
                     (match msg.CL.message_direction, handshake_msg with
                      | CL.Received, M.EncryptedExtensions ee ->
                        assert (e3 == CS.ConnNetworkEvent ({
                          CL.message_direction = CL.Received;
                          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                        }));
                        lemma_client_hs_server_hello_received_empty_keys_encrypted_extensions_illegal
                          model3
                          ee;
                        assert False
                      | _, _ ->
                        lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
                          model3
                          msg;
                        assert (CS.step_model model3 e3 == None);
                        assert False)
                   | M.TlsApplicationData _ ->
                     lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
                       model3
                       msg;
                     assert (CS.step_model model3 e3 == None);
                     assert False
                   | M.TlsIgnoredPostHandshake _ ->
                     lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
                       model3
                       msg;
                     assert (CS.step_model model3 e3 == None);
                     assert False
                   | M.TlsKeyUpdate _ ->
                     lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
                       model3
                       msg;
                     assert (CS.step_model model3 e3 == None);
                     assert False)
              )
            )
           )
         )
       )
     )

#push-options "--z3rlimit 10"
let lemma_client_no_tail_model4_witness
            (client:CS.connection_state)
            : Lemma
                (requires
                  CD.client_driver_application_ready client /\
                  FStar.List.Tot.length client.CS.cs_event_log == 16)
                (ensures
                  exists start ch sh client_shared e4 rest model4 tail_sent tail_received.
                    client.CS.cs_event_log ==
                      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                      CS.ConnNetworkEvent ({
                        CL.message_direction = CL.Sent;
                        CL.message_value = M.TlsHandshake (M.ClientHello ch);
                      }) ::
                      CS.ConnNetworkEvent ({
                        CL.message_direction = CL.Received;
                        CL.message_value = M.TlsHandshake (M.ServerHello sh);
                      }) ::
                      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
                      e4 ::
                      rest /\
                    FStar.List.Tot.length rest == 11 /\
                    model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
                    model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
                    Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
                    Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
                    model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
                    model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
                    model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
                    model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
                    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model /\
                    client_application_progress_rank client.CS.cs_model == 0)
=
            lemma_client_no_tail_log_spine16 client;
            lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
            eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
              client.CS.cs_event_log ==
                [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            with
            (
              eliminate exists start ch sh client_shared rest_after_derive.
                client.CS.cs_event_log ==
                  CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
                  rest_after_derive
              with
              (
                assert (client.CS.cs_event_log ==
                  e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
                assert (e0 == CS.ConnLocalEvent (CS.LocalStartHandshake start));
                assert (e1 == CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                }));
                assert (e2 == CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ServerHello sh);
                }));
                assert (e3 == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared));
                assert (rest_after_derive == [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);

                assert (CT.client_end_to_end_invariant client);
                assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent client);
                lemma_client_application_ready_progress_rank_zero client;
                let initial = CS.initial_model client.CS.cs_model.CS.model_config in
                assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                  initial
                  client.CS.cs_event_log
                  client.CS.cs_wire_log.CL.raw_sent
                  client.CS.cs_wire_log.CL.raw_received
                  client.CS.cs_model);
                assert_norm (
                  TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                    initial
                    (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
                    client.CS.cs_wire_log.CL.raw_sent
                    client.CS.cs_wire_log.CL.raw_received
                    client.CS.cs_model ==
                  (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
                    CS.legal_event initial e0 /\
                    CS.step_model initial e0 == Some model1 /\
                    CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
                    Seq.equal
                      client.CS.cs_wire_log.CL.raw_sent
                      (B.append delta_sent0 tail_sent0) /\
                    Seq.equal
                      client.CS.cs_wire_log.CL.raw_received
                      (B.append delta_received0 tail_received0) /\
                    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                      model1
                      [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                      tail_sent0
                      tail_received0
                      client.CS.cs_model));
                eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
                  CS.legal_event initial e0 /\
                  CS.step_model initial e0 == Some model1 /\
                  CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
                  Seq.equal
                    client.CS.cs_wire_log.CL.raw_sent
                    (B.append delta_sent0 tail_sent0) /\
                  Seq.equal
                    client.CS.cs_wire_log.CL.raw_received
                    (B.append delta_received0 tail_received0) /\
                  TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                    model1
                    [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                    tail_sent0
                    tail_received0
                    client.CS.cs_model
                with
                (
                  assert (initial.CS.model_control == CS.ControlNew);
                  assert (initial.CS.model_config.CS.config_role == CS.ClientEndpoint);
                  assert_norm (
                    CS.step_model initial (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
                    Some (CS.with_handshake_stage
                      initial
                      ({ initial.CS.model_handshake with CS.hs_start = Some start })
                      CS.HsStarted));
                  assert (model1 ==
                    CS.with_handshake_stage
                      initial
                      ({ initial.CS.model_handshake with CS.hs_start = Some start })
                      CS.HsStarted);

                  assert_norm (
                    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                      model1
                      [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                      tail_sent0
                      tail_received0
                      client.CS.cs_model ==
                    (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
                      CS.legal_event model1 e1 /\
                      CS.step_model model1 e1 == Some model2 /\
                      CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
                      Seq.equal tail_sent0 (B.append delta_sent1 tail_sent1) /\
                      Seq.equal tail_received0 (B.append delta_received1 tail_received1) /\
                      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                        model2
                        [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                        tail_sent1
                        tail_received1
                        client.CS.cs_model));
                  eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
                    CS.legal_event model1 e1 /\
                    CS.step_model model1 e1 == Some model2 /\
                    CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
                    Seq.equal tail_sent0 (B.append delta_sent1 tail_sent1) /\
                    Seq.equal tail_received0 (B.append delta_received1 tail_received1) /\
                    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                      model2
                      [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                      tail_sent1
                      tail_received1
                      client.CS.cs_model
                  with
                  (
                    assert_norm (
                      CS.step_model model1
                        (CS.ConnNetworkEvent ({
                          CL.message_direction = CL.Sent;
                          CL.message_value = M.TlsHandshake (M.ClientHello ch);
                        })) ==
                      Some (CS.with_handshake_stage
                        model1
                        (CS.append_handshake_to_transcript
                          ({ model1.CS.model_handshake with
                              CS.hs_client_hello = Some ch;
                              CS.hs_buffers =
                                { model1.CS.model_handshake.CS.hs_buffers with
                                    CS.hb_client_hello_bytes =
                                      TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                                };
                          })
                          (M.ClientHello ch))
                        CS.HsClientHelloSent));
                    assert (model2 ==
                      CS.with_handshake_stage
                        model1
                        (CS.append_handshake_to_transcript
                          ({ model1.CS.model_handshake with
                              CS.hs_client_hello = Some ch;
                              CS.hs_buffers =
                                { model1.CS.model_handshake.CS.hs_buffers with
                                    CS.hb_client_hello_bytes =
                                      TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                                };
                          })
                          (M.ClientHello ch))
                        CS.HsClientHelloSent);
                    assert (model2.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent);
                    assert (model2.CS.model_config.CS.config_role == CS.ClientEndpoint);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_master_secret == None);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
                    assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);

                    assert_norm (
                      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                        model2
                        [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                        tail_sent1
                        tail_received1
                        client.CS.cs_model ==
                      (exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
                        CS.legal_event model2 e2 /\
                        CS.step_model model2 e2 == Some model3 /\
                        CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
                        Seq.equal tail_sent1 (B.append delta_sent2 tail_sent2) /\
                        Seq.equal tail_received1 (B.append delta_received2 tail_received2) /\
                        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                          model3
                          [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                          tail_sent2
                          tail_received2
                          client.CS.cs_model));
                    eliminate exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
                      CS.legal_event model2 e2 /\
                      CS.step_model model2 e2 == Some model3 /\
                      CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
                      Seq.equal tail_sent1 (B.append delta_sent2 tail_sent2) /\
                      Seq.equal tail_received1 (B.append delta_received2 tail_received2) /\
                      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                        model3
                        [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                        tail_sent2
                        tail_received2
                        client.CS.cs_model
                    with
                    (
                      assert_norm (
                        CS.step_model model2
                          (CS.ConnNetworkEvent ({
                            CL.message_direction = CL.Received;
                            CL.message_value = M.TlsHandshake (M.ServerHello sh);
                          })) ==
                        Some (CS.with_handshake_stage
                          model2
                          (CS.append_handshake_to_transcript
                            ({ model2.CS.model_handshake with
                                CS.hs_server_hello = Some sh;
                                CS.hs_buffers =
                                  { model2.CS.model_handshake.CS.hs_buffers with
                                      CS.hb_server_hello_bytes =
                                        TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh);
                                  };
                            })
                            (M.ServerHello sh))
                          CS.HsServerHelloReceived));
                      assert (model3 ==
                        CS.with_handshake_stage
                          model2
                          (CS.append_handshake_to_transcript
                            ({ model2.CS.model_handshake with
                                CS.hs_server_hello = Some sh;
                                CS.hs_buffers =
                                  { model2.CS.model_handshake.CS.hs_buffers with
                                      CS.hb_server_hello_bytes =
                                        TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh);
                                  };
                            })
                            (M.ServerHello sh))
                          CS.HsServerHelloReceived);
                      assert (model3.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
                      assert (model3.CS.model_config.CS.config_role == CS.ClientEndpoint);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_master_secret == None);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
                      assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);

                      assert_norm (
                        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                          model3
                          [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                          tail_sent2
                          tail_received2
                          client.CS.cs_model ==
                        (exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
                          CS.legal_event model3 e3 /\
                          CS.step_model model3 e3 == Some model4 /\
                          CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
                          Seq.equal tail_sent2 (B.append delta_sent3 tail_sent3) /\
                          Seq.equal tail_received2 (B.append delta_received3 tail_received3) /\
                          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                            model4
                            [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                            tail_sent3
                            tail_received3
                            client.CS.cs_model));
                      eliminate exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
                        CS.legal_event model3 e3 /\
                        CS.step_model model3 e3 == Some model4 /\
                        CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
                        Seq.equal tail_sent2 (B.append delta_sent3 tail_sent3) /\
                        Seq.equal tail_received2 (B.append delta_received3 tail_received3) /\
                        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                          model4
                          [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                          tail_sent3
                          tail_received3
                          client.CS.cs_model
                      with
                      (
                        assert (
                          CS.step_model
                            model3
                            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
                          Some (CS.derive_shared_secret_model
                            model3
                            model3.CS.model_handshake
                            client_shared));
                        assert (model4 == CS.derive_shared_secret_model
                          model3
                          model3.CS.model_handshake
                          client_shared);
                        assert (model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
                        assert (model4.CS.model_config.CS.config_role == CS.ClientEndpoint);
                        assert (Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
                        assert (Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret);
                        assert (Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret);
                        assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
                        assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
                        assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
                        assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
                        let rest : list CS.conn_event =
                          [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15] in
                        assert_norm (FStar.List.Tot.length rest == 11);
                        assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                          model4
                          (e4 :: rest)
                          tail_sent3
                          tail_received3
                          client.CS.cs_model);
                        assert (client.CS.cs_event_log ==
                          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                          CS.ConnNetworkEvent ({
                            CL.message_direction = CL.Sent;
                            CL.message_value = M.TlsHandshake (M.ClientHello ch);
                          }) ::
                          CS.ConnNetworkEvent ({
                            CL.message_direction = CL.Received;
                            CL.message_value = M.TlsHandshake (M.ServerHello sh);
                          }) ::
                          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
                          e4 ::
                          rest)
                      )
                    )
                  )
                )
              )
            )
#pop-options

let lemma_client_no_tail_fifth_event_handshake_traffic_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            rest /\
          client_no_tail_handshake_traffic_install_event e4)
=
  lemma_client_no_tail_model4_witness client;
  eliminate exists start ch sh client_shared e4 rest model4 tail_sent tail_received.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      rest /\
    FStar.List.Tot.length rest == 11 /\
    model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
    model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
    Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
    Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
    Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
    model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
    model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
    model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
    model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model /\
    client_application_progress_rank client.CS.cs_model == 0
  with
  (
    lemma_client_post_derive_next_event_handshake_traffic_install
      model4
      e4
      rest
      tail_sent
      tail_received
      client.CS.cs_model;
    assert (client_no_tail_handshake_traffic_install_event e4)
  )
