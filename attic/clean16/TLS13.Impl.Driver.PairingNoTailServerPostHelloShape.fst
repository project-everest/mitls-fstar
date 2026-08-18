module TLS13.Impl.Driver.PairingNoTailServerPostHelloShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module CSL = TLS13.ConnectionState.Lemmas
module ListP = FStar.List.Tot.Properties
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSC = TLS13.Impl.Driver.PairingNoTailServerCleartextShape
module PNTSFShape = TLS13.Impl.Driver.PairingNoTailServerFlightShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PNTWHR = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module Seq = FStar.Seq
module SD = TLS13.Impl.Server.Driver
module ST = TLS13.Impl.Server.Types

#push-options ""

let lemma_not_conn_event_is_ccs_elim
  (ev:CS.conn_event)
  : Lemma
      (requires ~ (conn_event_is_ccs ev))
      (ensures
        ~ (exists m.
          ev == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec))
=
  match ev with
  | CS.ConnNetworkEvent m ->
    ()
  | CS.ConnLocalEvent _ ->
    ()

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_no_tail_post_server_hello_suffix_shape server)
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (FStar.List.Tot.length server.CS.cs_event_log == 16);
  eliminate exists client_start client_ch client_sh client_shared e4 e5 client_rest.
    client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
        }) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
        e4 ::
        e5 ::
        client_rest /\
    TLS13.Impl.Driver.PairingNoTailInversion.client_no_tail_handshake_traffic_install_event e4 /\
    TLS13.Impl.Driver.PairingNoTailInversion.client_no_tail_handshake_traffic_install_event e5
  with
  (
    eliminate exists server_ch selection server_shared server_sh server_rest.
      server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
          }) ::
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
          }) ::
          server_rest
    with
    (
      let server_ev0 = CS.ConnLocalEvent CS.LocalStartServer in
      let server_ev1 =
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) in
      let server_ev2 =
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
      let server_ev3 =
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
      let server_ev4 =
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        }) in
      let server_prefix : list CS.conn_event =
        server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [] in
      ListP.append_cons_l
        server_ev0
        (server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [])
        server_rest;
      ListP.append_cons_l
        server_ev1
        (server_ev2 :: server_ev3 :: server_ev4 :: [])
        server_rest;
      ListP.append_cons_l
        server_ev2
        (server_ev3 :: server_ev4 :: [])
        server_rest;
      ListP.append_cons_l
        server_ev3
        (server_ev4 :: [])
        server_rest;
      ListP.append_cons_l server_ev4 [] server_rest;
      ListP.append_nil_l server_rest;
      assert (FStar.List.Tot.append server_prefix server_rest ==
        server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
        server_rest);
      assert (server.CS.cs_event_log ==
        server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
        server_rest);
      assert (server_prefix ==
        PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh);
      ListP.append_length server_prefix server_rest;
      assert_norm
        (FStar.List.Tot.length
          (server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: []) == 5);
      assert (FStar.List.Tot.length server_prefix == 5);
      assert (
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              server_ch
              selection
              server_shared
              server_sh)
            server_rest);
      assert (FStar.List.Tot.length server_rest == 11);
      match server_rest with
      | e5 :: e6 :: rest ->
        assert (FStar.List.Tot.length rest == 9);
        assert (server_no_tail_post_server_hello_suffix_shape server)
      | _ ->
        assert False
    )
  )

let lemma_server_no_tail_no_ccs_post_server_hello_suffix_shape
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_no_ccs_application_ready_boundary server)
      (ensures server_no_tail_post_server_hello_suffix_shape server)
=
  PNTSS.lemma_server_no_tail_start_spine16 server;
  eliminate exists e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    server.CS.cs_event_log ==
      [ CS.ConnLocalEvent CS.LocalStartServer;
        e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ]
  with
  (
    assert (FStar.List.Tot.mem e1 server.CS.cs_event_log);
    assert (~ (conn_event_is_ccs e1));
    lemma_not_conn_event_is_ccs_elim e1;
    PNTSS.lemma_server_no_tail_second_event_client_hello_if_not_ccs16 server;
    eliminate exists ch rest1.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        rest1
    with
    (
      match rest1 with
      | e2' :: rest2 ->
        assert (server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          e2' ::
          rest2);
        assert_norm (FStar.List.Tot.mem e2'
          (CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          e2' ::
          rest2));
        assert (FStar.List.Tot.mem e2' server.CS.cs_event_log);
        assert (~ (conn_event_is_ccs e2'));
        lemma_not_conn_event_is_ccs_elim e2';
        PNTSC.lemma_server_no_tail_third_event_select_parameters_if_not_ccs16 server;
        eliminate exists ch0 selection rest2'.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch0);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest2'
        with
        (
          match rest2' with
          | e3' :: rest3 ->
            assert (server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch0);
              }) ::
              CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
              e3' ::
              rest3);
            assert_norm (FStar.List.Tot.mem e3'
              (CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch0);
              }) ::
              CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
              e3' ::
              rest3));
            assert (FStar.List.Tot.mem e3' server.CS.cs_event_log);
            assert (~ (conn_event_is_ccs e3'));
            lemma_not_conn_event_is_ccs_elim e3';
            PNTSC.lemma_server_no_tail_fourth_event_derive_shared_secret_if_not_ccs16 server;
            eliminate exists ch1 selection1 server_shared rest3'.
              server.CS.cs_event_log ==
                CS.ConnLocalEvent CS.LocalStartServer ::
                CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch1);
                }) ::
                CS.ConnLocalEvent (CS.LocalSelectServerParameters selection1) ::
                CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                rest3'
            with
            (
              match rest3' with
              | e4' :: rest4 ->
                assert (server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch1);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection1) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                  e4' ::
                  rest4);
                assert_norm (FStar.List.Tot.mem e4'
                  (CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch1);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection1) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                  e4' ::
                  rest4));
                assert (FStar.List.Tot.mem e4' server.CS.cs_event_log);
                assert (~ (conn_event_is_ccs e4'));
                lemma_not_conn_event_is_ccs_elim e4';
                PNTSC.lemma_server_no_tail_fifth_event_server_hello_if_not_ccs16 server;
                eliminate exists ch2 selection2 server_shared2 sh rest5.
                  server.CS.cs_event_log ==
                    CS.ConnLocalEvent CS.LocalStartServer ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch2);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection2) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared2) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }) ::
                    rest5
                with
                (
                  let server_prefix =
                    PWSeg.server_cleartext_handshake_prefix_events
                      ch2
                      selection2
                      server_shared2
                      sh in
                  ListP.append_cons_l
                    (CS.ConnLocalEvent CS.LocalStartServer)
                    (CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch2);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection2) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared2) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }) ::
                    [])
                    rest5;
                  ListP.append_cons_l
                    (CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch2);
                    }))
                    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection2) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared2) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }) ::
                    [])
                    rest5;
                  ListP.append_cons_l
                    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection2))
                    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared2) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }) ::
                    [])
                    rest5;
                  ListP.append_cons_l
                    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared2))
                    (CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }) ::
                    [])
                    rest5;
                  ListP.append_cons_l
                    (CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }))
                    []
                    rest5;
                  ListP.append_nil_l rest5;
                  assert (server.CS.cs_event_log ==
                    FStar.List.Tot.append server_prefix rest5);
                  ListP.append_length server_prefix rest5;
                  assert_norm (FStar.List.Tot.length
                    (CS.ConnLocalEvent CS.LocalStartServer ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch2);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection2) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared2) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }) ::
                    []) == 5);
                  assert (FStar.List.Tot.length server_prefix == 5);
                  assert (FStar.List.Tot.length rest5 == 11);
                  match rest5 with
                  | e5' :: e6' :: rest ->
                    assert (FStar.List.Tot.length rest == 9);
                    assert (server_no_tail_post_server_hello_suffix_shape server)
                  | _ ->
                    assert False
                )
              | [] ->
                assert False
            )
          | [] ->
            assert False
        )
      | [] ->
        assert False
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape_with_start_spine16
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        server_no_tail_post_server_hello_suffix_shape_with_start_spine16
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_server_no_tail_handshake_install_event_direction_cases
  (ev:CS.conn_event)
  : Lemma
      (requires PNI.server_no_tail_handshake_traffic_install_event ev)
      (ensures
        PNTSS.server_no_tail_handshake_write_install_event ev \/
        PNTSS.server_no_tail_handshake_read_install_event ev)
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    (match role_install.CS.install_payload.CS.install_direction with
     | CS.TrafficWrite -> ()
     | CS.TrafficRead -> ())
  | _ ->
    assert False

let lemma_server_post_first_install_direction_shape
  (model5 model6:CS.connection_model)
  (e5:CS.conn_event)
  : Lemma
      (requires
        model5.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model5.CS.model_handshake.CS.hs_certificate == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        PNI.server_no_tail_handshake_traffic_install_event e5 /\
        CS.step_model model5 e5 == Some model6)
      (ensures
        model6.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model6.CS.model_handshake.CS.hs_certificate == None /\
        model6.CS.model_handshake.CS.hs_certificate_verify == None /\
        model6.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        (PNTSS.server_no_tail_handshake_write_install_event e5 ==>
          Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
          None? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic) /\
        (PNTSS.server_no_tail_handshake_read_install_event e5 ==>
          None? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
          Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic))
=
  match e5 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    let install = role_install.CS.install_payload in
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (
      CS.step_model model5 e5 ==
      Some {
        model5 with
          CS.model_record =
            CS.install_record_keys_for_role
              role_install.CS.install_role
              model5.CS.model_record
              install;
          CS.model_handshake = {
            model5.CS.model_handshake with
              CS.hs_keys =
                CS.update_key_schedule_with_install_for_role
                  role_install.CS.install_role
                  model5.CS.model_handshake.CS.hs_keys
                  install;
          };
      });
    (match install.CS.install_direction with
     | CS.TrafficWrite ->
       assert_norm (
         CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
         CS.ServerTraffic);
       assert_norm (
         CS.update_key_schedule_with_label
           model5.CS.model_handshake.CS.hs_keys
           CS.TrafficHandshake
           CS.ServerTraffic
           install.CS.install_material ==
         { model5.CS.model_handshake.CS.hs_keys with
             CS.ks_server_handshake_traffic = Some install.CS.install_material })
     | CS.TrafficRead ->
       assert_norm (
         CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficRead ==
         CS.ClientTraffic);
       assert_norm (
         CS.update_key_schedule_with_label
           model5.CS.model_handshake.CS.hs_keys
           CS.TrafficHandshake
           CS.ClientTraffic
           install.CS.install_material ==
         { model5.CS.model_handshake.CS.hs_keys with
             CS.ks_client_handshake_traffic = Some install.CS.install_material }))
  | _ ->
    assert (PNI.server_no_tail_handshake_traffic_install_event e5);
    assert False

let lemma_server_post_two_install_cover_model_shape
  (model5 model6 model7:CS.connection_model)
  (e5 e6:CS.conn_event)
  : Lemma
      (requires
        model5.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model5.CS.model_handshake.CS.hs_certificate == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        CS.step_model model5 e5 == Some model6 /\
        CS.step_model model6 e6 == Some model7)
      (ensures
        model7.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model7.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model7.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model7.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model7.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model7.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model7.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model7.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model7.CS.model_handshake.CS.hs_certificate == None /\
        model7.CS.model_handshake.CS.hs_certificate_verify == None /\
        model7.CS.model_handshake.CS.hs_certificate_verify_verified == false)
=
  assert (PNI.server_no_tail_handshake_traffic_install_event e5);
  lemma_server_post_first_install_direction_shape model5 model6 e5;
  match e6 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    let install = role_install.CS.install_payload in
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (
      CS.step_model model6 e6 ==
      Some {
        model6 with
          CS.model_record =
            CS.install_record_keys_for_role
              role_install.CS.install_role
              model6.CS.model_record
              install;
          CS.model_handshake = {
            model6.CS.model_handshake with
              CS.hs_keys =
                CS.update_key_schedule_with_install_for_role
                  role_install.CS.install_role
                  model6.CS.model_handshake.CS.hs_keys
                  install;
          };
      });
    (match install.CS.install_direction with
     | CS.TrafficWrite ->
       assert (PNTSS.server_no_tail_handshake_write_install_event e6);
       assert (PNTSS.server_no_tail_handshake_read_install_event e5);
       assert (Some?
         model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
       assert (None?
         model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
       assert_norm (
         CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
         CS.ServerTraffic);
       assert_norm (
         CS.update_key_schedule_with_label
           model6.CS.model_handshake.CS.hs_keys
           CS.TrafficHandshake
           CS.ServerTraffic
           install.CS.install_material ==
         { model6.CS.model_handshake.CS.hs_keys with
             CS.ks_server_handshake_traffic = Some install.CS.install_material })
     | CS.TrafficRead ->
       assert (PNTSS.server_no_tail_handshake_read_install_event e6);
       assert (PNTSS.server_no_tail_handshake_write_install_event e5);
       assert (Some?
         model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
       assert (None?
         model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
       assert_norm (
         CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficRead ==
         CS.ClientTraffic);
       assert_norm (
         CS.update_key_schedule_with_label
           model6.CS.model_handshake.CS.hs_keys
           CS.TrafficHandshake
           CS.ClientTraffic
           install.CS.install_material ==
         { model6.CS.model_handshake.CS.hs_keys with
             CS.ks_client_handshake_traffic = Some install.CS.install_material }))
  | _ ->
    assert (PNI.server_no_tail_handshake_traffic_install_event e6);
    assert False

let lemma_intro_server_no_tail_post_two_handshake_installs_tail_order
  (server:CS.connection_state)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (rest:list CS.conn_event)
  : Lemma
      (requires
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            (e5 :: e6 :: rest) /\
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        PNTSFShape.server_post_two_handshake_installs_tail_order rest)
      (ensures server_no_tail_post_two_handshake_installs_tail_order server)
=
  introduce exists ch' selection' server_shared' sh' e5' e6' rest'.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch'
          selection'
          server_shared'
          sh')
        (e5' :: e6' :: rest') /\
    PNTSS.server_no_tail_two_handshake_install_cover e5' e6' /\
    PNTSFShape.server_post_two_handshake_installs_tail_order rest'
  with ch selection server_shared sh e5 e6 rest
  and ()

let lemma_server_cleartext_prefix_append_expand
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (suffix:list CS.conn_event)
  : Lemma
      (ensures
        FStar.List.Tot.append
          (PWSeg.server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh)
          suffix ==
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
        suffix)
=
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 =
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    }) in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let ev4 =
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    }) in
  assert (
    PWSeg.server_cleartext_handshake_prefix_events
      ch
      selection
      server_shared
      sh ==
    ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: []);
  ListP.append_cons_l ev0 (ev1 :: ev2 :: ev3 :: ev4 :: []) suffix;
  ListP.append_cons_l ev1 (ev2 :: ev3 :: ev4 :: []) suffix;
  ListP.append_cons_l ev2 (ev3 :: ev4 :: []) suffix;
  ListP.append_cons_l ev3 (ev4 :: []) suffix;
  ListP.append_cons_l ev4 [] suffix;
  ListP.append_nil_l suffix

let lemma_server_no_tail_post_two_handshake_installs_tail_order_for_split
  (server:CS.connection_state)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (rest:list CS.conn_event)
  : Lemma
      (requires
        server_no_tail_post_two_handshake_installs_tail_order server /\
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            (e5 :: e6 :: rest))
      (ensures
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        PNTSFShape.server_post_two_handshake_installs_tail_order rest)
=
  eliminate exists ch' selection' server_shared' sh' e5' e6' rest'.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch'
          selection'
          server_shared'
          sh')
        (e5' :: e6' :: rest') /\
    PNTSS.server_no_tail_two_handshake_install_cover e5' e6' /\
    PNTSFShape.server_post_two_handshake_installs_tail_order rest'
  with
  (
    let suffix = e5 :: e6 :: rest in
    let suffix' = e5' :: e6' :: rest' in
    lemma_server_cleartext_prefix_append_expand
      ch
      selection
      server_shared
      sh
      suffix;
    lemma_server_cleartext_prefix_append_expand
      ch'
      selection'
      server_shared'
      sh'
      suffix';
    assert (
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
      suffix ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch');
      }) ::
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection') ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared') ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh');
      }) ::
      suffix');
    assert (suffix == suffix');
    assert (e5 == e5');
    assert (e6 == e6');
    assert (rest == rest')
  )

let lemma_server_duplicate_second_install_window_rank
  (model6 model7:CS.connection_model)
  (e6:CS.conn_event)
  : Lemma
      (requires
        model6.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model6.CS.model_handshake.CS.hs_certificate == None /\
        model6.CS.model_handshake.CS.hs_certificate_verify == None /\
        model6.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        PNI.server_no_tail_handshake_traffic_install_event e6 /\
        CS.step_model model6 e6 == Some model7 /\
        ((Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
          None? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
          PNTSS.server_no_tail_handshake_write_install_event e6) \/
         (None? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
          Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
          PNTSS.server_no_tail_handshake_read_install_event e6)))
      (ensures
        model7.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model7.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        PNTWHR.server_hello_window_rank model7 == 10)
=
  match e6 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    let install = role_install.CS.install_payload in
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (
      CS.step_model model6 e6 ==
      Some {
        model6 with
          CS.model_record =
            CS.install_record_keys_for_role
              role_install.CS.install_role
              model6.CS.model_record
              install;
          CS.model_handshake = {
            model6.CS.model_handshake with
              CS.hs_keys =
                CS.update_key_schedule_with_install_for_role
                  role_install.CS.install_role
                  model6.CS.model_handshake.CS.hs_keys
                  install;
          };
      });
    (match install.CS.install_direction with
     | CS.TrafficWrite ->
       assert_norm (
         CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
         CS.ServerTraffic);
       assert_norm (
         CS.update_key_schedule_with_label
           model6.CS.model_handshake.CS.hs_keys
           CS.TrafficHandshake
           CS.ServerTraffic
           install.CS.install_material ==
         { model6.CS.model_handshake.CS.hs_keys with
             CS.ks_server_handshake_traffic = Some install.CS.install_material });
       assert (None? model7.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
     | CS.TrafficRead ->
       assert_norm (
         CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficRead ==
         CS.ClientTraffic);
       assert_norm (
         CS.update_key_schedule_with_label
           model6.CS.model_handshake.CS.hs_keys
           CS.TrafficHandshake
           CS.ClientTraffic
           install.CS.install_material ==
         { model6.CS.model_handshake.CS.hs_keys with
             CS.ks_client_handshake_traffic = Some install.CS.install_material });
       assert (None? model7.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
    assert_norm (PNTWHR.server_hello_window_late_flight_progress
      model7.CS.model_handshake == 4);
    assert_norm (PNTWHR.server_hello_window_rank model7 == 10)
  | _ ->
    assert (PNI.server_no_tail_handshake_traffic_install_event e6);
    assert False

let lemma_server_tail_order_from_two_step_replay
  (server:CS.connection_state)
  (ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:GSH.serverHello)
  (e5 e6:CS.conn_event)
  (rest:list CS.conn_event)
  (model5 model6 model7:CS.connection_model)
  (tail_sent tail_received tail_sent2 tail_received2 tail_sent3 tail_received3:B.bytes)
  : Lemma
      (requires
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            (e5 :: e6 :: rest) /\
        FStar.List.Tot.length rest == 9 /\
        server.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank server.CS.cs_model == 0 /\
        model5.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model5.CS.model_handshake.CS.hs_certificate == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        PNTWHR.server_hello_window_rank model5 ==
          FStar.List.Tot.length (e6 :: rest) + 1 /\
        CS.step_model model5 e5 == Some model6 /\
        CS.step_model model6 e6 == Some model7 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model7
          rest
          tail_sent3
          tail_received3
          server.CS.cs_model /\
        PNI.server_no_tail_handshake_traffic_install_event e5 /\
        PNI.server_no_tail_handshake_traffic_install_event e6)
      (ensures server_no_tail_post_two_handshake_installs_tail_order server)
=
  let e5_write = PNTSS.server_no_tail_handshake_write_install_event e5 in
  let e5_read = PNTSS.server_no_tail_handshake_read_install_event e5 in
  let e6_write = PNTSS.server_no_tail_handshake_write_install_event e6 in
  let e6_read = PNTSS.server_no_tail_handshake_read_install_event e6 in
  lemma_server_post_first_install_direction_shape model5 model6 e5;
  lemma_server_no_tail_handshake_install_event_direction_cases e5;
  lemma_server_no_tail_handshake_install_event_direction_cases e6;
  assert (e5_write \/ e5_read);
  assert (e6_write \/ e6_read);
  if e5_write /\ e6_write then (
    assert (Some?
      model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    assert (None?
      model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    lemma_server_duplicate_second_install_window_rank model6 model7 e6;
    PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
      model7
      rest
      tail_sent3
      tail_received3
      server.CS.cs_model;
    assert (PNTWHR.server_hello_window_rank model7 <=
      FStar.List.Tot.length rest);
    assert False
  );
  if e5_read /\ e6_read then (
    assert (None?
      model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    assert (Some?
      model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    lemma_server_duplicate_second_install_window_rank model6 model7 e6;
    PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
      model7
      rest
      tail_sent3
      tail_received3
      server.CS.cs_model;
    assert (PNTWHR.server_hello_window_rank model7 <=
      FStar.List.Tot.length rest);
    assert False
  );
  assert (PNTSS.server_no_tail_two_handshake_install_cover e5 e6);
  lemma_server_post_two_install_cover_model_shape model5 model6 model7 e5 e6;
  PNTSFShape.lemma_server_post_two_handshake_installs_tail_order_from_replay
    model7
    rest
    tail_sent3
    tail_received3
    server.CS.cs_model;
  lemma_intro_server_no_tail_post_two_handshake_installs_tail_order
    server
    ch
    selection
    server_shared
    sh
    e5
    e6
    rest

let lemma_clean16_no_tail_valid_byte_traces_server_next_two_events_handshake_installs
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        PNTSS.server_no_tail_next_two_events_handshake_installs server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (SD.server_driver_application_ready server);
  assert (FStar.List.Tot.length server.CS.cs_event_log == 16);
  assert (ST.server_end_to_end_invariant server);
  assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent server);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
  assert (TLS13.Spec.StateMachine.Correspondence.stable_server_x25519_key_share_projection server);
  assert (TLS13.Spec.StateMachine.Correspondence.server_x25519_key_share_projection server);
  assert (Some?
    server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  PNTWHR.lemma_server_hello_window_rank_application_data_installed_zero
    server.CS.cs_model;
  assert (PNTWHR.server_hello_window_rank server.CS.cs_model == 0);
  eliminate exists
    server_ch
    selection
    server_shared
    server_sh
    e5
    e6
    rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh)
        (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9
  with
  (
    let server_ev0 = CS.ConnLocalEvent CS.LocalStartServer in
    let server_ev1 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) in
    let server_ev2 =
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
    let server_ev3 =
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
    let server_ev4 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
      }) in
    let server_prefix : list CS.conn_event =
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [] in
    let server_suffix = e5 :: e6 :: rest in
    let initial = CS.initial_model server.CS.cs_model.CS.model_config in
    let raw_sent = server.CS.cs_wire_log.CL.raw_sent in
    let raw_received = server.CS.cs_wire_log.CL.raw_received in
    ListP.append_cons_l
      server_ev0
      (server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev1
      (server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev2
      (server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev3
      (server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l server_ev4 [] server_suffix;
    ListP.append_nil_l server_suffix;
    assert (server_prefix ==
      PWSeg.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh);
    assert (FStar.List.Tot.append server_prefix server_suffix ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_suffix);
    assert (server.CS.cs_event_log ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_suffix);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      server.CS.cs_event_log
      raw_sent
      raw_received
      server.CS.cs_model);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      (server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
       server_suffix)
      raw_sent
      raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_cleartext_prefix_step_models_from_raw_replay
      initial
      server_ch
      selection
      server_shared
      server_sh
      server_suffix
      raw_sent
      raw_received
      server.CS.cs_model;
    eliminate exists
      model1
      model2
      model3
      model4
      model5
      tail_sent
      tail_received.
      CS.step_model
        initial
        (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
      CS.step_model
        model1
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        })) == Some model2 /\
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
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        })) == Some model5 /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        model5
        server_suffix
        tail_sent
        tail_received
        server.CS.cs_model
    with
    (
      PNTWHR.lemma_server_hello_window_after_server_cleartext_prefix_fresh
        initial
        server_ch
        selection
        server_shared
        server_sh
        model1
        model2
        model3
        model4
        model5;
      assert (PNTWHR.server_hello_window_rank model5 == 11);
      assert_norm (FStar.List.Tot.length (e6 :: rest) ==
        FStar.List.Tot.length rest + 1);
      assert (FStar.List.Tot.length (e6 :: rest) == 10);
      assert (PNTWHR.server_hello_window_rank model5 ==
        FStar.List.Tot.length (e6 :: rest) + 1);
      PNTWHR.lemma_server_hello_window_tight_next_two_events_handshake_traffic_installs
        model5
        e5
        e6
        rest
        tail_sent
        tail_received
        server.CS.cs_model;
      assert (PNTSS.server_no_tail_next_two_events_handshake_installs server)
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_next_two_events_handshake_install_cover
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        PNTSS.server_no_tail_next_two_events_handshake_install_cover server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (SD.server_driver_application_ready server);
  assert (FStar.List.Tot.length server.CS.cs_event_log == 16);
  assert (ST.server_end_to_end_invariant server);
  assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent server);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
  assert (TLS13.Spec.StateMachine.Correspondence.stable_server_x25519_key_share_projection server);
  assert (TLS13.Spec.StateMachine.Correspondence.server_x25519_key_share_projection server);
  assert (Some?
    server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  PNTWHR.lemma_server_hello_window_rank_application_data_installed_zero
    server.CS.cs_model;
  assert (PNTWHR.server_hello_window_rank server.CS.cs_model == 0);
  eliminate exists
    server_ch
    selection
    server_shared
    server_sh
    e5
    e6
    rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh)
        (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9
  with
  (
    let server_ev0 = CS.ConnLocalEvent CS.LocalStartServer in
    let server_ev1 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) in
    let server_ev2 =
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
    let server_ev3 =
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
    let server_ev4 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
      }) in
    let server_prefix : list CS.conn_event =
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [] in
    let server_suffix = e5 :: e6 :: rest in
    let initial = CS.initial_model server.CS.cs_model.CS.model_config in
    let raw_sent = server.CS.cs_wire_log.CL.raw_sent in
    let raw_received = server.CS.cs_wire_log.CL.raw_received in
    ListP.append_cons_l
      server_ev0
      (server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev1
      (server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev2
      (server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev3
      (server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l server_ev4 [] server_suffix;
    ListP.append_nil_l server_suffix;
    assert (server_prefix ==
      PWSeg.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh);
    assert (FStar.List.Tot.append server_prefix server_suffix ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_suffix);
    assert (server.CS.cs_event_log ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_suffix);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      server.CS.cs_event_log
      raw_sent
      raw_received
      server.CS.cs_model);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      (server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
       server_suffix)
      raw_sent
      raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_cleartext_prefix_step_models_from_raw_replay
      initial
      server_ch
      selection
      server_shared
      server_sh
      server_suffix
      raw_sent
      raw_received
      server.CS.cs_model;
    eliminate exists
      model1
      model2
      model3
      model4
      model5
      tail_sent
      tail_received.
      CS.step_model
        initial
        (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
      CS.step_model
        model1
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        })) == Some model2 /\
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
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        })) == Some model5 /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        model5
        server_suffix
        tail_sent
        tail_received
        server.CS.cs_model
    with
    (
      PNTWHR.lemma_server_hello_window_after_server_cleartext_prefix_fresh
        initial
        server_ch
        selection
        server_shared
        server_sh
        model1
        model2
        model3
        model4
        model5;
      assert (PNTWHR.server_hello_window_rank model5 == 11);
      assert_norm (FStar.List.Tot.length (e6 :: rest) ==
        FStar.List.Tot.length rest + 1);
      assert (FStar.List.Tot.length (e6 :: rest) == 10);
      assert (PNTWHR.server_hello_window_rank model5 ==
        FStar.List.Tot.length (e6 :: rest) + 1);
      PNTWHR.lemma_server_hello_window_tight_next_two_events_handshake_traffic_installs
        model5
        e5
        e6
        rest
        tail_sent
        tail_received
        server.CS.cs_model;
      assert (PNI.server_no_tail_handshake_traffic_install_event e5);
      assert (PNI.server_no_tail_handshake_traffic_install_event e6);
      assert_norm (
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model5 (e5 :: e6 :: rest)
          tail_sent tail_received server.CS.cs_model ==
        (exists model6 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model5 e5 /\
          CS.step_model model5 e5 == Some model6 /\
          CS.event_raw_delta_legal model5 e5 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model6
            (e6 :: rest)
            tail_sent2
            tail_received2
            server.CS.cs_model));
      eliminate exists model6 delta_sent delta_received tail_sent2 tail_received2.
        CS.legal_event model5 e5 /\
        CS.step_model model5 e5 == Some model6 /\
        CS.event_raw_delta_legal model5 e5 delta_sent delta_received /\
        Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
        Seq.equal tail_received (B.append delta_received tail_received2) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model6
          (e6 :: rest)
          tail_sent2
          tail_received2
          server.CS.cs_model
      with
      (
        lemma_server_post_first_install_direction_shape model5 model6 e5;
        assert_norm (
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model6 (e6 :: rest)
            tail_sent2 tail_received2 server.CS.cs_model ==
          (exists model7 delta_sent2 delta_received2 tail_sent3 tail_received3.
            CS.legal_event model6 e6 /\
            CS.step_model model6 e6 == Some model7 /\
            CS.event_raw_delta_legal model6 e6 delta_sent2 delta_received2 /\
            Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
            Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model7
              rest
              tail_sent3
              tail_received3
              server.CS.cs_model));
        eliminate exists model7 delta_sent2 delta_received2 tail_sent3 tail_received3.
          CS.legal_event model6 e6 /\
          CS.step_model model6 e6 == Some model7 /\
          CS.event_raw_delta_legal model6 e6 delta_sent2 delta_received2 /\
          Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
          Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model7
            rest
            tail_sent3
            tail_received3
            server.CS.cs_model
        with
        (
          let e5_write = PNTSS.server_no_tail_handshake_write_install_event e5 in
          let e5_read = PNTSS.server_no_tail_handshake_read_install_event e5 in
          let e6_write = PNTSS.server_no_tail_handshake_write_install_event e6 in
          let e6_read = PNTSS.server_no_tail_handshake_read_install_event e6 in
          lemma_server_no_tail_handshake_install_event_direction_cases e5;
          lemma_server_no_tail_handshake_install_event_direction_cases e6;
          assert (e5_write \/ e5_read);
          assert (e6_write \/ e6_read);
          if e5_write /\ e6_write then (
            assert (Some?
              model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
            assert (None?
              model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
            lemma_server_duplicate_second_install_window_rank model6 model7 e6;
            PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
              model7
              rest
              tail_sent3
              tail_received3
              server.CS.cs_model;
            assert (PNTWHR.server_hello_window_rank model7 <=
              FStar.List.Tot.length rest);
            assert False
          );
          if e5_read /\ e6_read then (
            assert (None?
              model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
            assert (Some?
              model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
            lemma_server_duplicate_second_install_window_rank model6 model7 e6;
            PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
              model7
              rest
              tail_sent3
              tail_received3
              server.CS.cs_model;
            assert (PNTWHR.server_hello_window_rank model7 <=
              FStar.List.Tot.length rest);
            assert False
          );
          assert (PNTSS.server_no_tail_two_handshake_install_cover e5 e6);
          assert (PNTSS.server_no_tail_next_two_events_handshake_install_cover server)
        )
      )
    )
  )

let lemma_server_no_tail_no_ccs_post_two_handshake_installs_tail_order
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_no_ccs_application_ready_boundary server)
      (ensures server_no_tail_post_two_handshake_installs_tail_order server)
=
  lemma_server_no_tail_no_ccs_post_server_hello_suffix_shape server;
  assert (SD.server_driver_application_ready server);
  assert (FStar.List.Tot.length server.CS.cs_event_log == 16);
  assert (ST.server_end_to_end_invariant server);
  assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent server);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
  assert (TLS13.Spec.StateMachine.Correspondence.stable_server_x25519_key_share_projection server);
  assert (TLS13.Spec.StateMachine.Correspondence.server_x25519_key_share_projection server);
  assert (Some?
    server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  PNTWHR.lemma_server_hello_window_rank_application_data_installed_zero
    server.CS.cs_model;
  assert (PNTWHR.server_hello_window_rank server.CS.cs_model == 0);
  eliminate exists
    server_ch
    selection
    server_shared
    server_sh
    e5
    e6
    rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh)
        (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9
  with
  (
    let server_suffix = e5 :: e6 :: rest in
    let initial = CS.initial_model server.CS.cs_model.CS.model_config in
    let raw_sent = server.CS.cs_wire_log.CL.raw_sent in
    let raw_received = server.CS.cs_wire_log.CL.raw_received in
    lemma_server_cleartext_prefix_append_expand
      server_ch
      selection
      server_shared
      server_sh
      server_suffix;
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      server.CS.cs_event_log
      raw_sent
      raw_received
      server.CS.cs_model);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
       }) ::
       server_suffix)
      raw_sent
      raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_cleartext_prefix_step_models_from_raw_replay
      initial
      server_ch
      selection
      server_shared
      server_sh
      server_suffix
      raw_sent
      raw_received
      server.CS.cs_model;
    eliminate exists
      model1
      model2
      model3
      model4
      model5
      tail_sent
      tail_received.
      CS.step_model
        initial
        (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
      CS.step_model
        model1
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        })) == Some model2 /\
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
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        })) == Some model5 /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        model5
        server_suffix
        tail_sent
        tail_received
        server.CS.cs_model
    with
    (
      PNTWHR.lemma_server_hello_window_after_server_cleartext_prefix_fresh
        initial
        server_ch
        selection
        server_shared
        server_sh
        model1
        model2
        model3
        model4
        model5;
      assert (PNTWHR.server_hello_window_rank model5 == 11);
      assert_norm (FStar.List.Tot.length (e6 :: rest) ==
        FStar.List.Tot.length rest + 1);
      assert (FStar.List.Tot.length (e6 :: rest) == 10);
      assert (PNTWHR.server_hello_window_rank model5 ==
        FStar.List.Tot.length (e6 :: rest) + 1);
      PNTWHR.lemma_server_hello_window_tight_next_two_events_handshake_traffic_installs
        model5
        e5
        e6
        rest
        tail_sent
        tail_received
        server.CS.cs_model;
      assert (PNI.server_no_tail_handshake_traffic_install_event e5);
      assert (PNI.server_no_tail_handshake_traffic_install_event e6);
      assert_norm (
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model5 (e5 :: e6 :: rest)
          tail_sent tail_received server.CS.cs_model ==
        (exists model6 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model5 e5 /\
          CS.step_model model5 e5 == Some model6 /\
          CS.event_raw_delta_legal model5 e5 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model6
            (e6 :: rest)
            tail_sent2
            tail_received2
            server.CS.cs_model));
      eliminate exists model6 delta_sent delta_received tail_sent2 tail_received2.
        CS.legal_event model5 e5 /\
        CS.step_model model5 e5 == Some model6 /\
        CS.event_raw_delta_legal model5 e5 delta_sent delta_received /\
        Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
        Seq.equal tail_received (B.append delta_received tail_received2) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model6
          (e6 :: rest)
          tail_sent2
          tail_received2
          server.CS.cs_model
      with
      (
        assert_norm (
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model6 (e6 :: rest)
            tail_sent2 tail_received2 server.CS.cs_model ==
          (exists model7 delta_sent2 delta_received2 tail_sent3 tail_received3.
            CS.legal_event model6 e6 /\
            CS.step_model model6 e6 == Some model7 /\
            CS.event_raw_delta_legal model6 e6 delta_sent2 delta_received2 /\
            Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
            Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model7
              rest
              tail_sent3
              tail_received3
              server.CS.cs_model));
        eliminate exists model7 delta_sent2 delta_received2 tail_sent3 tail_received3.
          CS.legal_event model6 e6 /\
          CS.step_model model6 e6 == Some model7 /\
          CS.event_raw_delta_legal model6 e6 delta_sent2 delta_received2 /\
          Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
          Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model7
            rest
            tail_sent3
            tail_received3
            server.CS.cs_model
        with
        (
          lemma_server_tail_order_from_two_step_replay
            server
            server_ch
            selection
            server_shared
            server_sh
            e5
            e6
            rest
            model5
            model6
            model7
            tail_sent
            tail_received
            tail_sent2
            tail_received2
            tail_sent3
            tail_received3
        )
      )
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_post_two_handshake_installs_tail_order
  (client_initial:EC.client_initial_state)
  (server_initial:ES.server_initial_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        server_no_tail_post_two_handshake_installs_tail_order server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (SD.server_driver_application_ready server);
  assert (FStar.List.Tot.length server.CS.cs_event_log == 16);
  assert (ST.server_end_to_end_invariant server);
  assert (TLS13.Spec.StateMachine.Replay.connection_state_raw_event_replay_consistent server);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
  assert (TLS13.Spec.StateMachine.Correspondence.stable_server_x25519_key_share_projection server);
  assert (TLS13.Spec.StateMachine.Correspondence.server_x25519_key_share_projection server);
  assert (Some?
    server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  PNTWHR.lemma_server_hello_window_rank_application_data_installed_zero
    server.CS.cs_model;
  assert (PNTWHR.server_hello_window_rank server.CS.cs_model == 0);
  eliminate exists
    server_ch
    selection
    server_shared
    server_sh
    e5
    e6
    rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh)
        (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9
  with
  (
    let server_ev0 = CS.ConnLocalEvent CS.LocalStartServer in
    let server_ev1 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) in
    let server_ev2 =
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
    let server_ev3 =
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
    let server_ev4 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
      }) in
    let server_prefix : list CS.conn_event =
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [] in
    let server_suffix = e5 :: e6 :: rest in
    let initial = CS.initial_model server.CS.cs_model.CS.model_config in
    let raw_sent = server.CS.cs_wire_log.CL.raw_sent in
    let raw_received = server.CS.cs_wire_log.CL.raw_received in
    ListP.append_cons_l
      server_ev0
      (server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev1
      (server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev2
      (server_ev3 :: server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l
      server_ev3
      (server_ev4 :: [])
      server_suffix;
    ListP.append_cons_l server_ev4 [] server_suffix;
    ListP.append_nil_l server_suffix;
    assert (server_prefix ==
      PWSeg.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh);
    assert (FStar.List.Tot.append server_prefix server_suffix ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_suffix);
    assert (server.CS.cs_event_log ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_suffix);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      server.CS.cs_event_log
      raw_sent
      raw_received
      server.CS.cs_model);
    assert (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      initial
      (server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
       server_suffix)
      raw_sent
      raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_cleartext_prefix_step_models_from_raw_replay
      initial
      server_ch
      selection
      server_shared
      server_sh
      server_suffix
      raw_sent
      raw_received
      server.CS.cs_model;
    eliminate exists
      model1
      model2
      model3
      model4
      model5
      tail_sent
      tail_received.
      CS.step_model
        initial
        (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
      CS.step_model
        model1
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        })) == Some model2 /\
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
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        })) == Some model5 /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
        model5
        server_suffix
        tail_sent
        tail_received
        server.CS.cs_model
    with
    (
      PNTWHR.lemma_server_hello_window_after_server_cleartext_prefix_fresh
        initial
        server_ch
        selection
        server_shared
        server_sh
        model1
        model2
        model3
        model4
        model5;
      assert (PNTWHR.server_hello_window_rank model5 == 11);
      assert_norm (FStar.List.Tot.length (e6 :: rest) ==
        FStar.List.Tot.length rest + 1);
      assert (FStar.List.Tot.length (e6 :: rest) == 10);
      assert (PNTWHR.server_hello_window_rank model5 ==
        FStar.List.Tot.length (e6 :: rest) + 1);
      PNTWHR.lemma_server_hello_window_tight_next_two_events_handshake_traffic_installs
        model5
        e5
        e6
        rest
        tail_sent
        tail_received
        server.CS.cs_model;
      assert (PNI.server_no_tail_handshake_traffic_install_event e5);
      assert (PNI.server_no_tail_handshake_traffic_install_event e6);
      assert_norm (
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model5 (e5 :: e6 :: rest)
          tail_sent tail_received server.CS.cs_model ==
        (exists model6 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model5 e5 /\
          CS.step_model model5 e5 == Some model6 /\
          CS.event_raw_delta_legal model5 e5 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model6
            (e6 :: rest)
            tail_sent2
            tail_received2
            server.CS.cs_model));
      eliminate exists model6 delta_sent delta_received tail_sent2 tail_received2.
        CS.legal_event model5 e5 /\
        CS.step_model model5 e5 == Some model6 /\
        CS.event_raw_delta_legal model5 e5 delta_sent delta_received /\
        Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
        Seq.equal tail_received (B.append delta_received tail_received2) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model6
          (e6 :: rest)
          tail_sent2
          tail_received2
          server.CS.cs_model
      with
      (
        lemma_server_post_first_install_direction_shape model5 model6 e5;
        assert_norm (
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model6 (e6 :: rest)
            tail_sent2 tail_received2 server.CS.cs_model ==
          (exists model7 delta_sent2 delta_received2 tail_sent3 tail_received3.
            CS.legal_event model6 e6 /\
            CS.step_model model6 e6 == Some model7 /\
            CS.event_raw_delta_legal model6 e6 delta_sent2 delta_received2 /\
            Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
            Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
              model7
              rest
              tail_sent3
              tail_received3
              server.CS.cs_model));
        eliminate exists model7 delta_sent2 delta_received2 tail_sent3 tail_received3.
          CS.legal_event model6 e6 /\
          CS.step_model model6 e6 == Some model7 /\
          CS.event_raw_delta_legal model6 e6 delta_sent2 delta_received2 /\
          Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
          Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model7
            rest
            tail_sent3
            tail_received3
            server.CS.cs_model
        with
        (
          lemma_server_tail_order_from_two_step_replay
            server
            server_ch
            selection
            server_shared
            server_sh
            e5
            e6
            rest
            model5
            model6
            model7
            tail_sent
            tail_received
            tail_sent2
            tail_received2
            tail_sent3
            tail_received3
        )
      )
    )
  )

#pop-options
