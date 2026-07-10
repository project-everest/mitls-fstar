module TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types

let lemma_server_hello_window_rank_fresh_is_eleven
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false)
      (ensures server_hello_window_rank model == 11)
= ()

let lemma_server_hello_window_rank_application_data_installed_zero
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlApplicationData /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        CS.application_record_keys_installed_for_role
          CS.ServerEndpoint
          model)
      (ensures server_hello_window_rank model == 0)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ServerEndpoint
      CS.TrafficWrite == CS.ServerTraffic);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ServerEndpoint
      CS.TrafficRead == CS.ClientTraffic);
  match
    keys.CS.ks_client_application_traffic,
    keys.CS.ks_server_application_traffic
  with
  | Some _, Some _ -> ()
  | _, _ ->
    assert False

let lemma_server_hello_window_after_server_cleartext_prefix_fresh
  (model0:CS.connection_model)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (model1:CS.connection_model)
  (model2:CS.connection_model)
  (model3:CS.connection_model)
  (model4:CS.connection_model)
  (model5:CS.connection_model)
  : Lemma
      (requires
        model0 == CS.initial_model model0.CS.model_config /\
        model0.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.step_model
          model0
          (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
        CS.step_model
          model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) == Some model2 /\
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
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) == Some model5)
      (ensures
        model5.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model5.CS.model_handshake.CS.hs_certificate == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify == None /\
        model5.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        server_hello_window_rank model5 == 11)
=
  assert (model0.CS.model_control == CS.ControlNew);
  assert (model0.CS.model_handshake == CS.empty_handshake_state);
  assert_norm (
    CS.step_model model0 (CS.ConnLocalEvent CS.LocalStartServer) ==
    Some (CS.with_handshake_stage
      model0
      model0.CS.model_handshake
      CS.HsAwaitingClientHello));
  assert (model1 ==
    CS.with_handshake_stage
      model0
      model0.CS.model_handshake
      CS.HsAwaitingClientHello);
  assert (model1.CS.model_control ==
    CS.ControlHandshaking CS.HsAwaitingClientHello);
  assert (model1.CS.model_config == model0.CS.model_config);
  assert (model1.CS.model_handshake.CS.hs_keys ==
    model0.CS.model_handshake.CS.hs_keys);
  assert (model1.CS.model_handshake.CS.hs_encrypted_extensions == None);
  assert (model1.CS.model_handshake.CS.hs_certificate == None);
  assert (model1.CS.model_handshake.CS.hs_certificate_verify == None);
  assert (model1.CS.model_handshake.CS.hs_certificate_verify_verified == false);
  let hs1 = model1.CS.model_handshake in
  let model2_expected =
    CS.with_handshake_stage
      model1
      (CS.append_handshake_to_transcript
        ({ hs1 with
            CS.hs_client_hello = Some ch;
            CS.hs_buffers =
              { hs1.CS.hs_buffers with
                  CS.hb_client_hello_bytes =
                    TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
              };
        })
        (M.ClientHello ch))
      CS.HsClientHelloReceived in
  assert_norm (
    CS.step_model
      model1
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) == Some model2_expected);
  assert (model2 == model2_expected);
  assert (model2.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (model2.CS.model_config == model1.CS.model_config);
  assert (model2.CS.model_handshake.CS.hs_keys ==
    model1.CS.model_handshake.CS.hs_keys);
  assert (model2.CS.model_handshake.CS.hs_server_selection == None);
  assert (model2.CS.model_handshake.CS.hs_encrypted_extensions == None);
  assert (model2.CS.model_handshake.CS.hs_certificate == None);
  assert (model2.CS.model_handshake.CS.hs_certificate_verify == None);
  assert (model2.CS.model_handshake.CS.hs_certificate_verify_verified == false);
  let model3_expected =
    CS.with_handshake_stage
      model2
      { model2.CS.model_handshake with
          CS.hs_server_selection = Some selection;
          CS.hs_client_hello =
            Some selection.CS.server_selected_client_hello;
      }
      CS.HsClientHelloReceived in
  assert_norm (
    CS.step_model
      model2
      (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
    Some model3_expected);
  assert (model3 == model3_expected);
  assert (model3.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (model3.CS.model_config == model2.CS.model_config);
  assert (model3.CS.model_handshake.CS.hs_keys ==
    model2.CS.model_handshake.CS.hs_keys);
  assert (model3.CS.model_handshake.CS.hs_encrypted_extensions == None);
  assert (model3.CS.model_handshake.CS.hs_certificate == None);
  assert (model3.CS.model_handshake.CS.hs_certificate_verify == None);
  assert (model3.CS.model_handshake.CS.hs_certificate_verify_verified == false);
  let model4_expected =
    CS.derive_shared_secret_model
      model3
      model3.CS.model_handshake
      server_shared in
  assert_norm (
    CS.step_model
      model3
      (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
    Some model4_expected);
  assert (model4 == model4_expected);
  assert (model4.CS.model_control ==
    CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (model4.CS.model_config == model3.CS.model_config);
  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
    Some server_shared);
  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
  assert (model4.CS.model_handshake.CS.hs_encrypted_extensions == None);
  assert (model4.CS.model_handshake.CS.hs_certificate == None);
  assert (model4.CS.model_handshake.CS.hs_certificate_verify == None);
  assert (model4.CS.model_handshake.CS.hs_certificate_verify_verified == false);
  let hs4 = model4.CS.model_handshake in
  let model5_expected =
    CS.with_handshake_stage
      model4
      (CS.append_handshake_to_transcript
        ({ hs4 with
            CS.hs_server_hello = Some sh;
            CS.hs_buffers =
              { hs4.CS.hs_buffers with
                  CS.hb_server_hello_bytes =
                    TLS13.Wire.Spec.serialize_handshake (M.ServerHello sh);
              };
        })
        (M.ServerHello sh))
      CS.HsServerHelloSent in
  assert_norm (
    CS.step_model
      model4
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) == Some model5_expected);
  assert (model5 == model5_expected);
  assert (model5.CS.model_config == model4.CS.model_config);
  assert (model5.CS.model_control ==
    CS.ControlHandshaking CS.HsServerHelloSent);
  assert (model5.CS.model_handshake.CS.hs_keys ==
    model4.CS.model_handshake.CS.hs_keys);
  assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
    Some server_shared);
  assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
  assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
  assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
  assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
  assert (model5.CS.model_handshake.CS.hs_encrypted_extensions == None);
  assert (model5.CS.model_handshake.CS.hs_certificate == None);
  assert (model5.CS.model_handshake.CS.hs_certificate_verify == None);
  assert (model5.CS.model_handshake.CS.hs_certificate_verify_verified == false);
  lemma_server_hello_window_rank_fresh_is_eleven model5

let lemma_server_hello_window_role_install_step
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived) /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) /\
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) ==
          Some model')
      (ensures
        server_hello_window_rank model <=
        server_hello_window_rank model' + 1)
=
  let install = role_install.CS.install_payload in
  assert (CS.legal_local_event
    model
    (CS.LocalInstallTrafficKeysForRole role_install));
  assert (role_install.CS.install_role == CS.ServerEndpoint);
  assert (CS.step_local_event
    model
    (CS.LocalInstallTrafficKeysForRole role_install) == Some model');
  match model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ServerEndpoint
      stage
      install);
    (match stage, install.CS.install_epoch, install.CS.install_direction with
    | CS.HsServerHelloSent, CS.TrafficHandshake, CS.TrafficWrite ->
      assert (server_hello_window_rank model <=
        server_hello_window_rank model' + 1)
    | CS.HsServerHelloSent, CS.TrafficHandshake, CS.TrafficRead ->
      assert (server_hello_window_rank model <=
        server_hello_window_rank model' + 1)
    | CS.HsServerFinishedSent, CS.TrafficApplication, CS.TrafficWrite ->
      assert (server_hello_window_rank model <=
        server_hello_window_rank model' + 1)
    | CS.HsClientFinishedReceived, CS.TrafficApplication, CS.TrafficRead ->
      assert (server_hello_window_rank model <=
        server_hello_window_rank model' + 1)
    | _, _, _ ->
      assert False)
  | _ ->
    assert False

let lemma_server_hello_window_rank_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived) /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        CS.ControlFailed? model'.CS.model_control \/
        server_hello_window_rank model <= server_hello_window_rank model' + 1)
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
        assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert False
      | CS.LocalInstallTrafficKeysForRole role_install ->
        lemma_server_hello_window_role_install_step model role_install model'
      | CS.LocalFail _ ->
        assert False
      | _ ->
        (match model.CS.model_control, local with
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CS.LocalSignCertificateVerify _ ->
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | CS.ControlHandshaking CS.HsClientFinishedReceived,
          CS.LocalVerifyClientFinished _ ->
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | _, _ ->
          assert (CS.step_local_event model local == None);
          assert False))
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message
        model
        msg.CL.message_direction
        msg.CL.message_value);
      assert (CS.step_tls_message
        model
        msg.CL.message_direction
        msg.CL.message_value == Some model');
      (match msg.CL.message_value with
      | M.TlsAlert alert ->
        assert False
      | M.TlsChangeCipherSpec ->
        assert (model' == model);
        assert (server_hello_window_rank model <=
          server_hello_window_rank model' + 1)
      | M.TlsHandshake hs_msg ->
        (match model.CS.model_control, msg.CL.message_direction, hs_msg with
        | CS.ControlHandshaking CS.HsServerHelloSent,
          CL.Sent,
          M.EncryptedExtensions ee ->
          assert (CS.legal_handshake_message
            model
            CL.Sent
            (M.EncryptedExtensions ee));
          assert (Some?
            model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
          let hs0 = model.CS.model_handshake in
          let model_after =
            CS.with_handshake_stage
              {
                model with
                  CS.model_record = {
                    model.CS.model_record with
                      CS.record_write = R.next_seq model.CS.model_record.CS.record_write;
                  };
              }
              (CS.append_handshake_to_transcript
                { hs0 with CS.hs_encrypted_extensions = Some ee }
                (M.EncryptedExtensions ee))
              CS.HsServerEncryptedFlightSent in
          assert_norm (
            CS.step_tls_message
              model
              CL.Sent
              (M.TlsHandshake (M.EncryptedExtensions ee)) ==
            Some model_after);
          assert (model' == model_after);
          assert (model'.CS.model_control ==
            CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
          assert (model'.CS.model_handshake.CS.hs_keys ==
            model.CS.model_handshake.CS.hs_keys);
          assert (model'.CS.model_handshake.CS.hs_certificate ==
            model.CS.model_handshake.CS.hs_certificate);
          assert (model'.CS.model_handshake.CS.hs_certificate_verify ==
            model.CS.model_handshake.CS.hs_certificate_verify);
          assert (model'.CS.model_handshake.CS.hs_certificate_verify_verified ==
            model.CS.model_handshake.CS.hs_certificate_verify_verified);
          (match model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
          | Some _ -> ()
          | None -> assert False);
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CL.Sent,
          M.Certificate _ ->
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CL.Sent,
          M.CertificateVerify _ ->
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CL.Sent,
          M.Finished _ ->
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerFinishedSent,
          CL.Received,
          M.Finished _ ->
          assert (server_hello_window_rank model <=
            server_hello_window_rank model' + 1)
        | _, _, _ ->
          assert (CS.step_handshake_message
            model
            msg.CL.message_direction
            hs_msg == None);
          assert False)
      | M.TlsApplicationData _ ->
        assert False
      | M.TlsIgnoredPostHandshake _ ->
        assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert False
      | M.TlsKeyUpdate _ ->
        assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert False))

(**
  Small standalone fact needed by the [ControlApplicationData] case of
  [lemma_server_hello_window_rank_replay_lower_bound] below: once a
  [TlsAlert CloseNotify] takes the model out of [ControlApplicationData] and
  into [ControlClosing]/[ControlClosed], there is no legal event that ever
  returns it to [ControlApplicationData] ([ControlClosing] only ever steps
  to [ControlClosed] or [ControlFailed]; nothing but [LocalFail] is legal at
  [ControlClosed] at all).
**)
#push-options "--split_queries always --z3rlimit 10"
let rec lemma_closing_or_closed_never_returns_to_application_data
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        (model.CS.model_control == CS.ControlClosing \/
         model.CS.model_control == CS.ControlClosed) /\
        CS.conn_events_raw_replay model events raw_sent raw_received final_model)
      (ensures ~ (final_model.CS.model_control == CS.ControlApplicationData))
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      ~ (final_model.CS.model_control == CS.ControlApplicationData)
    with _.
    (
      match model1.CS.model_control with
      | CS.ControlFailed _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model
      | _ ->
        (match model.CS.model_control with
        | CS.ControlClosing ->
          (match ev with
          | CS.ConnNetworkEvent msg ->
            assert (CS.legal_tls_message
              model
              msg.CL.message_direction
              msg.CL.message_value);
            (match msg.CL.message_value with
            | M.TlsAlert T.Close_notify ->
              assert (msg.CL.message_direction == CL.Received);
              assert (model1.CS.model_control == CS.ControlClosed);
              lemma_closing_or_closed_never_returns_to_application_data
                model1
                rest
                tail_sent
                tail_received
                final_model
            | M.TlsAlert _ ->
              assert False
            | _ ->
              assert (CS.step_model model ev == None);
              assert False)
          | CS.ConnLocalEvent local ->
            assert (CS.legal_local_event model local);
            (match local with
            | CS.LocalFail _ ->
              assert False
            | _ ->
              assert (CS.step_local_event model local == None);
              assert False))
        | CS.ControlClosed ->
          (match ev with
          | CS.ConnLocalEvent local ->
            assert (CS.legal_local_event model local);
            (match local with
            | CS.LocalFail _ ->
              assert False
            | _ ->
              assert (CS.step_local_event model local == None);
              assert False)
          | CS.ConnNetworkEvent msg ->
            assert (CS.legal_tls_message
              model
              msg.CL.message_direction
              msg.CL.message_value);
            (match msg.CL.message_value with
            | M.TlsAlert _ ->
              assert False
            | _ ->
              assert (CS.step_model model ev == None);
              assert False))
        | _ ->
          assert False)
    )

let rec lemma_server_hello_window_rank_replay_lower_bound
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived \/
         model.CS.model_control == CS.ControlApplicationData) /\
        CS.conn_events_raw_replay model events raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_hello_window_rank final_model == 0)
      (ensures
        server_hello_window_rank model <= FStar.List.Tot.length events)
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      server_hello_window_rank model <= FStar.List.Tot.length (ev :: rest)
    with _.
    (
      match model.CS.model_control with
      | CS.ControlApplicationData ->
        CSL.lemma_step_model_preserves_config model ev model1;
        (match model1.CS.model_control with
        | CS.ControlFailed _ ->
          PNI.lemma_conn_events_raw_replay_from_failed_results_failed
            model1
            rest
            tail_sent
            tail_received
            final_model;
          assert (CS.ControlFailed? final_model.CS.model_control);
          assert (final_model.CS.model_control == CS.ControlApplicationData);
          assert False
        | CS.ControlApplicationData ->
          lemma_server_hello_window_rank_replay_lower_bound
            model1
            rest
            tail_sent
            tail_received
            final_model;
          assert (server_hello_window_rank model1 <= FStar.List.Tot.length rest);
          assert (server_hello_window_rank model == server_hello_window_rank model1)
        | _ ->
          // The only remaining legal (non-failed) transitions out of
          // [ControlApplicationData] are the [TlsAlert CloseNotify] moves
          // into [ControlClosing]/[ControlClosed], neither of which can
          // ever legally return to [ControlApplicationData].
          lemma_closing_or_closed_never_returns_to_application_data
            model1
            rest
            tail_sent
            tail_received
            final_model;
          assert (~ (final_model.CS.model_control == CS.ControlApplicationData));
          assert (final_model.CS.model_control == CS.ControlApplicationData);
          assert False)
      | _ ->
        lemma_server_hello_window_rank_step model ev model1;
        (match model1.CS.model_control with
        | CS.ControlFailed _ ->
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
          CSL.lemma_step_model_preserves_config model ev model1;
          assert (model1.CS.model_config == model.CS.model_config);
          lemma_server_hello_window_rank_replay_lower_bound
            model1
            rest
            tail_sent
            tail_received
            final_model;
          assert (server_hello_window_rank model <=
            server_hello_window_rank model1 + 1);
          assert (server_hello_window_rank model1 <= FStar.List.Tot.length rest);
          assert (FStar.List.Tot.length (ev :: rest) == FStar.List.Tot.length rest + 1))
    )

(**
  See the [.fsti] comment for why this auxiliary fact is necessary in
  addition to the numeric rank bound above.
**)
let rec lemma_server_hello_window_stuck_without_client_handshake_traffic
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        (model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent \/
         model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent) /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        CS.conn_events_raw_replay model events raw_sent raw_received final_model)
      (ensures ~ (final_model.CS.model_control == CS.ControlApplicationData))
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      ~ (final_model.CS.model_control == CS.ControlApplicationData)
    with _.
    (
      CSL.lemma_step_model_preserves_config model ev model1;
      match model1.CS.model_control with
      | CS.ControlFailed _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model
      | _ ->
        // Establish that [model1] again satisfies the invariant (still one
        // of the two stages, still missing the client handshake traffic
        // key), then recurse; the one case that would violate the
        // invariant ([Received Finished] at [HsServerFinishedSent]) is
        // ruled out directly because it requires
        // [Some? ks_client_handshake_traffic], contradicting our hypothesis.
        (match ev with
        | CS.ConnLocalEvent local ->
          assert (CS.legal_local_event model local);
          assert (CS.step_local_event model local == Some model1);
          (match local with
          | CS.LocalInstallTrafficKeys _ ->
            assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert False
          | CS.LocalInstallTrafficKeysForRole role_install ->
            let install = role_install.CS.install_payload in
            assert (role_install.CS.install_role == CS.ServerEndpoint);
            (match model.CS.model_control with
            | CS.ControlHandshaking stage ->
              assert (CS.traffic_install_allowed_at_stage_for_role
                CS.ServerEndpoint
                stage
                install);
              (match stage, install.CS.install_epoch, install.CS.install_direction with
              | CS.HsServerFinishedSent, CS.TrafficApplication, CS.TrafficWrite ->
                assert (model1.CS.model_control ==
                  CS.ControlHandshaking CS.HsServerFinishedSent);
                assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                  model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
                lemma_server_hello_window_stuck_without_client_handshake_traffic
                  model1
                  rest
                  tail_sent
                  tail_received
                  final_model
              | _, _, _ ->
                assert False)
            | _ ->
              assert False)
          | CS.LocalSignCertificateVerify _ ->
            assert (model.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
            assert (model1.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
            assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
              model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
            lemma_server_hello_window_stuck_without_client_handshake_traffic
              model1
              rest
              tail_sent
              tail_received
              final_model
          | CS.LocalFail _ ->
            assert False
          | _ ->
            assert (CS.step_local_event model local == None);
            assert False)
        | CS.ConnNetworkEvent msg ->
          assert (CS.legal_tls_message
            model
            msg.CL.message_direction
            msg.CL.message_value);
          assert (CS.step_tls_message
            model
            msg.CL.message_direction
            msg.CL.message_value == Some model1);
          (match msg.CL.message_value with
          | M.TlsAlert _ ->
            assert False
          | M.TlsChangeCipherSpec ->
            assert (model1 == model);
            lemma_server_hello_window_stuck_without_client_handshake_traffic
              model1
              rest
              tail_sent
              tail_received
              final_model
          | M.TlsHandshake hs_msg ->
            (match model.CS.model_control, msg.CL.message_direction, hs_msg with
            | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
              CL.Sent,
              M.Certificate _ ->
              assert (model1.CS.model_control ==
                CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
              assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
              lemma_server_hello_window_stuck_without_client_handshake_traffic
                model1
                rest
                tail_sent
                tail_received
                final_model
            | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
              CL.Sent,
              M.CertificateVerify _ ->
              assert (model1.CS.model_control ==
                CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
              assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
              lemma_server_hello_window_stuck_without_client_handshake_traffic
                model1
                rest
                tail_sent
                tail_received
                final_model
            | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
              CL.Sent,
              M.Finished _ ->
              assert (model1.CS.model_control ==
                CS.ControlHandshaking CS.HsServerFinishedSent);
              assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
              lemma_server_hello_window_stuck_without_client_handshake_traffic
                model1
                rest
                tail_sent
                tail_received
                final_model
            | CS.ControlHandshaking CS.HsServerFinishedSent,
              CL.Received,
              M.Finished _ ->
              // Ruled out directly: this transition's own legality requires
              // [Some? ks_client_handshake_traffic], contradicting our
              // hypothesis that it is [None].
              assert (Some?
                model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
              assert False
            | _, _, _ ->
              assert (CS.step_handshake_message
                model
                msg.CL.message_direction
                hs_msg == None);
              assert False)
          | M.TlsApplicationData _ ->
            assert False
          | M.TlsIgnoredPostHandshake _ ->
            assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert False
          | M.TlsKeyUpdate _ ->
            assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert False))
    )

let lemma_server_hello_window_tight_next_event_handshake_traffic_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        ~ (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
           Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic) /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_hello_window_rank final_model == 0 /\
        server_hello_window_rank model == FStar.List.Tot.length rest + 1)
      (ensures PNI.server_no_tail_handshake_traffic_install_event ev)
=
  assert_norm (
    CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev /\
    CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
  returns PNI.server_no_tail_handshake_traffic_install_event ev
  with _.
  (
    match model1.CS.model_control with
    | CS.ControlFailed _ ->
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
      lemma_server_hello_window_rank_step model ev model1;
      CSL.lemma_step_model_preserves_config model ev model1;
      lemma_server_hello_window_rank_replay_lower_bound
        model1
        rest
        tail_sent
        tail_received
        final_model;
      assert (server_hello_window_rank model1 <= FStar.List.Tot.length rest);
      (match ev with
      | CS.ConnLocalEvent local ->
        assert (CS.legal_local_event model local);
        (match local with
        | CS.LocalInstallTrafficKeysForRole role_install ->
          let install = role_install.CS.install_payload in
          assert (role_install.CS.install_role == CS.ServerEndpoint);
          assert (CS.traffic_install_allowed_at_stage_for_role
            CS.ServerEndpoint
            CS.HsServerHelloSent
            install);
          (match install.CS.install_epoch, install.CS.install_direction with
          | CS.TrafficHandshake, CS.TrafficWrite ->
            assert (PNI.server_no_tail_handshake_traffic_install_event ev)
          | CS.TrafficHandshake, CS.TrafficRead ->
            assert (PNI.server_no_tail_handshake_traffic_install_event ev)
          | CS.TrafficApplication, _ ->
            assert False)
        | CS.LocalInstallTrafficKeys _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | CS.LocalFail _ ->
          assert False
        | _ ->
          assert (CS.step_local_event model local == None);
          assert False)
      | CS.ConnNetworkEvent msg ->
        assert (CS.legal_tls_message
          model
          msg.CL.message_direction
          msg.CL.message_value);
        (match msg.CL.message_value with
        | M.TlsAlert _ ->
          assert False
        | M.TlsChangeCipherSpec ->
          assert (model1 == model);
          assert (server_hello_window_rank model <= FStar.List.Tot.length rest);
          assert False
        | M.TlsHandshake hs_msg ->
          (match msg.CL.message_direction, hs_msg with
          | CL.Sent, M.EncryptedExtensions ee ->
            assert (CS.legal_handshake_message
              model
              CL.Sent
              (M.EncryptedExtensions ee));
            assert (Some?
              model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
            assert (model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
              None);
            let hs0 = model.CS.model_handshake in
            let model_after =
              CS.with_handshake_stage
                {
                  model with
                    CS.model_record = {
                      model.CS.model_record with
                        CS.record_write = R.next_seq model.CS.model_record.CS.record_write;
                    };
                }
                (CS.append_handshake_to_transcript
                  { hs0 with CS.hs_encrypted_extensions = Some ee }
                  (M.EncryptedExtensions ee))
                CS.HsServerEncryptedFlightSent in
            assert_norm (
              CS.step_tls_message
                model
                CL.Sent
                (M.TlsHandshake (M.EncryptedExtensions ee)) ==
              Some model_after);
            assert (model1 == model_after);
            assert (model1.CS.model_control ==
              CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
            assert (model1.CS.model_handshake.CS.hs_keys ==
              model.CS.model_handshake.CS.hs_keys);
            assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
              None);
            lemma_server_hello_window_stuck_without_client_handshake_traffic
              model1
              rest
              tail_sent
              tail_received
              final_model;
            assert (~ (final_model.CS.model_control == CS.ControlApplicationData));
            assert False
          | _, _ ->
            assert (CS.step_handshake_message
              model
              msg.CL.message_direction
              hs_msg == None);
            assert False)
        | M.TlsApplicationData _ ->
          assert False
        | M.TlsIgnoredPostHandshake _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | M.TlsKeyUpdate _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False))
  )

let lemma_server_hello_window_after_fresh_handshake_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model' /\
        PNI.server_no_tail_handshake_traffic_install_event ev)
      (ensures
        model'.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model'.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model'.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        ~ (Some? model'.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
           Some? model'.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic) /\
        model'.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model'.CS.model_handshake.CS.hs_certificate == None /\
        model'.CS.model_handshake.CS.hs_certificate_verify == None /\
        model'.CS.model_handshake.CS.hs_certificate_verify_verified == false)
=
  match ev with
  | CS.ConnLocalEvent local ->
    assert (CS.legal_local_event model local);
    assert (CS.step_local_event model local == Some model');
    (match local with
    | CS.LocalInstallTrafficKeysForRole role_install ->
      let install = role_install.CS.install_payload in
      assert (role_install.CS.install_role == CS.ServerEndpoint);
      assert (install.CS.install_epoch == CS.TrafficHandshake);
      assert (CS.traffic_install_allowed_at_stage_for_role
        CS.ServerEndpoint
        CS.HsServerHelloSent
        install);
      let keys' =
        CS.update_key_schedule_with_install_for_role
          CS.ServerEndpoint
          model.CS.model_handshake.CS.hs_keys
          install in
      let model_after = {
        model with
          CS.model_record =
            CS.install_record_keys_for_role
              CS.ServerEndpoint
              model.CS.model_record
              install;
          CS.model_handshake = {
            model.CS.model_handshake with
              CS.hs_keys = keys';
          };
      } in
      assert_norm (
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) ==
        Some model_after);
      assert (model' == model_after);
      assert (model'.CS.model_config == model.CS.model_config);
      assert (model'.CS.model_control == model.CS.model_control);
      assert (model'.CS.model_handshake.CS.hs_encrypted_extensions ==
        model.CS.model_handshake.CS.hs_encrypted_extensions);
      assert (model'.CS.model_handshake.CS.hs_certificate ==
        model.CS.model_handshake.CS.hs_certificate);
      assert (model'.CS.model_handshake.CS.hs_certificate_verify ==
        model.CS.model_handshake.CS.hs_certificate_verify);
      assert (model'.CS.model_handshake.CS.hs_certificate_verify_verified ==
        model.CS.model_handshake.CS.hs_certificate_verify_verified);
      assert (model'.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
      (match install.CS.install_direction with
      | CS.TrafficWrite ->
        assert_norm
          (CS.traffic_label_for_endpoint_direction
            CS.ServerEndpoint
            CS.TrafficWrite == CS.ServerTraffic);
        assert (model'.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
          model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
        assert (model'.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None)
      | CS.TrafficRead ->
        assert_norm
          (CS.traffic_label_for_endpoint_direction
            CS.ServerEndpoint
            CS.TrafficRead == CS.ClientTraffic);
        assert (model'.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic ==
          model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
        assert (model'.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None))
    | _ ->
      assert False)
  | _ ->
    assert False

let lemma_server_hello_window_tight_next_two_events_handshake_traffic_installs
  (model:CS.connection_model)
  (ev0:CS.conn_event)
  (ev1:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        CS.conn_events_raw_replay
          model
          (ev0 :: ev1 :: rest)
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_hello_window_rank final_model == 0 /\
        server_hello_window_rank model ==
          FStar.List.Tot.length (ev1 :: rest) + 1)
      (ensures
        PNI.server_no_tail_handshake_traffic_install_event ev0 /\
        PNI.server_no_tail_handshake_traffic_install_event ev1)
=
  lemma_server_hello_window_tight_next_event_handshake_traffic_install
    model
    ev0
    (ev1 :: rest)
    raw_sent
    raw_received
    final_model;
  assert (PNI.server_no_tail_handshake_traffic_install_event ev0);
  assert_norm (
    CS.conn_events_raw_replay model (ev0 :: ev1 :: rest) raw_sent raw_received final_model ==
    (exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev0 /\
      CS.step_model model ev0 == Some model1 /\
      CS.event_raw_delta_legal model ev0 delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 (ev1 :: rest) tail_sent tail_received final_model));
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    CS.legal_event model ev0 /\
    CS.step_model model ev0 == Some model1 /\
    CS.event_raw_delta_legal model ev0 delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    CS.conn_events_raw_replay model1 (ev1 :: rest) tail_sent tail_received final_model
  returns
    PNI.server_no_tail_handshake_traffic_install_event ev0 /\
    PNI.server_no_tail_handshake_traffic_install_event ev1
  with _.
  (
    lemma_server_hello_window_after_fresh_handshake_install
      model
      ev0
      model1;
    lemma_server_hello_window_rank_step model ev0 model1;
    assert (server_hello_window_rank model <=
      server_hello_window_rank model1 + 1);
    lemma_server_hello_window_rank_replay_lower_bound
      model1
      (ev1 :: rest)
      tail_sent
      tail_received
      final_model;
    assert (server_hello_window_rank model1 <=
      FStar.List.Tot.length (ev1 :: rest));
    assert_norm (FStar.List.Tot.length (ev1 :: rest) ==
      FStar.List.Tot.length rest + 1);
    assert (server_hello_window_rank model1 == FStar.List.Tot.length rest + 1);
    lemma_server_hello_window_tight_next_event_handshake_traffic_install
      model1
      ev1
      rest
      tail_sent
      tail_received
      final_model;
    assert (PNI.server_no_tail_handshake_traffic_install_event ev1)
  )

#pop-options
