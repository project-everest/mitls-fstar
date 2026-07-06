module TLS13.Impl.Driver.PairingNoTailClientProtectedShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

noextract
let client_after_two_handshake_installs_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

let lemma_client_after_two_install_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_two_handshake_installs_model model)
      (ensures PNI.client_application_progress_rank model == 10)
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
    | Some _, Some _, Some _, None, None ->
      assert (PNI.option_missing keys.CS.ks_shared_secret == 0);
      assert (PNI.option_missing keys.CS.ks_client_handshake_traffic == 0);
      assert (PNI.option_missing keys.CS.ks_server_handshake_traffic == 0);
      assert (PNI.client_app_obligation_rank keys == 2);
      assert (PNI.client_early_obligation_rank keys == 2);
      assert (PNI.client_application_progress_rank model == 10)
    | _, _, _, _, _ ->
      assert False)
  | _ ->
    assert False

noextract
let client_after_encrypted_extensions_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

let lemma_client_after_encrypted_extensions_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_encrypted_extensions_model model)
      (ensures PNI.client_application_progress_rank model == 9)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived ->
    (match
      keys.CS.ks_shared_secret,
      keys.CS.ks_client_handshake_traffic,
      keys.CS.ks_client_application_traffic,
      keys.CS.ks_server_application_traffic
    with
    | Some _, Some _, None, None ->
      assert (PNI.option_missing keys.CS.ks_shared_secret == 0);
      assert (PNI.option_missing keys.CS.ks_client_handshake_traffic == 0);
      assert (PNI.client_app_obligation_rank keys == 2);
      assert (PNI.client_late_obligation_rank keys == 2);
      assert (PNI.client_application_progress_rank model == 9)
    | _, _, _, _ ->
      assert False)
  | _ ->
    assert False

let lemma_client_after_certificate_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_certificate_model model)
      (ensures PNI.client_application_progress_rank model == 8)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsCertificateReceived ->
    (match
      keys.CS.ks_shared_secret,
      keys.CS.ks_client_handshake_traffic,
      keys.CS.ks_client_application_traffic,
      keys.CS.ks_server_application_traffic
    with
    | Some _, Some _, None, None ->
      assert (PNI.option_missing keys.CS.ks_shared_secret == 0);
      assert (PNI.option_missing keys.CS.ks_client_handshake_traffic == 0);
      assert (PNI.client_app_obligation_rank keys == 2);
      assert (PNI.client_late_obligation_rank keys == 2);
      assert (PNI.client_application_progress_rank model == 8)
    | _, _, _, _ ->
      assert False)
  | _ ->
    assert False

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_encrypted_extensions_step_model_shape
  (model6 model7:CS.connection_model)
  (ee:M.encrypted_extensions)
  : Lemma
      (requires
        client_after_two_handshake_installs_model model6 /\
        CS.step_model
          model6
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          }) == Some model7)
      (ensures client_after_encrypted_extensions_model model7)
=
  CSL.lemma_step_model_preserves_config
    model6
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    })
    model7;
  assert_norm (
    CS.step_model
      model6
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ==
    Some (CS.with_handshake_stage
      { model6 with
          CS.model_record = {
            model6.CS.model_record with
              CS.record_read = R.next_seq model6.CS.model_record.CS.record_read;
          };
      }
      (CS.append_handshake_to_transcript
        { model6.CS.model_handshake with CS.hs_encrypted_extensions = Some ee }
        (M.EncryptedExtensions ee))
      CS.HsEncryptedExtensionsReceived));
  assert (model7.CS.model_config == model6.CS.model_config)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_certificate_step_model_shape
  (model7 model8:CS.connection_model)
  (cert:M.certificate_msg)
  : Lemma
      (requires
        client_after_encrypted_extensions_model model7 /\
        CS.step_model
          model7
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          }) == Some model8)
      (ensures client_after_certificate_model model8)
=
  CSL.lemma_step_model_preserves_config
    model7
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    })
    model8;
  assert_norm (
    CS.step_model
      model7
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ==
    Some (CS.with_handshake_stage
      { model7 with
          CS.model_record = {
            model7.CS.model_record with
              CS.record_read = R.next_seq model7.CS.model_record.CS.record_read;
          };
      }
      (CS.append_handshake_to_transcript
        { model7.CS.model_handshake with
            CS.hs_certificate = Some cert;
            CS.hs_buffers =
              { model7.CS.model_handshake.CS.hs_buffers with
                  CS.hb_certificate_leaf_der =
                    (match cert.M.chain with
                     | leaf :: _ -> Some leaf
                     | [] -> None);
              };
        }
        (M.Certificate cert))
      CS.HsCertificateReceived));
  assert (model8.CS.model_config == model7.CS.model_config)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_two_install_local_install_progress_rank
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_after_two_handshake_installs_model model /\
        CS.legal_event model ev /\
        (match ev with
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> True
         | _ -> False) /\
        CS.step_model model ev == Some model1)
      (ensures PNI.client_application_progress_rank model1 == 10)
=
  CSL.lemma_step_model_preserves_config model ev model1;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (CS.legal_local_event model (CS.LocalInstallTrafficKeys install));
    assert (CS.traffic_install_allowed_at_stage CS.HsServerHelloReceived install);
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert (
         CS.step_model model ev ==
         Some {
           model with
             CS.model_record = CS.install_record_keys model.CS.model_record install;
             CS.model_handshake = {
               model.CS.model_handshake with
                 CS.hs_keys =
                   CS.update_key_schedule_with_install
                     model.CS.model_handshake.CS.hs_keys
                     install;
             };
         });
       (match install.CS.install_direction with
        | CS.TrafficWrite ->
          assert_norm (
            CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
            CS.ClientTraffic);
          assert_norm (
            CS.update_key_schedule_with_label
              model.CS.model_handshake.CS.hs_keys
              CS.TrafficHandshake
              CS.ClientTraffic
              install.CS.install_material ==
            { model.CS.model_handshake.CS.hs_keys with
                CS.ks_client_handshake_traffic = Some install.CS.install_material })
        | CS.TrafficRead ->
          assert_norm (
            CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
            CS.ServerTraffic);
          assert_norm (
            CS.update_key_schedule_with_label
              model.CS.model_handshake.CS.hs_keys
              CS.TrafficHandshake
              CS.ServerTraffic
              install.CS.install_material ==
            { model.CS.model_handshake.CS.hs_keys with
                CS.ks_server_handshake_traffic = Some install.CS.install_material }));
       assert (client_after_two_handshake_installs_model model1);
       lemma_client_after_two_install_progress_rank model1
     | CS.TrafficApplication ->
       assert_norm (CS.traffic_install_allowed_at_stage
         CS.HsServerHelloReceived
         install == False);
       assert False)
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (CS.legal_local_event model (CS.LocalInstallTrafficKeysForRole role_install));
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ClientEndpoint
      CS.HsServerHelloReceived
      role_install.CS.install_payload);
    let install = role_install.CS.install_payload in
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert (
         CS.step_model model ev ==
         Some {
           model with
             CS.model_record =
               CS.install_record_keys_for_role
                 role_install.CS.install_role
                 model.CS.model_record
                 install;
             CS.model_handshake = {
               model.CS.model_handshake with
                 CS.hs_keys =
                   CS.update_key_schedule_with_install_for_role
                     role_install.CS.install_role
                     model.CS.model_handshake.CS.hs_keys
                     install;
             };
         });
       (match install.CS.install_direction with
        | CS.TrafficWrite ->
          assert_norm (
            CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
            CS.ClientTraffic);
          assert_norm (
            CS.update_key_schedule_with_label
              model.CS.model_handshake.CS.hs_keys
              CS.TrafficHandshake
              CS.ClientTraffic
              install.CS.install_material ==
            { model.CS.model_handshake.CS.hs_keys with
                CS.ks_client_handshake_traffic = Some install.CS.install_material })
        | CS.TrafficRead ->
          assert_norm (
            CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
            CS.ServerTraffic);
          assert_norm (
            CS.update_key_schedule_with_label
              model.CS.model_handshake.CS.hs_keys
              CS.TrafficHandshake
              CS.ServerTraffic
              install.CS.install_material ==
            { model.CS.model_handshake.CS.hs_keys with
                CS.ks_server_handshake_traffic = Some install.CS.install_material }));
       assert (client_after_two_handshake_installs_model model1);
       lemma_client_after_two_install_progress_rank model1
     | CS.TrafficApplication ->
       assert_norm (CS.traffic_install_allowed_at_stage_for_role
         CS.ClientEndpoint
         CS.HsServerHelloReceived
         install == False);
       assert False)
  | _ ->
    assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_two_install_local_derive_progress_rank
  (model model1:CS.connection_model)
  (shared:C.x25519_shared_secret)
  : Lemma
      (requires
        client_after_two_handshake_installs_model model /\
        CS.legal_event model (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) /\
        CS.step_model model (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
          Some model1)
      (ensures PNI.client_application_progress_rank model1 == 10)
=
  CSL.lemma_step_model_preserves_config
    model
    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared))
    model1;
  assert (
    CS.step_model model (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
    Some (CS.derive_shared_secret_model model model.CS.model_handshake shared));
  assert (model1 == CS.derive_shared_secret_model model model.CS.model_handshake shared);
  assert (client_after_two_handshake_installs_model model1);
  lemma_client_after_two_install_progress_rank model1
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_two_installs_next_event_encrypted_extensions
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_two_handshake_installs_model model /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 9)
      (ensures
        exists ee.
          ev == CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          })
=
  lemma_client_after_two_install_progress_rank model;
  assert (PNI.client_application_progress_rank model == 10);
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
    exists ee.
      ev == CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }
  with _.
  (
    CSL.lemma_step_model_preserves_config model ev model1;
    match ev with
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalFail err ->
         assert (model1.CS.model_control == CS.ControlFailed err);
         PNI.lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (CS.ControlFailed? final_model.CS.model_control);
         assert False
       | CS.LocalDeriveSharedSecret shared ->
         lemma_client_after_two_install_local_derive_progress_rank model model1 shared;
         PNI.lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (PNI.client_application_progress_rank model1 == 10);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (10 <= 9);
         assert False
       | CS.LocalInstallTrafficKeys _
       | CS.LocalInstallTrafficKeysForRole _ ->
         lemma_client_after_two_install_local_install_progress_rank model model1 ev;
         PNI.lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (PNI.client_application_progress_rank model1 == 10);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (10 <= 9);
         assert False
       | _ ->
         PNI.lemma_client_hs_server_hello_received_local_event_step_none model local;
         assert (CS.step_model model ev == None);
         assert False)
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsAlert alert ->
         assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
         PNI.lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (CS.ControlFailed? final_model.CS.model_control);
         assert False
       | M.TlsChangeCipherSpec ->
         assert_norm (CS.step_model model ev == Some model);
         assert (model1 == model);
         PNI.lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (PNI.client_application_progress_rank model1 == 10);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (10 <= 9);
         assert False
       | M.TlsHandshake hs ->
         (match msg.CL.message_direction, hs with
          | CL.Received, M.EncryptedExtensions ee ->
            introduce exists (ee':M.encrypted_extensions).
              ev == CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
              }
            with ee and ()
          | _, _ ->
            PNI.lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
              model
              msg;
            assert (CS.step_model model ev == None);
            assert False)
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         PNI.lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False)
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_seventh_event_encrypted_extensions_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_first_protected_receive_shape client)
=
  PNI.lemma_client_no_tail_model4_witness client;
  PCPS.lemma_client_no_tail_fifth_and_sixth_events_handshake_install_cover_clean client;
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
    CS.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_first_protected_receive_shape client
  with _.
  (
    eliminate exists start' ch' sh' client_shared' e4' e5' rest'.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch');
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh');
        }) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
        e4' ::
        e5' ::
        rest' /\
      PCPS.client_no_tail_two_handshake_install_cover e4' e5'
    returns client_no_tail_first_protected_receive_shape client
    with _.
    (
      assert (start' == start);
      assert (ch' == ch);
      assert (sh' == sh);
      assert (client_shared' == client_shared);
      assert (e4' == e4);
      match rest with
      | e5 :: rest2 ->
        assert (e5' == e5);
        assert (rest' == rest2);
        assert (PCPS.client_no_tail_two_handshake_install_cover e4 e5);
        assert (FStar.List.Tot.length rest2 == 10);
        assert_norm (
          CS.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model ==
          (exists model5 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model4 e4 /\
            CS.step_model model4 e4 == Some model5 /\
            CS.event_raw_delta_legal model4 e4 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model5 rest tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model5 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model4 e4 /\
          CS.step_model model4 e4 == Some model5 /\
          CS.event_raw_delta_legal model4 e4 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model5 rest tail_sent2 tail_received2 client.CS.cs_model
        returns client_no_tail_first_protected_receive_shape client
        with _.
        (
          assert_norm (
            CS.conn_events_raw_replay model5 (e5 :: rest2) tail_sent2 tail_received2 client.CS.cs_model ==
            (exists model6 delta_sent2 delta_received2 tail_sent3 tail_received3.
              CS.legal_event model5 e5 /\
              CS.step_model model5 e5 == Some model6 /\
              CS.event_raw_delta_legal model5 e5 delta_sent2 delta_received2 /\
              Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
              Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
              CS.conn_events_raw_replay model6 rest2 tail_sent3 tail_received3 client.CS.cs_model));
          eliminate exists model6 delta_sent2 delta_received2 tail_sent3 tail_received3.
            CS.legal_event model5 e5 /\
            CS.step_model model5 e5 == Some model6 /\
            CS.event_raw_delta_legal model5 e5 delta_sent2 delta_received2 /\
            Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
            Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
            CS.conn_events_raw_replay model6 rest2 tail_sent3 tail_received3 client.CS.cs_model
          returns client_no_tail_first_protected_receive_shape client
          with _.
          (
            PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
            if
              PCPS.client_no_tail_handshake_write_install_event e4 /\
              PCPS.client_no_tail_handshake_read_install_event e5
            then (
              assert (PCPS.client_no_tail_handshake_write_install_event e4);
              assert (PCPS.client_no_tail_handshake_read_install_event e5);
              PCPS.lemma_client_no_tail_handshake_write_install_event_implies_handshake_traffic_install_event e4;
              PCPS.lemma_client_no_tail_handshake_read_install_event_implies_handshake_traffic_install_event e5
            ) else (
              assert (
                PCPS.client_no_tail_handshake_read_install_event e4 /\
                PCPS.client_no_tail_handshake_write_install_event e5);
              assert (PCPS.client_no_tail_handshake_read_install_event e4);
              assert (PCPS.client_no_tail_handshake_write_install_event e5);
              PCPS.lemma_client_no_tail_handshake_read_install_event_implies_handshake_traffic_install_event e4;
              PCPS.lemma_client_no_tail_handshake_write_install_event_implies_handshake_traffic_install_event e5
            );
            assert (PNI.client_no_tail_handshake_traffic_install_event e4);
            assert (PNI.client_no_tail_handshake_traffic_install_event e5);
            PCPS.lemma_client_two_handshake_install_cover_model_shape model4 model5 model6 e4 e5;
            assert (client_after_two_handshake_installs_model model6);
            match rest2 with
            | e6 :: rest3 ->
              assert (FStar.List.Tot.length rest3 == 9);
              lemma_client_after_two_installs_next_event_encrypted_extensions
                model6
                e6
                rest3
                tail_sent3
                tail_received3
                client.CS.cs_model;
              eliminate exists ee.
                e6 == CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                }
              returns client_no_tail_first_protected_receive_shape client
              with _.
              (
                introduce exists
                  (start0:CS.handshake_start)
                  (ch0:M.client_hello)
                  (sh0:M.server_hello)
                  (client_shared0:C.x25519_shared_secret)
                  (e40:CS.conn_event)
                  (e50:CS.conn_event)
                  (ee0:M.encrypted_extensions)
                  (rest0:list CS.conn_event).
                  client.CS.cs_event_log ==
                    CS.ConnLocalEvent (CS.LocalStartHandshake start0) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                    }) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh0);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared0) ::
                    e40 ::
                    e50 ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee0);
                    }) ::
                    rest0 /\
                  PCPS.client_no_tail_two_handshake_install_cover e40 e50
                with start ch sh client_shared e4 e5 ee rest3 and ()
              )
          )
        )
    )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model6_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
            e5 ::
            rest2 /\
          FStar.List.Tot.length rest2 == 10 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_two_handshake_installs_model model6 /\
          CS.conn_events_raw_replay
            model6
            rest2
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  PNI.lemma_client_no_tail_model4_witness client;
  PCPS.lemma_client_no_tail_fifth_and_sixth_events_handshake_install_cover_clean client;
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
    CS.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
        e5 ::
        rest2 /\
      FStar.List.Tot.length rest2 == 10 /\
      PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
      client_after_two_handshake_installs_model model6 /\
      CS.conn_events_raw_replay
        model6
        rest2
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    eliminate exists start' ch' sh' client_shared' e4' e5' rest'.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch');
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh');
        }) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
        e4' ::
        e5' ::
        rest' /\
      PCPS.client_no_tail_two_handshake_install_cover e4' e5'
    returns
      exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
          e5 ::
          rest2 /\
        FStar.List.Tot.length rest2 == 10 /\
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        client_after_two_handshake_installs_model model6 /\
        CS.conn_events_raw_replay
          model6
          rest2
          tail_sent
          tail_received
          client.CS.cs_model /\
        PNI.client_application_progress_rank client.CS.cs_model == 0
    with _.
    (
      assert (start' == start);
      assert (ch' == ch);
      assert (sh' == sh);
      assert (client_shared' == client_shared);
      assert (e4' == e4);
      match rest with
      | e5 :: rest2 ->
        assert (e5' == e5);
        assert (rest' == rest2);
        assert (PCPS.client_no_tail_two_handshake_install_cover e4 e5);
        assert (FStar.List.Tot.length rest2 == 10);
        assert_norm (
          CS.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model ==
          (exists model5 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model4 e4 /\
            CS.step_model model4 e4 == Some model5 /\
            CS.event_raw_delta_legal model4 e4 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model5 rest tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model5 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model4 e4 /\
          CS.step_model model4 e4 == Some model5 /\
          CS.event_raw_delta_legal model4 e4 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model5 rest tail_sent2 tail_received2 client.CS.cs_model
        returns
          exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
              e5 ::
              rest2 /\
            FStar.List.Tot.length rest2 == 10 /\
            PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
            client_after_two_handshake_installs_model model6 /\
            CS.conn_events_raw_replay
              model6
              rest2
              tail_sent
              tail_received
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
        with _.
        (
          assert_norm (
            CS.conn_events_raw_replay model5 (e5 :: rest2) tail_sent2 tail_received2 client.CS.cs_model ==
            (exists model6 delta_sent2 delta_received2 tail_sent3 tail_received3.
              CS.legal_event model5 e5 /\
              CS.step_model model5 e5 == Some model6 /\
              CS.event_raw_delta_legal model5 e5 delta_sent2 delta_received2 /\
              Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
              Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
              CS.conn_events_raw_replay model6 rest2 tail_sent3 tail_received3 client.CS.cs_model));
          eliminate exists model6 delta_sent2 delta_received2 tail_sent3 tail_received3.
            CS.legal_event model5 e5 /\
            CS.step_model model5 e5 == Some model6 /\
            CS.event_raw_delta_legal model5 e5 delta_sent2 delta_received2 /\
            Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
            Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
            CS.conn_events_raw_replay model6 rest2 tail_sent3 tail_received3 client.CS.cs_model
          returns
            exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
                e5 ::
                rest2 /\
              FStar.List.Tot.length rest2 == 10 /\
              PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
              client_after_two_handshake_installs_model model6 /\
              CS.conn_events_raw_replay
                model6
                rest2
                tail_sent
                tail_received
                client.CS.cs_model /\
              PNI.client_application_progress_rank client.CS.cs_model == 0
          with _.
          (
            PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
            if
              PCPS.client_no_tail_handshake_write_install_event e4 /\
              PCPS.client_no_tail_handshake_read_install_event e5
            then (
              PCPS.lemma_client_no_tail_handshake_write_install_event_implies_handshake_traffic_install_event e4;
              PCPS.lemma_client_no_tail_handshake_read_install_event_implies_handshake_traffic_install_event e5
            ) else (
              assert (
                PCPS.client_no_tail_handshake_read_install_event e4 /\
                PCPS.client_no_tail_handshake_write_install_event e5);
              PCPS.lemma_client_no_tail_handshake_read_install_event_implies_handshake_traffic_install_event e4;
              PCPS.lemma_client_no_tail_handshake_write_install_event_implies_handshake_traffic_install_event e5
            );
            assert (PNI.client_no_tail_handshake_traffic_install_event e4);
            assert (PNI.client_no_tail_handshake_traffic_install_event e5);
            PCPS.lemma_client_two_handshake_install_cover_model_shape model4 model5 model6 e4 e5;
            introduce exists
              (start0:CS.handshake_start)
              (ch0:M.client_hello)
              (sh0:M.server_hello)
              (client_shared0:C.x25519_shared_secret)
              (e40:CS.conn_event)
              (e50:CS.conn_event)
              (rest20:list CS.conn_event)
              (model60:CS.connection_model)
              (tail_sent0:B.bytes)
              (tail_received0:B.bytes).
              client.CS.cs_event_log ==
                CS.ConnLocalEvent (CS.LocalStartHandshake start0) ::
                CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                }) ::
                CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ServerHello sh0);
                }) ::
                CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared0) ::
                e40 ::
                e50 ::
                rest20 /\
              FStar.List.Tot.length rest20 == 10 /\
              PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
              client_after_two_handshake_installs_model model60 /\
              CS.conn_events_raw_replay
                model60
                rest20
                tail_sent0
                tail_received0
                client.CS.cs_model /\
              PNI.client_application_progress_rank client.CS.cs_model == 0
            with start ch sh client_shared e4 e5 rest2 model6 tail_sent3 tail_received3 and ()
          )
        )
    )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_encrypted_extensions_next_event_certificate
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_encrypted_extensions_model model /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 8)
      (ensures
        exists cert.
          ev == CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          })
=
  lemma_client_after_encrypted_extensions_progress_rank model;
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
    exists cert.
      ev == CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }
  with _.
  (
    match ev with
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalFail err ->
         assert (model1.CS.model_control == CS.ControlFailed err);
         PNI.lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert False
       | CS.LocalInstallTrafficKeys install ->
         assert (CS.legal_local_event model local);
         assert (CS.traffic_install_allowed_at_stage CS.HsEncryptedExtensionsReceived install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication -> assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsEncryptedExtensionsReceived
           role_install.CS.install_payload);
         (match role_install.CS.install_payload.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication -> assert False)
       | _ ->
         assert (CS.legal_local_event model local);
         assert False)
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsAlert alert ->
         assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
         PNI.lemma_conn_events_raw_replay_from_failed_results_failed
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert False
       | M.TlsChangeCipherSpec ->
         assert_norm (CS.step_model model ev == Some model);
         assert (model1 == model);
         PNI.lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (PNI.client_application_progress_rank model1 == 9);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (9 <= 8);
         assert False
       | M.TlsHandshake hs ->
         (match msg.CL.message_direction, hs with
          | CL.Received, M.Certificate cert ->
            introduce exists (cert':M.certificate_msg).
              ev == CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert');
              }
            with cert and ()
          | _, _ ->
            assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
            assert False)
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_certificate_next_event_validate_certificate
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_certificate_model model /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 7)
      (ensures
        exists peer.
         ev == CS.ConnLocalEvent (CS.LocalValidateCertificate peer))
=
  lemma_client_after_certificate_progress_rank model;
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
    exists peer.
      ev == CS.ConnLocalEvent (CS.LocalValidateCertificate peer)
  with _.
  (
    match ev with
    | CS.ConnLocalEvent local ->
      (match local with
       | CS.LocalFail err ->
         assert (model1.CS.model_control == CS.ControlFailed err);
         PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model;
         assert False
       | CS.LocalValidateCertificate peer ->
         introduce exists (peer':X.peer_identity).
          ev == CS.ConnLocalEvent (CS.LocalValidateCertificate peer')
         with peer and ()
       | CS.LocalInstallTrafficKeys install ->
         assert (CS.legal_local_event model local);
         assert (CS.traffic_install_allowed_at_stage CS.HsCertificateReceived install);
         (match install.CS.install_epoch with
         | CS.TrafficHandshake -> assert False
         | CS.TrafficApplication -> assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
          CS.ClientEndpoint
          CS.HsCertificateReceived
          role_install.CS.install_payload);
         (match role_install.CS.install_payload.CS.install_epoch with
         | CS.TrafficHandshake -> assert False
         | CS.TrafficApplication -> assert False)
       | _ ->
         assert (CS.legal_local_event model local);
         assert False)
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsAlert alert ->
         assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
         PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model;
         assert False
       | M.TlsChangeCipherSpec ->
         assert_norm (CS.step_model model ev == Some model);
         assert (model1 == model);
         PNI.lemma_client_application_progress_rank_replay_lower_bound
          model1
          rest
          tail_sent
          tail_received
          final_model;
         assert (PNI.client_application_progress_rank model1 == 8);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (8 <= 7);
         assert False
       | M.TlsHandshake _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_eighth_event_certificate_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_second_protected_receive_shape client)
=
  lemma_client_no_tail_model6_witness client;
  eliminate exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
      e5 ::
      rest2 /\
    FStar.List.Tot.length rest2 == 10 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_two_handshake_installs_model model6 /\
    CS.conn_events_raw_replay
      model6
      rest2
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_second_protected_receive_shape client
  with _.
  (
    match rest2 with
    | e6 :: rest3 ->
      assert (FStar.List.Tot.length rest3 == 9);
      lemma_client_after_two_installs_next_event_encrypted_extensions
        model6
        e6
        rest3
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists ee.
        e6 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        }
      returns client_no_tail_second_protected_receive_shape client
      with _.
      (
        assert_norm (
          CS.conn_events_raw_replay model6 (e6 :: rest3) tail_sent tail_received client.CS.cs_model ==
          (exists model7 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model6 e6 /\
            CS.step_model model6 e6 == Some model7 /\
            CS.event_raw_delta_legal model6 e6 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model7 rest3 tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model7 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model6 e6 /\
          CS.step_model model6 e6 == Some model7 /\
          CS.event_raw_delta_legal model6 e6 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model7 rest3 tail_sent2 tail_received2 client.CS.cs_model
        returns client_no_tail_second_protected_receive_shape client
        with _.
        (
          lemma_client_encrypted_extensions_step_model_shape model6 model7 ee;
          assert (client_after_encrypted_extensions_model model7);
          match rest3 with
          | e7 :: rest4 ->
            assert (FStar.List.Tot.length rest4 == 8);
            lemma_client_after_encrypted_extensions_next_event_certificate
              model7
              e7
              rest4
              tail_sent2
              tail_received2
              client.CS.cs_model;
            eliminate exists cert.
              e7 == CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              }
            returns client_no_tail_second_protected_receive_shape client
            with _.
            (
              introduce exists
                (start0:CS.handshake_start)
                (ch0:M.client_hello)
                (sh0:M.server_hello)
                (client_shared0:C.x25519_shared_secret)
                (e40:CS.conn_event)
                (e50:CS.conn_event)
                (ee0:M.encrypted_extensions)
                (cert0:M.certificate_msg)
                (rest0:list CS.conn_event).
                client.CS.cs_event_log ==
                  CS.ConnLocalEvent (CS.LocalStartHandshake start0) ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                  }) ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh0);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared0) ::
                  e40 ::
                  e50 ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee0);
                  }) ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Certificate cert0);
                  }) ::
                  rest0 /\
                PCPS.client_no_tail_two_handshake_install_cover e40 e50
              with start ch sh client_shared e4 e5 ee cert rest4 and ()
            )
        )
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model8_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
            e5 ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            }) ::
            rest4 /\
          FStar.List.Tot.length rest4 == 8 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_certificate_model model8 /\
          CS.conn_events_raw_replay
            model8
            rest4
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  lemma_client_no_tail_model6_witness client;
  eliminate exists start ch sh client_shared e4 e5 rest2 model6 tail_sent tail_received.
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
      e5 ::
      rest2 /\
    FStar.List.Tot.length rest2 == 10 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_two_handshake_installs_model model6 /\
    CS.conn_events_raw_replay
      model6
      rest2
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
        e5 ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        }) ::
        rest4 /\
      FStar.List.Tot.length rest4 == 8 /\
      PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
      client_after_certificate_model model8 /\
      CS.conn_events_raw_replay
        model8
        rest4
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    match rest2 with
    | e6 :: rest3 ->
      assert (FStar.List.Tot.length rest3 == 9);
      lemma_client_after_two_installs_next_event_encrypted_extensions
        model6
        e6
        rest3
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists ee.
        e6 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        }
      returns
        exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
            e5 ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            }) ::
            rest4 /\
          FStar.List.Tot.length rest4 == 8 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_certificate_model model8 /\
          CS.conn_events_raw_replay
            model8
            rest4
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0
      with _.
      (
        assert_norm (
          CS.conn_events_raw_replay model6 (e6 :: rest3) tail_sent tail_received client.CS.cs_model ==
          (exists model7 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model6 e6 /\
            CS.step_model model6 e6 == Some model7 /\
            CS.event_raw_delta_legal model6 e6 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model7 rest3 tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model7 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model6 e6 /\
          CS.step_model model6 e6 == Some model7 /\
          CS.event_raw_delta_legal model6 e6 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model7 rest3 tail_sent2 tail_received2 client.CS.cs_model
        returns
          exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
              e5 ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              }) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              }) ::
              rest4 /\
            FStar.List.Tot.length rest4 == 8 /\
            PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
            client_after_certificate_model model8 /\
            CS.conn_events_raw_replay
              model8
              rest4
              tail_sent
              tail_received
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
        with _.
        (
          lemma_client_encrypted_extensions_step_model_shape model6 model7 ee;
          assert (client_after_encrypted_extensions_model model7);
          match rest3 with
          | e7 :: rest4 ->
            assert (FStar.List.Tot.length rest4 == 8);
            lemma_client_after_encrypted_extensions_next_event_certificate
              model7
              e7
              rest4
              tail_sent2
              tail_received2
              client.CS.cs_model;
            eliminate exists cert.
              e7 == CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              }
            returns
              exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
                  e5 ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                  }) ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Certificate cert);
                  }) ::
                  rest4 /\
                FStar.List.Tot.length rest4 == 8 /\
                PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
                client_after_certificate_model model8 /\
                CS.conn_events_raw_replay
                  model8
                  rest4
                  tail_sent
                  tail_received
                  client.CS.cs_model /\
                PNI.client_application_progress_rank client.CS.cs_model == 0
            with _.
            (
              assert_norm (
                CS.conn_events_raw_replay model7 (e7 :: rest4) tail_sent2 tail_received2 client.CS.cs_model ==
                (exists model8 delta_sent2 delta_received2 tail_sent3 tail_received3.
                  CS.legal_event model7 e7 /\
                  CS.step_model model7 e7 == Some model8 /\
                  CS.event_raw_delta_legal model7 e7 delta_sent2 delta_received2 /\
                  Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
                  Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
                  CS.conn_events_raw_replay model8 rest4 tail_sent3 tail_received3 client.CS.cs_model));
              eliminate exists model8 delta_sent2 delta_received2 tail_sent3 tail_received3.
                CS.legal_event model7 e7 /\
                CS.step_model model7 e7 == Some model8 /\
                CS.event_raw_delta_legal model7 e7 delta_sent2 delta_received2 /\
                Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
                Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
                CS.conn_events_raw_replay model8 rest4 tail_sent3 tail_received3 client.CS.cs_model
              returns
                exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
                    e5 ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                    }) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.Certificate cert);
                    }) ::
                    rest4 /\
                  FStar.List.Tot.length rest4 == 8 /\
                  PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
                  client_after_certificate_model model8 /\
                  CS.conn_events_raw_replay
                    model8
                    rest4
                    tail_sent
                    tail_received
                    client.CS.cs_model /\
                  PNI.client_application_progress_rank client.CS.cs_model == 0
              with _.
              (
                lemma_client_certificate_step_model_shape model7 model8 cert;
                assert (client_after_certificate_model model8);
                introduce exists
                  (start0:CS.handshake_start)
                  (ch0:M.client_hello)
                  (sh0:M.server_hello)
                  (client_shared0:C.x25519_shared_secret)
                  (e40:CS.conn_event)
                  (e50:CS.conn_event)
                  (ee0:M.encrypted_extensions)
                  (cert0:M.certificate_msg)
                  (rest40:list CS.conn_event)
                  (model80:CS.connection_model)
                  (tail_sent0:B.bytes)
                  (tail_received0:B.bytes).
                  client.CS.cs_event_log ==
                    CS.ConnLocalEvent (CS.LocalStartHandshake start0) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch0);
                    }) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh0);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared0) ::
                    e40 ::
                    e50 ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee0);
                    }) ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.Certificate cert0);
                    }) ::
                    rest40 /\
                  FStar.List.Tot.length rest40 == 8 /\
                  PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
                  client_after_certificate_model model80 /\
                  CS.conn_events_raw_replay
                    model80
                    rest40
                    tail_sent0
                    tail_received0
                    client.CS.cs_model /\
                  PNI.client_application_progress_rank client.CS.cs_model == 0
                with start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent3 tail_received3 and ()
              )
            )
        )
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_ninth_event_validate_certificate_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_certificate_validated_shape client)
=
  lemma_client_no_tail_model8_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
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
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      rest4 /\
    FStar.List.Tot.length rest4 == 8 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_certificate_model model8 /\
    CS.conn_events_raw_replay
      model8
      rest4
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_certificate_validated_shape client
  with _.
  (
    match rest4 with
    | e8 :: rest5 ->
      assert (FStar.List.Tot.length rest5 == 7);
      lemma_client_after_certificate_next_event_validate_certificate
        model8
        e8
        rest5
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists peer.
        e8 == CS.ConnLocalEvent (CS.LocalValidateCertificate peer)
      returns client_no_tail_certificate_validated_shape client
      with _.
      (
        introduce exists
          (start0:CS.handshake_start)
          (ch0:M.client_hello)
          (sh0:M.server_hello)
          (client_shared0:C.x25519_shared_secret)
          (e40:CS.conn_event)
          (e50:CS.conn_event)
          (ee0:M.encrypted_extensions)
          (cert0:M.certificate_msg)
          (peer0:X.peer_identity)
          (rest0:list CS.conn_event).
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start0) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch0);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh0);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared0) ::
            e40 ::
            e50 ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee0);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert0);
            }) ::
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer0) ::
            rest0 /\
          PCPS.client_no_tail_two_handshake_install_cover e40 e50
        with start ch sh client_shared e4 e5 ee cert peer rest5 and ()
      )
  )
#pop-options
