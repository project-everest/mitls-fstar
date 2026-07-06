module TLS13.Impl.Driver.PairingNoTailClientFinishedShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PNTCVS = TLS13.Impl.Driver.PairingNoTailClientVerifyShape
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

noextract
let client_after_signature_verified_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
  Some? model.CS.model_handshake.CS.hs_certificate /\
  Some? model.CS.model_handshake.CS.hs_validated_peer /\
  Some? model.CS.model_handshake.CS.hs_certificate_verify /\
  model.CS.model_handshake.CS.hs_certificate_verify_verified == true /\
  Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

noextract
let client_after_server_finished_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived /\
  Some? model.CS.model_handshake.CS.hs_certificate /\
  Some? model.CS.model_handshake.CS.hs_validated_peer /\
  Some? model.CS.model_handshake.CS.hs_certificate_verify /\
  model.CS.model_handshake.CS.hs_certificate_verify_verified == true /\
  Some? model.CS.model_handshake.CS.hs_server_finished /\
  Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

noextract
let client_after_server_finished_verified_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
  Some? model.CS.model_handshake.CS.hs_certificate /\
  Some? model.CS.model_handshake.CS.hs_validated_peer /\
  Some? model.CS.model_handshake.CS.hs_certificate_verify /\
  model.CS.model_handshake.CS.hs_certificate_verify_verified == true /\
  Some? model.CS.model_handshake.CS.hs_server_finished /\
  model.CS.model_handshake.CS.hs_server_finished_verified == true /\
  Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

let lemma_client_after_signature_verified_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_signature_verified_model model)
      (ensures PNI.client_application_progress_rank model == 5)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified ->
    ()
  | _ ->
    assert False

let lemma_client_after_server_finished_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_server_finished_model model)
      (ensures PNI.client_application_progress_rank model == 4)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerFinishedReceived ->
    ()
  | _ ->
    assert False

let lemma_client_after_server_finished_verified_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_server_finished_verified_model model)
      (ensures PNI.client_application_progress_rank model == 3)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    ()
  | _ ->
    assert False

let lemma_client_after_server_finished_verified_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_server_finished_verified_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        Some? model.CS.model_handshake.CS.hs_validated_peer /\
        Some? model.CS.model_handshake.CS.hs_certificate_verify /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == true /\
        Some? model.CS.model_handshake.CS.hs_server_finished /\
        model.CS.model_handshake.CS.hs_server_finished_verified == true /\
        Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
=
  ()

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_signature_verify_step_model_shape
  (model10 model11:CS.connection_model)
  (cv:M.certificate_verify)
  : Lemma
      (requires
        PNTCVS.client_after_certificate_verify_model model10 /\
        model10.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        CS.step_model
          model10
          (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)) ==
        Some model11)
      (ensures client_after_signature_verified_model model11)
=
  PNTCVS.lemma_client_after_certificate_verify_model_facts model10;
  assert_norm (
    CS.step_model
      model10
      (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)) ==
    Some (CS.with_handshake_stage
      model10
      { model10.CS.model_handshake with
          CS.hs_certificate_verify = Some cv;
          CS.hs_certificate_verify_verified = true;
      }
      CS.HsCertificateVerifyVerified));
  assert (model11.CS.model_config == model10.CS.model_config)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_server_finished_received_step_model_shape
  (model11 model12:CS.connection_model)
  (sf:M.finished)
  : Lemma
      (requires
        client_after_signature_verified_model model11 /\
        CS.step_model
          model11
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          }) == Some model12)
      (ensures
        client_after_server_finished_model model12 /\
        model12.CS.model_handshake.CS.hs_server_finished == Some sf)
=
  assert_norm (
    CS.step_model
      model11
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ==
    Some (CS.with_handshake_stage
      { model11 with
          CS.model_record =
            { model11.CS.model_record with
                CS.record_read =
                  R.next_seq model11.CS.model_record.CS.record_read;
            };
      }
      { model11.CS.model_handshake with
          CS.hs_server_finished = Some sf;
      }
      CS.HsServerFinishedReceived));
  assert (model12.CS.model_config == model11.CS.model_config);
  assert (model12.CS.model_handshake.CS.hs_server_finished == Some sf)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_verify_finished_step_model_shape
  (model12 model13:CS.connection_model)
  (sf:M.finished)
  : Lemma
      (requires
        client_after_server_finished_model model12 /\
        model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
        CS.step_model
          model12
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) == Some model13)
      (ensures client_after_server_finished_verified_model model13)
=
  assert_norm (
    CS.step_model
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) ==
    Some (CS.with_handshake_stage
      model12
      (CS.append_handshake_to_transcript
        { model12.CS.model_handshake with
            CS.hs_server_finished = Some sf;
            CS.hs_server_finished_verified = true;
        }
        (M.Finished sf))
      CS.HsServerFinishedVerified));
  assert (model13.CS.model_config == model12.CS.model_config)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_signature_verified_next_event_server_finished
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_signature_verified_model model /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 4)
      (ensures
        exists sf.
          ev == CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          })
=
  lemma_client_after_signature_verified_progress_rank model;
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
    exists sf.
      ev == CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
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
         assert (CS.traffic_install_allowed_at_stage CS.HsCertificateVerifyVerified install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication -> assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
          CS.ClientEndpoint
          CS.HsCertificateVerifyVerified
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
         assert (PNI.client_application_progress_rank model1 == 5);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (5 <= 4);
         assert False
       | M.TlsHandshake (M.Finished sf) ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         (match msg.CL.message_direction with
          | CL.Received ->
            introduce exists (sf':M.finished).
              ev == CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf');
              }
            with sf and ()
          | CL.Sent ->
            assert False)
       | M.TlsHandshake _
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_server_finished_next_event_verify_finished
  (model:CS.connection_model)
  (stored_sf:M.finished)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_server_finished_model model /\
        model.CS.model_handshake.CS.hs_server_finished == Some stored_sf /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 3)
      (ensures ev == CS.ConnLocalEvent (CS.LocalVerifyFinished stored_sf))
=
  lemma_client_after_server_finished_progress_rank model;
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
  returns ev == CS.ConnLocalEvent (CS.LocalVerifyFinished stored_sf)
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
       | CS.LocalVerifyFinished sf ->
         assert (CS.legal_local_event model local);
         assert (CS.legal_local_event model (CS.LocalVerifyFinished sf));
         assert (sf == stored_sf)
       | CS.LocalInstallTrafficKeys install ->
         assert (CS.legal_local_event model local);
         assert (CS.traffic_install_allowed_at_stage CS.HsServerFinishedReceived install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication -> assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
          CS.ClientEndpoint
          CS.HsServerFinishedReceived
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
         assert (PNI.client_application_progress_rank model1 == 4);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (4 <= 3);
         assert False
       | M.TlsHandshake _
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model11_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent tail_received.
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
            rest7 /\
          FStar.List.Tot.length rest7 == 5 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_signature_verified_model model11 /\
          CS.conn_events_raw_replay
            model11
            rest7
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  PNTCVS.lemma_client_no_tail_model10_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent tail_received.
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
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      rest6 /\
    FStar.List.Tot.length rest6 == 6 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    model10.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
    PNTCVS.client_after_certificate_verify_model model10 /\
    CS.conn_events_raw_replay
      model10
      rest6
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent tail_received.
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
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        }) ::
        CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
        rest7 /\
      FStar.List.Tot.length rest7 == 5 /\
      PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
      client_after_signature_verified_model model11 /\
      CS.conn_events_raw_replay
        model11
        rest7
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    match rest6 with
    | e10 :: rest7 ->
      assert (FStar.List.Tot.length rest7 == 5);
      PNTCVS.lemma_client_after_certificate_verify_model_facts model10;
      PNTCVS.lemma_client_no_tail_eleventh_event_verify_certificate_signature_clean client;
      assert (e10 == CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv));
      assert_norm (
        CS.conn_events_raw_replay model10 (e10 :: rest7) tail_sent tail_received client.CS.cs_model ==
        (exists model11 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model10 e10 /\
          CS.step_model model10 e10 == Some model11 /\
          CS.event_raw_delta_legal model10 e10 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model11 rest7 tail_sent2 tail_received2 client.CS.cs_model));
      eliminate exists model11 delta_sent delta_received tail_sent2 tail_received2.
        CS.legal_event model10 e10 /\
        CS.step_model model10 e10 == Some model11 /\
        CS.event_raw_delta_legal model10 e10 delta_sent delta_received /\
        Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
        Seq.equal tail_received (B.append delta_received tail_received2) /\
        CS.conn_events_raw_replay model11 rest7 tail_sent2 tail_received2 client.CS.cs_model
      returns
        exists start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent tail_received.
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
            rest7 /\
          FStar.List.Tot.length rest7 == 5 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_signature_verified_model model11 /\
          CS.conn_events_raw_replay
            model11
            rest7
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0
      with _.
      (
        lemma_client_signature_verify_step_model_shape model10 model11 cv;
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
          (cv0:M.certificate_verify)
          (rest70:list CS.conn_event)
          (model110:CS.connection_model)
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer0) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv0);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv0) ::
            rest70 /\
          FStar.List.Tot.length rest70 == 5 /\
          PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
          client_after_signature_verified_model model110 /\
          CS.conn_events_raw_replay
            model110
            rest70
            tail_sent0
            tail_received0
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0
        with start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent2 tail_received2 and ()
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_twelfth_event_server_finished_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_server_finished_received_shape client)
=
  lemma_client_no_tail_model11_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent tail_received.
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
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      rest7 /\
    FStar.List.Tot.length rest7 == 5 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_signature_verified_model model11 /\
    CS.conn_events_raw_replay
      model11
      rest7
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_server_finished_received_shape client
  with _.
  (
    match rest7 with
    | e11 :: rest8 ->
      assert (FStar.List.Tot.length rest8 == 4);
      lemma_client_after_signature_verified_next_event_server_finished
        model11
        e11
        rest8
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists sf.
        e11 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        }
      returns client_no_tail_server_finished_received_shape client
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
          (cv0:M.certificate_verify)
          (sf0:M.finished)
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
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv0);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv0) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf0);
            }) ::
            rest0 /\
          PCPS.client_no_tail_two_handshake_install_cover e40 e50
        with start ch sh client_shared e4 e5 ee cert peer cv sf rest8 and ()
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model12_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            }) ::
            rest8 /\
          FStar.List.Tot.length rest8 == 4 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
          client_after_server_finished_model model12 /\
          CS.conn_events_raw_replay
            model12
            rest8
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  lemma_client_no_tail_model11_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv rest7 model11 tail_sent tail_received.
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
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      rest7 /\
    FStar.List.Tot.length rest7 == 5 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_signature_verified_model model11 /\
    CS.conn_events_raw_replay
      model11
      rest7
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        }) ::
        CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        }) ::
        rest8 /\
      FStar.List.Tot.length rest8 == 4 /\
      PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
      model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
      client_after_server_finished_model model12 /\
      CS.conn_events_raw_replay
        model12
        rest8
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    match rest7 with
    | e11 :: rest8 ->
      assert (FStar.List.Tot.length rest8 == 4);
      lemma_client_after_signature_verified_next_event_server_finished
        model11
        e11
        rest8
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists sf.
        e11 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        }
      returns
        exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            }) ::
            rest8 /\
          FStar.List.Tot.length rest8 == 4 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
          client_after_server_finished_model model12 /\
          CS.conn_events_raw_replay
            model12
            rest8
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0
      with _.
      (
        assert_norm (
          CS.conn_events_raw_replay model11 (e11 :: rest8) tail_sent tail_received client.CS.cs_model ==
          (exists model12 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model11 e11 /\
            CS.step_model model11 e11 == Some model12 /\
            CS.event_raw_delta_legal model11 e11 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model12 rest8 tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model12 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model11 e11 /\
          CS.step_model model11 e11 == Some model12 /\
          CS.event_raw_delta_legal model11 e11 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model12 rest8 tail_sent2 tail_received2 client.CS.cs_model
        returns
          exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              }) ::
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf);
              }) ::
              rest8 /\
            FStar.List.Tot.length rest8 == 4 /\
            PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
            model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
            client_after_server_finished_model model12 /\
            CS.conn_events_raw_replay
              model12
              rest8
              tail_sent
              tail_received
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
        with _.
        (
          lemma_client_server_finished_received_step_model_shape model11 model12 sf;
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
            (cv0:M.certificate_verify)
            (sf0:M.finished)
            (rest80:list CS.conn_event)
            (model120:CS.connection_model)
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
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer0) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv0);
              }) ::
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv0) ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf0);
              }) ::
              rest80 /\
            FStar.List.Tot.length rest80 == 4 /\
            PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
            model120.CS.model_handshake.CS.hs_server_finished == Some sf0 /\
            client_after_server_finished_model model120 /\
            CS.conn_events_raw_replay
              model120
              rest80
              tail_sent0
              tail_received0
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
          with start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent2 tail_received2 and ()
        )
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model13_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv sf rest9 model13 tail_sent tail_received.
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
            rest9 /\
          FStar.List.Tot.length rest9 == 3 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_server_finished_verified_model model13 /\
          CS.conn_events_raw_replay
            model13
            rest9
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  lemma_client_no_tail_model12_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      rest8 /\
    FStar.List.Tot.length rest8 == 4 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
    client_after_server_finished_model model12 /\
    CS.conn_events_raw_replay
      model12
      rest8
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 ee cert peer cv sf rest9 model13 tail_sent tail_received.
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
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        }) ::
        CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        }) ::
        CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
        rest9 /\
      FStar.List.Tot.length rest9 == 3 /\
      PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
      client_after_server_finished_verified_model model13 /\
      CS.conn_events_raw_replay
        model13
        rest9
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    match rest8 with
    | e12 :: rest9 ->
      assert (FStar.List.Tot.length rest9 == 3);
      lemma_client_after_server_finished_next_event_verify_finished
        model12
        sf
        e12
        rest9
        tail_sent
        tail_received
        client.CS.cs_model;
      assert (e12 == CS.ConnLocalEvent (CS.LocalVerifyFinished sf));
      assert_norm (
        CS.conn_events_raw_replay model12 (e12 :: rest9) tail_sent tail_received client.CS.cs_model ==
        (exists model13 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model12 e12 /\
          CS.step_model model12 e12 == Some model13 /\
          CS.event_raw_delta_legal model12 e12 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model13 rest9 tail_sent2 tail_received2 client.CS.cs_model));
      eliminate exists model13 delta_sent delta_received tail_sent2 tail_received2.
        CS.legal_event model12 e12 /\
        CS.step_model model12 e12 == Some model13 /\
        CS.event_raw_delta_legal model12 e12 delta_sent delta_received /\
        Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
        Seq.equal tail_received (B.append delta_received tail_received2) /\
        CS.conn_events_raw_replay model13 rest9 tail_sent2 tail_received2 client.CS.cs_model
      returns
        exists start ch sh client_shared e4 e5 ee cert peer cv sf rest9 model13 tail_sent tail_received.
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
            rest9 /\
          FStar.List.Tot.length rest9 == 3 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_server_finished_verified_model model13 /\
          CS.conn_events_raw_replay
            model13
            rest9
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0
      with _.
      (
        lemma_client_verify_finished_step_model_shape model12 model13 sf;
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
          (cv0:M.certificate_verify)
          (sf0:M.finished)
          (rest90:list CS.conn_event)
          (model130:CS.connection_model)
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
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer0) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv0);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv0) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf0);
            }) ::
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf0) ::
            rest90 /\
          FStar.List.Tot.length rest90 == 3 /\
          PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
          client_after_server_finished_verified_model model130 /\
          CS.conn_events_raw_replay
            model130
            rest90
            tail_sent0
            tail_received0
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0
        with start ch sh client_shared e4 e5 ee cert peer cv sf rest9 model13 tail_sent2 tail_received2 and ()
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_thirteenth_event_verify_finished_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_server_finished_verified_shape client)
=
  lemma_client_no_tail_model12_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf rest8 model12 tail_sent tail_received.
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
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      rest8 /\
    FStar.List.Tot.length rest8 == 4 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    model12.CS.model_handshake.CS.hs_server_finished == Some sf /\
    client_after_server_finished_model model12 /\
    CS.conn_events_raw_replay
      model12
      rest8
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_server_finished_verified_shape client
  with _.
  (
    match rest8 with
    | e12 :: rest9 ->
      assert (FStar.List.Tot.length rest9 == 3);
      lemma_client_after_server_finished_next_event_verify_finished
        model12
        sf
        e12
        rest9
        tail_sent
        tail_received
        client.CS.cs_model;
      assert (e12 == CS.ConnLocalEvent (CS.LocalVerifyFinished sf));
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
        (cv0:M.certificate_verify)
        (sf0:M.finished)
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
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv0);
          }) ::
          CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv0) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished sf0);
          }) ::
          CS.ConnLocalEvent (CS.LocalVerifyFinished sf0) ::
          rest0 /\
        PCPS.client_no_tail_two_handshake_install_cover e40 e50
      with start ch sh client_shared e4 e5 ee cert peer cv sf rest9 and ()
  )
#pop-options
