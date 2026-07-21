module TLS13.Impl.Driver.PairingNoTailClientVerifyShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module PCPrS = TLS13.Impl.Driver.PairingNoTailClientProtectedShape
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

noextract
let client_after_certificate_validated_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated /\
  Some? model.CS.model_handshake.CS.hs_certificate /\
  Some? model.CS.model_handshake.CS.hs_validated_peer /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

noextract
let client_after_certificate_verify_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
  Some? model.CS.model_handshake.CS.hs_certificate /\
  Some? model.CS.model_handshake.CS.hs_validated_peer /\
  Some? model.CS.model_handshake.CS.hs_certificate_verify /\
  Some? model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

let lemma_client_after_certificate_validated_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_certificate_validated_model model)
      (ensures PNI.client_application_progress_rank model == 7)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsCertificateValidated ->
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
      assert (PNI.client_application_progress_rank model == 7)
    | _, _, _, _ ->
      assert False)
  | _ ->
    assert False

let lemma_client_after_certificate_verify_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_certificate_verify_model model)
      (ensures PNI.client_application_progress_rank model == 6)
=
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived ->
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
      assert (PNI.client_application_progress_rank model == 6)
    | _, _, _, _ ->
      assert False)
  | _ ->
    assert False

let lemma_client_after_certificate_verify_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_certificate_verify_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        Some? model.CS.model_handshake.CS.hs_validated_peer /\
        Some? model.CS.model_handshake.CS.hs_certificate_verify /\
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
let lemma_client_validate_certificate_step_model_shape
  (model8 model9:CS.connection_model)
  (peer:X.peer_identity)
  : Lemma
      (requires
        PCPrS.client_after_certificate_model model8 /\
        CS.step_model
          model8
          (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)) == Some model9)
      (ensures client_after_certificate_validated_model model9)
=
  CSL.lemma_step_model_preserves_config
    model8
    (CS.ConnLocalEvent (CS.LocalValidateCertificate peer))
    model9;
  assert_norm (
    CS.step_model
      model8
      (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)) ==
    Some (CS.with_handshake_stage
      model8
      { model8.CS.model_handshake with CS.hs_validated_peer = Some peer }
      CS.HsCertificateValidated));
  assert (model9.CS.model_config == model8.CS.model_config)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_certificate_verify_step_model_shape
  (model9 model10:CS.connection_model)
  (cv:GCV.certificateVerify)
  : Lemma
      (requires
        client_after_certificate_validated_model model9 /\
        CS.step_model
          model9
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          }) == Some model10)
      (ensures
        client_after_certificate_verify_model model10 /\
        model10.CS.model_handshake.CS.hs_certificate_verify == Some cv)
=
  CSL.lemma_step_model_preserves_config
    model9
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    })
    model10;
  assert_norm (
    CS.step_model
      model9
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ==
    Some (CS.with_handshake_stage
      { model9 with
          CS.model_record =
            { model9.CS.model_record with
                CS.record_read =
                  TLS13.Record.Spec.next_seq
                    model9.CS.model_record.CS.record_read;
            };
      }
      (CS.append_handshake_to_transcript
        { model9.CS.model_handshake with
            CS.hs_certificate_verify = Some cv;
            CS.hs_buffers =
              { model9.CS.model_handshake.CS.hs_buffers with
                  CS.hb_certificate_verify_input =
                    Some (TLS13.Handshake.Spec.certificate_verify_input
                      (TLS13.Transcript.hash
                        model9.CS.model_handshake.CS.hs_transcript));
              };
        }
        (M.CertificateVerify cv))
      CS.HsCertificateVerifyReceived));
  assert (model10.CS.model_config == model9.CS.model_config);
  assert (model10.CS.model_handshake.CS.hs_certificate_verify == Some cv)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model9_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
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
            rest5 /\
          FStar.List.Tot.length rest5 == 7 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_certificate_validated_model model9 /\
          CS.conn_events_raw_replay
            model9
            rest5
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  PCPrS.lemma_client_no_tail_model8_witness client;
  PCPrS.lemma_client_no_tail_ninth_event_validate_certificate_clean client;
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
    PCPrS.client_after_certificate_model model8 /\
    CS.conn_events_raw_replay
      model8
      rest4
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
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
        rest5 /\
      FStar.List.Tot.length rest5 == 7 /\
      PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
      client_after_certificate_validated_model model9 /\
      CS.conn_events_raw_replay
        model9
        rest5
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    eliminate exists start' ch' sh' client_shared' e4' e5' ee' cert' peer rest'.
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
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate cert');
        }) ::
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
        rest' /\
      PCPS.client_no_tail_two_handshake_install_cover e4' e5'
    returns
      exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
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
          rest5 /\
        FStar.List.Tot.length rest5 == 7 /\
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        client_after_certificate_validated_model model9 /\
        CS.conn_events_raw_replay
          model9
          rest5
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
      assert (e5' == e5);
      assert (ee' == ee);
      assert (cert' == cert);
      match rest4 with
      | e8 :: rest5 ->
        assert (e8 == CS.ConnLocalEvent (CS.LocalValidateCertificate peer));
        assert (rest' == rest5);
        assert (FStar.List.Tot.length rest5 == 7);
        assert_norm (
          CS.conn_events_raw_replay model8 (e8 :: rest5) tail_sent tail_received client.CS.cs_model ==
          (exists model9 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model8 e8 /\
            CS.step_model model8 e8 == Some model9 /\
            CS.event_raw_delta_legal model8 e8 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model9 rest5 tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model9 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model8 e8 /\
          CS.step_model model8 e8 == Some model9 /\
          CS.event_raw_delta_legal model8 e8 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model9 rest5 tail_sent2 tail_received2 client.CS.cs_model
        returns
          exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
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
              rest5 /\
            FStar.List.Tot.length rest5 == 7 /\
            PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
            client_after_certificate_validated_model model9 /\
            CS.conn_events_raw_replay
              model9
              rest5
              tail_sent
              tail_received
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
        with _.
        (
          lemma_client_validate_certificate_step_model_shape model8 model9 peer;
          introduce exists
            (start0:CS.handshake_start)
            (ch0:GCH.clientHello)
            (sh0:GSH.serverHello)
            (client_shared0:C.x25519_shared_secret)
            (e40:CS.conn_event)
            (e50:CS.conn_event)
            (ee0:GEE.encryptedExtensions)
            (cert0:GCert.certificate)
            (peer0:X.peer_identity)
            (rest50:list CS.conn_event)
            (model90:CS.connection_model)
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
              rest50 /\
            FStar.List.Tot.length rest50 == 7 /\
            PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
            client_after_certificate_validated_model model90 /\
            CS.conn_events_raw_replay
              model90
              rest50
              tail_sent0
              tail_received0
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
          with start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent2 tail_received2 and ()
        )
    )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_certificate_validated_next_event_certificate_verify
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_certificate_validated_model model /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 6)
      (ensures
        exists cv.
          ev == CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          })
=
  lemma_client_after_certificate_validated_progress_rank model;
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
    exists cv.
      ev == CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
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
         assert (CS.traffic_install_allowed_at_stage CS.HsCertificateValidated install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication -> assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
          CS.ClientEndpoint
          CS.HsCertificateValidated
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
         assert (PNI.client_application_progress_rank model1 == 7);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (7 <= 6);
         assert False
       | M.TlsHandshake hs ->
         (match msg.CL.message_direction, hs with
          | CL.Received, M.CertificateVerify cv ->
            introduce exists (cv':GCV.certificateVerify).
              ev == CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              }
            with cv and ()
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
let lemma_client_no_tail_tenth_event_certificate_verify_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_certificate_verify_received_shape client)
=
  lemma_client_no_tail_model9_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
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
      rest5 /\
    FStar.List.Tot.length rest5 == 7 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_certificate_validated_model model9 /\
    CS.conn_events_raw_replay
      model9
      rest5
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_certificate_verify_received_shape client
  with _.
  (
    match rest5 with
    | e9 :: rest6 ->
      assert (FStar.List.Tot.length rest6 == 6);
      lemma_client_after_certificate_validated_next_event_certificate_verify
        model9
        e9
        rest6
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists cv.
        e9 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        }
      returns client_no_tail_certificate_verify_received_shape client
      with _.
      (
        introduce exists
          (start0:CS.handshake_start)
          (ch0:GCH.clientHello)
          (sh0:GSH.serverHello)
          (client_shared0:C.x25519_shared_secret)
          (e40:CS.conn_event)
          (e50:CS.conn_event)
          (ee0:GEE.encryptedExtensions)
          (cert0:GCert.certificate)
          (peer0:X.peer_identity)
          (cv0:GCV.certificateVerify)
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
            rest0 /\
          PCPS.client_no_tail_two_handshake_install_cover e40 e50
        with start ch sh client_shared e4 e5 ee cert peer cv rest6 and ()
      )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_model10_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent tail_received.
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
          client_after_certificate_verify_model model10 /\
          CS.conn_events_raw_replay
            model10
            rest6
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  lemma_client_no_tail_model9_witness client;
  lemma_client_no_tail_tenth_event_certificate_verify_clean client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer rest5 model9 tail_sent tail_received.
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
      rest5 /\
    FStar.List.Tot.length rest5 == 7 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_after_certificate_validated_model model9 /\
    CS.conn_events_raw_replay
      model9
      rest5
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns
    exists start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent tail_received.
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
      client_after_certificate_verify_model model10 /\
      CS.conn_events_raw_replay
        model10
        rest6
        tail_sent
        tail_received
        client.CS.cs_model /\
      PNI.client_application_progress_rank client.CS.cs_model == 0
  with _.
  (
    eliminate exists start' ch' sh' client_shared' e4' e5' ee' cert' peer' cv rest'.
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
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate cert');
        }) ::
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer') ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        }) ::
        rest' /\
      PCPS.client_no_tail_two_handshake_install_cover e4' e5'
    returns
      exists start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent tail_received.
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
        client_after_certificate_verify_model model10 /\
        CS.conn_events_raw_replay
          model10
          rest6
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
      assert (e5' == e5);
      assert (ee' == ee);
      assert (cert' == cert);
      assert (peer' == peer);
      match rest5 with
      | e9 :: rest6 ->
        assert (e9 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        });
        assert (rest' == rest6);
        assert (FStar.List.Tot.length rest6 == 6);
        assert_norm (
          CS.conn_events_raw_replay model9 (e9 :: rest6) tail_sent tail_received client.CS.cs_model ==
          (exists model10 delta_sent delta_received tail_sent2 tail_received2.
            CS.legal_event model9 e9 /\
            CS.step_model model9 e9 == Some model10 /\
            CS.event_raw_delta_legal model9 e9 delta_sent delta_received /\
            Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
            Seq.equal tail_received (B.append delta_received tail_received2) /\
            CS.conn_events_raw_replay model10 rest6 tail_sent2 tail_received2 client.CS.cs_model));
        eliminate exists model10 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model9 e9 /\
          CS.step_model model9 e9 == Some model10 /\
          CS.event_raw_delta_legal model9 e9 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          CS.conn_events_raw_replay model10 rest6 tail_sent2 tail_received2 client.CS.cs_model
        returns
          exists start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent tail_received.
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
            client_after_certificate_verify_model model10 /\
            CS.conn_events_raw_replay
              model10
              rest6
              tail_sent
              tail_received
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
        with _.
        (
          lemma_client_certificate_verify_step_model_shape model9 model10 cv;
          assert (model10.CS.model_handshake.CS.hs_certificate_verify == Some cv);
          assert (client_after_certificate_verify_model model10);
          assert (CS.conn_events_raw_replay model10 rest6 tail_sent2 tail_received2 client.CS.cs_model);
          assert (PNI.client_application_progress_rank client.CS.cs_model == 0);
          introduce exists
            (start0:CS.handshake_start)
            (ch0:GCH.clientHello)
            (sh0:GSH.serverHello)
            (client_shared0:C.x25519_shared_secret)
            (e40:CS.conn_event)
            (e50:CS.conn_event)
            (ee0:GEE.encryptedExtensions)
            (cert0:GCert.certificate)
            (peer0:X.peer_identity)
            (cv0:GCV.certificateVerify)
            (rest60:list CS.conn_event)
            (model100:CS.connection_model)
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
              rest60 /\
            FStar.List.Tot.length rest60 == 6 /\
            PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
            model100.CS.model_handshake.CS.hs_certificate_verify == Some cv0 /\
            client_after_certificate_verify_model model100 /\
            CS.conn_events_raw_replay
              model100
              rest60
              tail_sent0
              tail_received0
              client.CS.cs_model /\
            PNI.client_application_progress_rank client.CS.cs_model == 0
          with start ch sh client_shared e4 e5 ee cert peer cv rest6 model10 tail_sent2 tail_received2 and ()
        )
    )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_after_certificate_verify_next_event_verify_signature
  (model:CS.connection_model)
  (stored_cv:GCV.certificateVerify)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_certificate_verify_model model /\
        model.CS.model_handshake.CS.hs_certificate_verify == Some stored_cv /\
        CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 5)
      (ensures ev == CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature stored_cv))
=
  lemma_client_after_certificate_verify_progress_rank model;
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
  returns ev == CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature stored_cv)
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
       | CS.LocalVerifyCertificateSignature cv ->
         assert (CS.legal_local_event model local);
         assert (CS.legal_local_event model (CS.LocalVerifyCertificateSignature cv));
         assert (cv == stored_cv)
       | CS.LocalInstallTrafficKeys install ->
         assert (CS.legal_local_event model local);
         assert (CS.traffic_install_allowed_at_stage CS.HsCertificateVerifyReceived install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication -> assert False)
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
          CS.ClientEndpoint
          CS.HsCertificateVerifyReceived
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
         assert (PNI.client_application_progress_rank model1 == 6);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (6 <= 5);
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
let lemma_client_no_tail_eleventh_event_verify_certificate_signature_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_certificate_signature_verified_shape client)
=
  lemma_client_no_tail_model10_witness client;
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
    client_after_certificate_verify_model model10 /\
    CS.conn_events_raw_replay
      model10
      rest6
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  returns client_no_tail_certificate_signature_verified_shape client
  with _.
  (
    match rest6 with
    | e10 :: rest7 ->
      assert (FStar.List.Tot.length rest7 == 5);
      lemma_client_after_certificate_verify_next_event_verify_signature
        model10
        cv
        e10
        rest7
        tail_sent
        tail_received
        client.CS.cs_model;
      assert (e10 == CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv));
        introduce exists
          (start0:CS.handshake_start)
          (ch0:GCH.clientHello)
          (sh0:GSH.serverHello)
          (client_shared0:C.x25519_shared_secret)
          (e40:CS.conn_event)
          (e50:CS.conn_event)
          (ee0:GEE.encryptedExtensions)
          (cert0:GCert.certificate)
          (peer0:X.peer_identity)
          (cv0:GCV.certificateVerify)
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
            rest0 /\
          PCPS.client_no_tail_two_handshake_install_cover e40 e50
        with start ch sh client_shared e4 e5 ee cert peer cv rest7 and ()
  )
#pop-options
