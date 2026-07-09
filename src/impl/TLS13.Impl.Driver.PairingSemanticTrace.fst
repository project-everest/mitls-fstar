module TLS13.Impl.Driver.PairingSemanticTrace

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Pairing = TLS13.Impl.Driver.Pairing
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PNTSFShape = TLS13.Impl.Driver.PairingNoTailServerFlightShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

#push-options "--split_queries always --z3rlimit 10 --z3refresh"

noextract
let next_model
  (model:CS.connection_model)
  (ev:CS.conn_event)
  : GTot CS.connection_model =
  match CS.step_model model ev with
  | Some model1 -> model1
  | None -> model

let lemma_step_model_many_cons_next
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.step_model_many model (ev :: rest) == Some final_model)
      (ensures
        CS.step_model model ev == Some (next_model model ev) /\
        CS.step_model_many (next_model model ev) rest == Some final_model)
=
  match CS.step_model model ev with
  | Some _ ->
    ()
  | None ->
    assert_norm (CS.step_model_many model (ev :: rest) == None);
    assert False

let rec lemma_conn_events_raw_replay_legal_after_prefix
  (model:CS.connection_model)
  (prefix_model:CS.connection_model)
  (prefix:list CS.conn_event)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.step_model_many model prefix == Some prefix_model /\
        CS.conn_events_raw_replay
          model
          (prefix @ (ev :: rest))
          raw_sent
          raw_received
          final_model)
      (ensures CS.legal_event prefix_model ev)
      (decreases prefix)
=
  match prefix with
  | [] ->
    assert (prefix_model == model);
    assert_norm ([] @ (ev :: rest) == ev :: rest);
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
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns CS.legal_event prefix_model ev
    with _.
    ( assert (prefix_model == model) )
  | hd :: tl ->
    assert_norm ((hd :: tl) @ (ev :: rest) == hd :: (tl @ (ev :: rest)));
    eliminate exists
      (model1:CS.connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      CS.legal_event model hd /\
      CS.step_model model hd == Some model1 /\
      CS.event_raw_delta_legal model hd delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 (tl @ (ev :: rest)) tail_sent tail_received final_model
    returns CS.legal_event prefix_model ev
    with _.
    ( assert (model1 == next_model model hd);
      assert (CS.step_model_many model (hd :: tl) ==
        CS.step_model_many model1 tl);
      assert (CS.step_model_many model1 tl == Some prefix_model);
      lemma_conn_events_raw_replay_legal_after_prefix
        model1
        prefix_model
        tl
        ev
        rest
        tail_sent
        tail_received
        final_model )

noextract
let client_semantic_install_event
  (ev:CS.conn_event)
  : prop =
  PCPS.client_no_tail_handshake_write_install_event ev \/
  PCPS.client_no_tail_handshake_read_install_event ev \/
  PNTCAS.client_no_tail_application_write_install_event ev \/
  PNTCAS.client_no_tail_application_read_install_event ev

let lemma_client_semantic_install_event_tls_deltas_empty
  (ev:CS.conn_event)
  : Lemma
      (requires client_semantic_install_event ev)
      (ensures
        CS.conn_event_sent_tls_delta ev == [] /\
        CS.conn_event_received_tls_delta ev == [])
=
  if PCPS.client_no_tail_handshake_write_install_event ev then (
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev
  ) else if PCPS.client_no_tail_handshake_read_install_event ev then (
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev
  ) else if PNTCAS.client_no_tail_application_write_install_event ev then (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev
  ) else (
    assert (PNTCAS.client_no_tail_application_read_install_event ev);
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev
  );
  match ev with
  | CS.ConnLocalEvent _ ->
    ()
  | _ ->
    assert False

let lemma_client_semantic_install_event_local
  (ev:CS.conn_event)
  : Lemma
      (requires client_semantic_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent _ -> True
        | _ -> False))
=
  if PCPS.client_no_tail_handshake_write_install_event ev then (
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev
  ) else if PCPS.client_no_tail_handshake_read_install_event ev then (
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev
  ) else if PNTCAS.client_no_tail_application_write_install_event ev then (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev
  ) else (
    assert (PNTCAS.client_no_tail_application_read_install_event ev);
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev
  );
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ -> assert False

let lemma_client_semantic_install_event_preserves_slots
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_semantic_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        model1.CS.model_config == model.CS.model_config /\
        model1.CS.model_control == model.CS.model_control /\
        model1.CS.model_handshake.CS.hs_client_hello ==
          model.CS.model_handshake.CS.hs_client_hello /\
        model1.CS.model_handshake.CS.hs_server_hello ==
          model.CS.model_handshake.CS.hs_server_hello /\
        model1.CS.model_handshake.CS.hs_encrypted_extensions ==
          model.CS.model_handshake.CS.hs_encrypted_extensions /\
        model1.CS.model_handshake.CS.hs_certificate ==
          model.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify ==
          model.CS.model_handshake.CS.hs_certificate_verify /\
        model1.CS.model_handshake.CS.hs_server_finished ==
          model.CS.model_handshake.CS.hs_server_finished /\
        model1.CS.model_handshake.CS.hs_client_finished ==
          model.CS.model_handshake.CS.hs_client_finished)
=
  if PCPS.client_no_tail_handshake_write_install_event ev then (
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev
  ) else if PCPS.client_no_tail_handshake_read_install_event ev then (
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev
  ) else if PNTCAS.client_no_tail_application_write_install_event ev then (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev
  ) else (
    assert (PNTCAS.client_no_tail_application_read_install_event ev);
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev
  );
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match model.CS.model_control with
     | CS.ControlHandshaking _ ->
       assert_norm (CS.step_model model ev == Some model1)
     | _ ->
       assert_norm (CS.step_model model ev == None);
       assert False)
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    (match model.CS.model_control with
     | CS.ControlHandshaking _ ->
       assert_norm (CS.step_model model ev == Some model1)
     | _ ->
       assert_norm (CS.step_model model ev == None);
       assert False)
  | _ ->
    assert False

let lemma_client_local_verify_finished_step_slots
  (model model1:CS.connection_model)
  (sf:M.finished)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived /\
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) == Some model1)
      (ensures
        model1.CS.model_config == model.CS.model_config /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        model1.CS.model_handshake.CS.hs_client_hello ==
          model.CS.model_handshake.CS.hs_client_hello /\
        model1.CS.model_handshake.CS.hs_server_hello ==
          model.CS.model_handshake.CS.hs_server_hello /\
        model1.CS.model_handshake.CS.hs_encrypted_extensions ==
          model.CS.model_handshake.CS.hs_encrypted_extensions /\
        model1.CS.model_handshake.CS.hs_certificate ==
          model.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify ==
          model.CS.model_handshake.CS.hs_certificate_verify /\
        model1.CS.model_handshake.CS.hs_server_finished == Some sf /\
        model1.CS.model_handshake.CS.hs_client_finished ==
          model.CS.model_handshake.CS.hs_client_finished)
=
  assert_norm
    (CS.step_model
      model
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) == Some model1)

let lemma_client_sent_finished_step_slots
  (model model1:CS.connection_model)
  (cf:M.finished)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.step_model
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished cf);
          }) == Some model1)
      (ensures
        model1.CS.model_config == model.CS.model_config /\
        model1.CS.model_control == CS.ControlApplicationData /\
        model1.CS.model_handshake.CS.hs_client_hello ==
          model.CS.model_handshake.CS.hs_client_hello /\
        model1.CS.model_handshake.CS.hs_server_hello ==
          model.CS.model_handshake.CS.hs_server_hello /\
        model1.CS.model_handshake.CS.hs_encrypted_extensions ==
          model.CS.model_handshake.CS.hs_encrypted_extensions /\
        model1.CS.model_handshake.CS.hs_certificate ==
          model.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify ==
          model.CS.model_handshake.CS.hs_certificate_verify /\
        model1.CS.model_handshake.CS.hs_server_finished ==
          model.CS.model_handshake.CS.hs_server_finished /\
        model1.CS.model_handshake.CS.hs_client_finished == Some cf)
=
  assert_norm
    (CS.step_model
      model
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) == Some model1)

let lemma_client_finished_shape_model_slots_from_event_log
  (client:CS.connection_state)
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (peer:X.peer_identity)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  (cf:M.finished)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        client.CS.cs_event_log ==
          [
            CS.ConnLocalEvent (CS.LocalStartHandshake start);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            };
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
            e4;
            e5;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
            e13;
            e14;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf);
            }
          ] /\
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
        client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert /\
        client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf)
=
  assert (CS.connection_state_event_log_consistent client);
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  assert (client_semantic_install_event e4);
  assert (client_semantic_install_event e5);
  assert (client_semantic_install_event e13);
  assert (client_semantic_install_event e14);
  let final_model = client.CS.cs_model in
  let cfg = final_model.CS.model_config in
  let m0 = CS.initial_model cfg in
  let ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let ev1 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let ev2 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  let ev4 = e4 in
  let ev5 = e5 in
  let ev6 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let ev7 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let ev8 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let ev9 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let ev10 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let ev11 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished sf);
    } in
  let ev12 = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let ev13 = e13 in
  let ev14 = e14 in
  let ev15 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished cf);
    } in
  let tail15 = [] in
  let tail14 = ev15 :: tail15 in
  let tail13 = ev14 :: tail14 in
  let tail12 = ev13 :: tail13 in
  let tail11 = ev12 :: tail12 in
  let tail10 = ev11 :: tail11 in
  let tail9 = ev10 :: tail10 in
  let tail8 = ev9 :: tail9 in
  let tail7 = ev8 :: tail8 in
  let tail6 = ev7 :: tail7 in
  let tail5 = ev6 :: tail6 in
  let tail4 = ev5 :: tail5 in
  let tail3 = ev4 :: tail4 in
  let tail2 = ev3 :: tail3 in
  let tail1 = ev2 :: tail2 in
  let tail0 = ev1 :: tail1 in
  assert (client.CS.cs_event_log == ev0 :: tail0);
  assert (CS.step_model_many m0 (ev0 :: tail0) == Some final_model);

  let m1 = next_model m0 ev0 in
  lemma_step_model_many_cons_next m0 ev0 tail0 final_model;
  assert_norm (CS.step_model m0 ev0 == Some m1);
  assert (m1.CS.model_control == CS.ControlHandshaking CS.HsStarted);

  let m2 = next_model m1 ev1 in
  lemma_step_model_many_cons_next m1 ev1 tail1 final_model;
  assert_norm (CS.step_model m1 ev1 == Some m2);
  assert (m2.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent);
  assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);

  let m3 = next_model m2 ev2 in
  lemma_step_model_many_cons_next m2 ev2 tail2 final_model;
  assert_norm (CS.step_model m2 ev2 == Some m3);
  assert (m3.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
  assert (m3.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m3.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m4 = next_model m3 ev3 in
  lemma_step_model_many_cons_next m3 ev3 tail3 final_model;
  assert_norm (CS.step_model m3 ev3 == Some m4);
  assert (m4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
  assert (m4.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m4.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m5 = next_model m4 ev4 in
  lemma_step_model_many_cons_next m4 ev4 tail4 final_model;
  lemma_client_semantic_install_event_preserves_slots m4 m5 ev4;
  assert (m5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
  assert (m5.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m5.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m6 = next_model m5 ev5 in
  lemma_step_model_many_cons_next m5 ev5 tail5 final_model;
  lemma_client_semantic_install_event_preserves_slots m5 m6 ev5;
  assert (m6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
  assert (m6.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m6.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m7 = next_model m6 ev6 in
  lemma_step_model_many_cons_next m6 ev6 tail6 final_model;
  assert_norm (CS.step_model m6 ev6 == Some m7);
  assert (m7.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived);
  assert (m7.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m7.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m7.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);

  let m8 = next_model m7 ev7 in
  lemma_step_model_many_cons_next m7 ev7 tail7 final_model;
  assert_norm (CS.step_model m7 ev7 == Some m8);
  assert (m8.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived);
  assert (m8.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m8.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m8.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m8.CS.model_handshake.CS.hs_certificate == Some cert);

  let m9 = next_model m8 ev8 in
  lemma_step_model_many_cons_next m8 ev8 tail8 final_model;
  assert_norm (CS.step_model m8 ev8 == Some m9);
  assert (m9.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated);
  assert (m9.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m9.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m9.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m9.CS.model_handshake.CS.hs_certificate == Some cert);

  let m10 = next_model m9 ev9 in
  lemma_step_model_many_cons_next m9 ev9 tail9 final_model;
  assert_norm (CS.step_model m9 ev9 == Some m10);
  assert (m10.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived);
  assert (m10.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m10.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m10.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m10.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m10.CS.model_handshake.CS.hs_certificate_verify == Some cv);

  let m11 = next_model m10 ev10 in
  lemma_step_model_many_cons_next m10 ev10 tail10 final_model;
  assert_norm (CS.step_model m10 ev10 == Some m11);
  let m11_expected =
    CS.with_handshake_stage
      m10
      { m10.CS.model_handshake with
          CS.hs_certificate_verify = Some cv;
          CS.hs_certificate_verify_verified = true;
      }
      CS.HsCertificateVerifyVerified in
  assert_norm (CS.step_model m10 ev10 == Some m11_expected);
  assert (m11 == m11_expected);
  assert (m11.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified);
  assert (m11.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m11.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m11.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m11.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m11.CS.model_handshake.CS.hs_certificate_verify == Some cv);

  let m12 = next_model m11 ev11 in
  lemma_step_model_many_cons_next m11 ev11 tail11 final_model;
  assert_norm (CS.step_model m11 ev11 == Some m12);
  assert (m12.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived);
  assert (m12.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m12.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m12.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m12.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m12.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m12.CS.model_handshake.CS.hs_server_finished == Some sf);

  let m13 = next_model m12 ev12 in
  lemma_step_model_many_cons_next m12 ev12 tail12 final_model;
  assert_norm (CS.step_model m12 ev12 == Some m13);
  lemma_client_local_verify_finished_step_slots m12 m13 sf;
  assert (m13.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
  assert (m13.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m13.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m13.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m13.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m13.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m13.CS.model_handshake.CS.hs_server_finished == Some sf);

  let m14 = next_model m13 ev13 in
  lemma_step_model_many_cons_next m13 ev13 tail13 final_model;
  lemma_client_semantic_install_event_preserves_slots m13 m14 ev13;
  assert (m14.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
  assert (m14.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m14.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m14.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m14.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m14.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m14.CS.model_handshake.CS.hs_server_finished == Some sf);

  let m15 = next_model m14 ev14 in
  lemma_step_model_many_cons_next m14 ev14 tail14 final_model;
  lemma_client_semantic_install_event_preserves_slots m14 m15 ev14;
  assert (m15.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
  assert (m15.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m15.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m15.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m15.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m15.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m15.CS.model_handshake.CS.hs_server_finished == Some sf);

  let m16 = next_model m15 ev15 in
  lemma_step_model_many_cons_next m15 ev15 tail15 final_model;
  assert_norm (CS.step_model m15 ev15 == Some m16);
  lemma_client_sent_finished_step_slots m15 m16 cf;
  assert (m16.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m16.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m16.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m16.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m16.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m16.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (m16.CS.model_handshake.CS.hs_client_finished == Some cf);
  assert_norm (CS.step_model_many m16 [] == Some m16);
  assert (m16 == final_model)

let lemma_client_finished_shape_tls_message_projections
  (client_trace:list CS.conn_event)
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (peer:X.peer_identity)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  (cf:M.finished)
  : Lemma
      (requires
        client_trace ==
          [
            CS.ConnLocalEvent (CS.LocalStartHandshake start);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            };
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
            e4;
            e5;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
            e13;
            e14;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf);
            }
          ] /\
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        CS.sent_tls_messages client_trace ==
          [
            M.TlsHandshake (M.ClientHello ch);
            M.TlsHandshake (M.Finished cf)
          ] /\
        CS.received_tls_messages client_trace ==
          [
            M.TlsHandshake (M.ServerHello sh);
            M.TlsHandshake (M.EncryptedExtensions ee);
            M.TlsHandshake (M.Certificate cert);
            M.TlsHandshake (M.CertificateVerify cv);
            M.TlsHandshake (M.Finished sf)
          ])
=
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  assert (client_semantic_install_event e4);
  assert (client_semantic_install_event e5);
  assert (client_semantic_install_event e13);
  assert (client_semantic_install_event e14);
  lemma_client_semantic_install_event_tls_deltas_empty e4;
  lemma_client_semantic_install_event_tls_deltas_empty e5;
  lemma_client_semantic_install_event_tls_deltas_empty e13;
  lemma_client_semantic_install_event_tls_deltas_empty e14;
  lemma_client_semantic_install_event_local e4;
  lemma_client_semantic_install_event_local e5;
  lemma_client_semantic_install_event_local e13;
  lemma_client_semantic_install_event_local e14;
  match e4 with
  | CS.ConnLocalEvent l4 ->
    (match e5 with
     | CS.ConnLocalEvent l5 ->
       (match e13 with
        | CS.ConnLocalEvent l13 ->
          (match e14 with
           | CS.ConnLocalEvent l14 ->
             assert (client_trace ==
               [
                 CS.ConnLocalEvent (CS.LocalStartHandshake start);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ClientHello ch);
                 };
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ServerHello sh);
                 };
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
                 CS.ConnLocalEvent l4;
                 CS.ConnLocalEvent l5;
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                 };
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.Certificate cert);
                 };
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                 };
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.Finished sf);
                 };
                 CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
                 CS.ConnLocalEvent l13;
                 CS.ConnLocalEvent l14;
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.Finished cf);
                 }
               ]);
             assert_norm (CS.sent_tls_messages
               [
                 CS.ConnLocalEvent (CS.LocalStartHandshake start);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ClientHello ch);
                 };
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ServerHello sh);
                 };
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
                 CS.ConnLocalEvent l4;
                 CS.ConnLocalEvent l5;
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                 };
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.Certificate cert);
                 };
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                 };
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.Finished sf);
                 };
                 CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
                 CS.ConnLocalEvent l13;
                 CS.ConnLocalEvent l14;
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.Finished cf);
                 }
               ] ==
               [
                 M.TlsHandshake (M.ClientHello ch);
                 M.TlsHandshake (M.Finished cf)
               ]);
             assert_norm (CS.received_tls_messages
               [
                 CS.ConnLocalEvent (CS.LocalStartHandshake start);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ClientHello ch);
                 };
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ServerHello sh);
                 };
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
                 CS.ConnLocalEvent l4;
                 CS.ConnLocalEvent l5;
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
                 };
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.Certificate cert);
                 };
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
                 };
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.Finished sf);
                 };
                 CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
                 CS.ConnLocalEvent l13;
                 CS.ConnLocalEvent l14;
                 CS.ConnNetworkEvent {
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.Finished cf);
                 }
               ] ==
               [
                 M.TlsHandshake (M.ServerHello sh);
                 M.TlsHandshake (M.EncryptedExtensions ee);
                 M.TlsHandshake (M.Certificate cert);
                 M.TlsHandshake (M.CertificateVerify cv);
                 M.TlsHandshake (M.Finished sf)
               ]);
             assert (CS.sent_tls_messages client_trace ==
               [
                 M.TlsHandshake (M.ClientHello ch);
                 M.TlsHandshake (M.Finished cf)
               ]);
             assert (CS.received_tls_messages client_trace ==
               [
                 M.TlsHandshake (M.ServerHello sh);
                 M.TlsHandshake (M.EncryptedExtensions ee);
                 M.TlsHandshake (M.Certificate cert);
                 M.TlsHandshake (M.CertificateVerify cv);
                 M.TlsHandshake (M.Finished sf)
               ])
           | _ -> assert False)
        | _ -> assert False)
     | _ -> assert False)
  | _ -> assert False

let lemma_client_successful_no_tail_semantic_trace_state_from_witnesses
  (client:CS.connection_state)
  (client_trace:list CS.conn_event)
  (start:CS.handshake_start)
  (ch:M.client_hello)
  (sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (peer:X.peer_identity)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  (cf:M.finished)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        client_trace == client.CS.cs_event_log /\
        client.CS.cs_event_log ==
          [
            CS.ConnLocalEvent (CS.LocalStartHandshake start);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            };
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
            e4;
            e5;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
            e13;
            e14;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf);
            }
          ] /\
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        client_successful_no_tail_semantic_trace_state client client_trace)
=
  assert (client_trace == client.CS.cs_event_log);
  lemma_client_finished_shape_tls_message_projections
    client_trace
    start
    ch
    sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    e13
    e14
    cf;
  lemma_client_finished_shape_model_slots_from_event_log
    client
    start
    ch
    sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    e13
    e14
    cf;
  assert (client_successful_no_tail_semantic_trace_state_inputs
    client
    client_trace
    start
    ch
    sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    e13
    e14
    cf);
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
    (e130:CS.conn_event)
    (e140:CS.conn_event)
    (cf0:M.finished).
    client_successful_no_tail_semantic_trace_state_inputs
      client
      client_trace
      start0
      ch0
      sh0
      client_shared0
      e40
      e50
      ee0
      cert0
      peer0
      cv0
      sf0
      e130
      e140
      cf0
  with
    start
    ch
    sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    e13
    e14
    cf
  and ()

let lemma_client_successful_no_tail_semantic_trace_state_from_boundary
  (client:CS.connection_state)
  (client_trace:list CS.conn_event)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        client_trace == client.CS.cs_event_log)
      (ensures
        PNTCAS.client_no_tail_finished_sent_shape client /\
        client_successful_no_tail_semantic_trace_state client client_trace)
=
  PNTCAS.lemma_client_no_tail_sixteenth_event_client_finished_clean client;
  assert (PNTCAS.client_no_tail_finished_sent_shape client);
  eliminate exists
    (start:CS.handshake_start)
    (ch:M.client_hello)
    (sh:M.server_hello)
    (client_shared:C.x25519_shared_secret)
    (e4:CS.conn_event)
    (e5:CS.conn_event)
    (ee:M.encrypted_extensions)
    (cert:M.certificate_msg)
    (peer:X.peer_identity)
    (cv:M.certificate_verify)
    (sf:M.finished)
    (e13:CS.conn_event)
    (e14:CS.conn_event)
    (cf:M.finished).
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
      e13 ::
      e14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14
  returns
    PNTCAS.client_no_tail_finished_sent_shape client /\
    client_successful_no_tail_semantic_trace_state client client_trace
  with _.
  (
    assert (client_trace == client.CS.cs_event_log);
    lemma_client_successful_no_tail_semantic_trace_state_from_witnesses
      client
      client_trace
      start
      ch
      sh
      client_shared
      e4
      e5
      ee
      cert
      peer
      cv
      sf
      e13
      e14
      cf;
    assert (client_successful_no_tail_semantic_trace_state client client_trace)
  )

noextract
let server_semantic_handshake_install_event
  (ev:CS.conn_event)
  : prop =
  PNTSS.server_no_tail_handshake_write_install_event ev \/
  PNTSS.server_no_tail_handshake_read_install_event ev

let lemma_server_semantic_handshake_install_event_local
  (ev:CS.conn_event)
  : Lemma
      (requires server_semantic_handshake_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent _ -> True
        | _ -> False))
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ -> assert False

let lemma_server_semantic_handshake_install_event_tls_deltas_empty
  (ev:CS.conn_event)
  : Lemma
      (requires server_semantic_handshake_install_event ev)
      (ensures
        CS.conn_event_sent_tls_delta ev == [] /\
        CS.conn_event_received_tls_delta ev == [])
=
  lemma_server_semantic_handshake_install_event_local ev;
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ -> assert False

let lemma_local_install_for_role_preserves_slots
  (model model1:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires
        CS.step_model
          model
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole role_install)) == Some model1)
      (ensures
        model1.CS.model_config == model.CS.model_config /\
        model1.CS.model_control == model.CS.model_control /\
        model1.CS.model_handshake.CS.hs_client_hello ==
          model.CS.model_handshake.CS.hs_client_hello /\
        model1.CS.model_handshake.CS.hs_server_hello ==
          model.CS.model_handshake.CS.hs_server_hello /\
        model1.CS.model_handshake.CS.hs_encrypted_extensions ==
          model.CS.model_handshake.CS.hs_encrypted_extensions /\
        model1.CS.model_handshake.CS.hs_certificate ==
          model.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify ==
          model.CS.model_handshake.CS.hs_certificate_verify /\
        model1.CS.model_handshake.CS.hs_server_finished ==
          model.CS.model_handshake.CS.hs_server_finished /\
        model1.CS.model_handshake.CS.hs_client_finished ==
          model.CS.model_handshake.CS.hs_client_finished)
=
  match model.CS.model_control with
  | CS.ControlHandshaking _ ->
    assert_norm
      (CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole role_install)) == Some model1)
  | _ ->
    assert_norm
      (CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole role_install)) == None);
    assert False

let lemma_server_semantic_handshake_install_event_preserves_slots
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        server_semantic_handshake_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        model1.CS.model_config == model.CS.model_config /\
        model1.CS.model_control == model.CS.model_control /\
        model1.CS.model_handshake.CS.hs_client_hello ==
          model.CS.model_handshake.CS.hs_client_hello /\
        model1.CS.model_handshake.CS.hs_server_hello ==
          model.CS.model_handshake.CS.hs_server_hello /\
        model1.CS.model_handshake.CS.hs_encrypted_extensions ==
          model.CS.model_handshake.CS.hs_encrypted_extensions /\
        model1.CS.model_handshake.CS.hs_certificate ==
          model.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify ==
          model.CS.model_handshake.CS.hs_certificate_verify /\
        model1.CS.model_handshake.CS.hs_server_finished ==
          model.CS.model_handshake.CS.hs_server_finished /\
        model1.CS.model_handshake.CS.hs_client_finished ==
          model.CS.model_handshake.CS.hs_client_finished)
=
  lemma_server_semantic_handshake_install_event_local ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    lemma_local_install_for_role_preserves_slots model model1 role_install
  | _ ->
    assert False

let lemma_server_select_parameters_matches_received_client_hello_from_raw_replay
  (cfg:CS.connection_config)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          (CS.initial_model cfg)
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           } ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures selection.CS.server_selected_client_hello == ch)
=
  let m0 = CS.initial_model cfg in
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let tail0 = ev1 :: ev2 :: rest in
  PWR.lemma_conn_events_raw_replay_head
    m0
    ev0
    tail0
    raw_sent
    raw_received
    final_model;
  eliminate exists
    (m1:CS.connection_model)
    (delta_sent0:B.bytes)
    (delta_received0:B.bytes)
    (tail_sent0:B.bytes)
    (tail_received0:B.bytes).
    CS.legal_event m0 ev0 /\
    CS.step_model m0 ev0 == Some m1 /\
    CS.event_raw_delta_legal m0 ev0 delta_sent0 delta_received0 /\
    Seq.equal raw_sent (B.append delta_sent0 tail_sent0) /\
    Seq.equal raw_received (B.append delta_received0 tail_received0) /\
    CS.conn_events_raw_replay
      m1
      tail0
      tail_sent0
      tail_received0
      final_model
  returns selection.CS.server_selected_client_hello == ch
  with _.
  (
    assert (m1 == next_model m0 ev0);
    assert_norm ((next_model m0 ev0).CS.model_control ==
      CS.ControlHandshaking CS.HsAwaitingClientHello);
    assert (m1.CS.model_control ==
      CS.ControlHandshaking CS.HsAwaitingClientHello);
    PWR.lemma_conn_events_raw_replay_head
      m1
      ev1
      (ev2 :: rest)
      tail_sent0
      tail_received0
      final_model;
    eliminate exists
      (m2:CS.connection_model)
      (delta_sent1:B.bytes)
      (delta_received1:B.bytes)
      (tail_sent1:B.bytes)
      (tail_received1:B.bytes).
      CS.legal_event m1 ev1 /\
      CS.step_model m1 ev1 == Some m2 /\
      CS.event_raw_delta_legal m1 ev1 delta_sent1 delta_received1 /\
      Seq.equal tail_sent0 (B.append delta_sent1 tail_sent1) /\
      Seq.equal tail_received0 (B.append delta_received1 tail_received1) /\
      CS.conn_events_raw_replay
        m2
        (ev2 :: rest)
        tail_sent1
        tail_received1
        final_model
    returns selection.CS.server_selected_client_hello == ch
    with _.
    (
      assert (m2 == next_model m1 ev1);
      assert_norm ((next_model m1 ev1).CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived);
      assert_norm ((next_model m1 ev1).CS.model_handshake.CS.hs_client_hello ==
        Some ch);
      assert (m2.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived);
      assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);
      PWR.lemma_conn_events_raw_replay_head
        m2
        ev2
        rest
        tail_sent1
        tail_received1
        final_model;
      eliminate exists
        (m3:CS.connection_model)
        (delta_sent2:B.bytes)
        (delta_received2:B.bytes)
        (tail_sent2:B.bytes)
        (tail_received2:B.bytes).
        CS.legal_event m2 ev2 /\
        CS.step_model m2 ev2 == Some m3 /\
        CS.event_raw_delta_legal m2 ev2 delta_sent2 delta_received2 /\
        Seq.equal tail_sent1 (B.append delta_sent2 tail_sent2) /\
        Seq.equal tail_received1 (B.append delta_received2 tail_received2) /\
        CS.conn_events_raw_replay
          m3
          rest
          tail_sent2
          tail_received2
          final_model
      returns selection.CS.server_selected_client_hello == ch
      with _.
      (
        assert_norm (CS.legal_event m2 ev2);
        assert
          (m2.CS.model_handshake.CS.hs_client_hello ==
            Some selection.CS.server_selected_client_hello);
        assert (Some ch == Some selection.CS.server_selected_client_hello);
        assert (selection.CS.server_selected_client_hello == ch)
      )
    )
  )

let lemma_server_finished_shape_tls_message_projections
  (server_trace:list CS.conn_event)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (server_app_write_material:CS.traffic_key_material)
  (cf:M.finished)
  (server_app_read_material:CS.traffic_key_material)
  : Lemma
      (requires
        server_trace ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            [
              e5;
              e6;
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material;
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material;
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
            ] /\
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6)
      (ensures
        CS.sent_tls_messages server_trace ==
          [
            M.TlsHandshake (M.ServerHello sh);
            M.TlsHandshake (M.EncryptedExtensions ee);
            M.TlsHandshake (M.Certificate cert);
            M.TlsHandshake (M.CertificateVerify cv);
            M.TlsHandshake (M.Finished sf)
          ] /\
        CS.received_tls_messages server_trace ==
          [
            M.TlsHandshake (M.ClientHello ch);
            M.TlsHandshake (M.Finished cf)
          ])
=
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5 e6;
  assert (server_semantic_handshake_install_event e5);
  assert (server_semantic_handshake_install_event e6);
  lemma_server_semantic_handshake_install_event_local e5;
  lemma_server_semantic_handshake_install_event_local e6;
  match e5 with
  | CS.ConnLocalEvent l5 ->
    (match e6 with
     | CS.ConnLocalEvent l6 ->
       assert (server_trace ==
         [
           CS.ConnLocalEvent CS.LocalStartServer;
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           };
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared);
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           };
           CS.ConnLocalEvent l5;
           CS.ConnLocalEvent l6;
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
           };
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Certificate cert);
           };
           CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
           };
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished sf);
           };
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficWrite;
                 CS.install_material = server_app_write_material;
               };
             });
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.Finished cf);
           };
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficRead;
                 CS.install_material = server_app_read_material;
               };
             });
           CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
         ]);
       assert_norm (CS.sent_tls_messages
         [
          CS.ConnLocalEvent CS.LocalStartServer;
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          };
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          };
          CS.ConnLocalEvent l5;
          CS.ConnLocalEvent l6;
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          };
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            });
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished cf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_app_read_material;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
         ] ==
         [
           M.TlsHandshake (M.ServerHello sh);
           M.TlsHandshake (M.EncryptedExtensions ee);
           M.TlsHandshake (M.Certificate cert);
           M.TlsHandshake (M.CertificateVerify cv);
           M.TlsHandshake (M.Finished sf)
         ]);
       assert_norm (CS.received_tls_messages
         [
          CS.ConnLocalEvent CS.LocalStartServer;
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          };
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection);
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          };
          CS.ConnLocalEvent l5;
          CS.ConnLocalEvent l6;
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          };
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            });
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished cf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_app_read_material;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
         ] ==
         [
           M.TlsHandshake (M.ClientHello ch);
           M.TlsHandshake (M.Finished cf)
         ]);
       assert (CS.sent_tls_messages server_trace ==
         [
          M.TlsHandshake (M.ServerHello sh);
          M.TlsHandshake (M.EncryptedExtensions ee);
          M.TlsHandshake (M.Certificate cert);
          M.TlsHandshake (M.CertificateVerify cv);
          M.TlsHandshake (M.Finished sf)
         ]);
       assert (CS.received_tls_messages server_trace ==
         [
          M.TlsHandshake (M.ClientHello ch);
          M.TlsHandshake (M.Finished cf)
         ])
     | _ -> assert False)
  | _ -> assert False

let lemma_server_finished_shape_model_slots_from_event_log
  (server:CS.connection_state)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (server_app_write_material:CS.traffic_key_material)
  (cf:M.finished)
  (server_app_read_material:CS.traffic_key_material)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            [
              e5;
              e6;
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material;
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material;
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
            ] /\
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6)
      (ensures
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
        server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert /\
        server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf)
=
  assert (CS.connection_state_event_log_consistent server);
  assert (CS.connection_state_raw_event_replay_consistent server);
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5 e6;
  assert (server_semantic_handshake_install_event e5);
  assert (server_semantic_handshake_install_event e6);
  let final_model = server.CS.cs_model in
  let cfg = final_model.CS.model_config in
  let m0 = CS.initial_model cfg in
  let ev0 = CS.ConnLocalEvent CS.LocalStartServer in
  let ev1 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello ch);
    } in
  let ev2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let ev4 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello sh);
    } in
  let ev5 = e5 in
  let ev6 = e6 in
  let ev7 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
    } in
  let ev8 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Certificate cert);
    } in
  let ev9 = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let ev10 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
    } in
  let ev11 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished sf);
    } in
  let app_write_install =
    {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = server_app_write_material;
      };
    } in
  let ev12 =
    CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole app_write_install) in
  let ev13 =
    CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.Finished cf);
    } in
  let app_read_install =
    {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = server_app_read_material;
      };
    } in
  let ev14 =
    CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole app_read_install) in
  let ev15 = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
  let tail15 = [] in
  let tail14 = ev15 :: tail15 in
  let tail13 = ev14 :: tail14 in
  let tail12 = ev13 :: tail13 in
  let tail11 = ev12 :: tail12 in
  let tail10 = ev11 :: tail11 in
  let tail9 = ev10 :: tail10 in
  let tail8 = ev9 :: tail9 in
  let tail7 = ev8 :: tail8 in
  let tail6 = ev7 :: tail7 in
  let tail5 = ev6 :: tail6 in
  let tail4 = ev5 :: tail5 in
  let tail3 = ev4 :: tail4 in
  let tail2 = ev3 :: tail3 in
  let tail1 = ev2 :: tail2 in
  let tail0 = ev1 :: tail1 in
  assert (server.CS.cs_event_log == ev0 :: tail0);
  assert (CS.step_model_many m0 (ev0 :: tail0) == Some final_model);
  assert
    (CS.conn_events_raw_replay
      m0
      (ev0 :: tail0)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      final_model);
  lemma_server_select_parameters_matches_received_client_hello_from_raw_replay
    cfg
    ch
    selection
    tail2
    server.CS.cs_wire_log.CL.raw_sent
    server.CS.cs_wire_log.CL.raw_received
    final_model;
  assert (selection.CS.server_selected_client_hello == ch);

  let m1 = next_model m0 ev0 in
  lemma_step_model_many_cons_next m0 ev0 tail0 final_model;
  assert_norm (CS.step_model m0 ev0 == Some m1);
  assert (m1.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello);

  let m2 = next_model m1 ev1 in
  lemma_step_model_many_cons_next m1 ev1 tail1 final_model;
  assert_norm (CS.step_model m1 ev1 == Some m2);
  assert (m2.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);

  let m3 = next_model m2 ev2 in
  lemma_step_model_many_cons_next m2 ev2 tail2 final_model;
  assert_norm (CS.step_model m2 ev2 == Some m3);
  assert (m3.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (m3.CS.model_handshake.CS.hs_client_hello == Some ch);

  let m4 = next_model m3 ev3 in
  lemma_step_model_many_cons_next m3 ev3 tail3 final_model;
  assert_norm (CS.step_model m3 ev3 == Some m4);
  assert (m4.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived);
  assert (m4.CS.model_handshake.CS.hs_client_hello == Some ch);

  let m5 = next_model m4 ev4 in
  lemma_step_model_many_cons_next m4 ev4 tail4 final_model;
  assert_norm (CS.step_model m4 ev4 == Some m5);
  assert (m5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
  assert (m5.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m5.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m6 = next_model m5 ev5 in
  lemma_step_model_many_cons_next m5 ev5 tail5 final_model;
  lemma_server_semantic_handshake_install_event_preserves_slots m5 m6 ev5;
  assert (m6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
  assert (m6.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m6.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m7 = next_model m6 ev6 in
  lemma_step_model_many_cons_next m6 ev6 tail6 final_model;
  lemma_server_semantic_handshake_install_event_preserves_slots m6 m7 ev6;
  assert (m7.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
  assert (m7.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m7.CS.model_handshake.CS.hs_server_hello == Some sh);

  let m8 = next_model m7 ev7 in
  lemma_step_model_many_cons_next m7 ev7 tail7 final_model;
  assert_norm (CS.step_model m7 ev7 == Some m8);
  assert (m8.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (m8.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m8.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m8.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);

  let m9 = next_model m8 ev8 in
  lemma_step_model_many_cons_next m8 ev8 tail8 final_model;
  assert_norm (CS.step_model m8 ev8 == Some m9);
  assert (m9.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (m9.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m9.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m9.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m9.CS.model_handshake.CS.hs_certificate == Some cert);

  let m10 = next_model m9 ev9 in
  lemma_step_model_many_cons_next m9 ev9 tail9 final_model;
  assert_norm (CS.step_model m9 ev9 == Some m10);
  assert (m10.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (m10.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m10.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m10.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m10.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m10.CS.model_handshake.CS.hs_certificate_verify == Some cv);

  let m11 = next_model m10 ev10 in
  lemma_step_model_many_cons_next m10 ev10 tail10 final_model;
  assert_norm (CS.step_model m10 ev10 == Some m11);
  assert (m11.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (m11.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m11.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m11.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m11.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m11.CS.model_handshake.CS.hs_certificate_verify == Some cv);

  let m12 = next_model m11 ev11 in
  lemma_step_model_many_cons_next m11 ev11 tail11 final_model;
  assert_norm (CS.step_model m11 ev11 == Some m12);
  assert (m12.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
  assert (m12.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m12.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m12.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m12.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m12.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m12.CS.model_handshake.CS.hs_server_finished == Some sf);

  let m13 = next_model m12 ev12 in
  lemma_step_model_many_cons_next m12 ev12 tail12 final_model;
  lemma_local_install_for_role_preserves_slots m12 m13 app_write_install;
  assert (m13.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
  assert (m13.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m13.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m13.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m13.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m13.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m13.CS.model_handshake.CS.hs_server_finished == Some sf);

  let m14 = next_model m13 ev13 in
  lemma_step_model_many_cons_next m13 ev13 tail13 final_model;
  assert_norm (CS.step_model m13 ev13 == Some m14);
  assert (m14.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived);
  assert (m14.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m14.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m14.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m14.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m14.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m14.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (m14.CS.model_handshake.CS.hs_client_finished == Some cf);

  let m15 = next_model m14 ev14 in
  lemma_step_model_many_cons_next m14 ev14 tail14 final_model;
  lemma_local_install_for_role_preserves_slots m14 m15 app_read_install;
  assert (m15.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived);
  assert (m15.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m15.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m15.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m15.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m15.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m15.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (m15.CS.model_handshake.CS.hs_client_finished == Some cf);

  let m16 = next_model m15 ev15 in
  lemma_step_model_many_cons_next m15 ev15 tail15 final_model;
  assert_norm (CS.step_model m15 ev15 == Some m16);
  assert (m16.CS.model_handshake.CS.hs_client_hello == Some ch);
  assert (m16.CS.model_handshake.CS.hs_server_hello == Some sh);
  assert (m16.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (m16.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (m16.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (m16.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (m16.CS.model_handshake.CS.hs_client_finished == Some cf);
  assert_norm (CS.step_model_many m16 [] == Some m16);
  assert (m16 == final_model)

let lemma_server_successful_no_tail_semantic_trace_state_from_witnesses
  (server:CS.connection_state)
  (server_trace:list CS.conn_event)
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  (ee:M.encrypted_extensions)
  (cert:M.certificate_msg)
  (cv:M.certificate_verify)
  (sf:M.finished)
  (server_app_write_material:CS.traffic_key_material)
  (cf:M.finished)
  (server_app_read_material:CS.traffic_key_material)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        server_trace == server.CS.cs_event_log /\
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            [
              e5;
              e6;
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material;
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material;
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
            ] /\
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6)
      (ensures
        server_successful_no_tail_semantic_trace_state server server_trace)
=
  lemma_server_finished_shape_tls_message_projections
    server_trace
    ch
    selection
    server_shared
    sh
    e5
    e6
    ee
    cert
    cv
    sf
    server_app_write_material
    cf
    server_app_read_material;
  lemma_server_finished_shape_model_slots_from_event_log
    server
    ch
    selection
    server_shared
    sh
    e5
    e6
    ee
    cert
    cv
    sf
    server_app_write_material
    cf
    server_app_read_material;
  assert (server_successful_no_tail_semantic_trace_state_inputs
    server
    server_trace
    ch
    selection
    server_shared
    sh
    e5
    e6
    ee
    cert
    cv
    sf
    server_app_write_material
    cf
    server_app_read_material);
  introduce exists
    (ch0:M.client_hello)
    (selection0:CS.server_handshake_selection)
    (server_shared0:C.x25519_shared_secret)
    (sh0:M.server_hello)
    (e50:CS.conn_event)
    (e60:CS.conn_event)
    (ee0:M.encrypted_extensions)
    (cert0:M.certificate_msg)
    (cv0:M.certificate_verify)
    (sf0:M.finished)
    (server_app_write_material0:CS.traffic_key_material)
    (cf0:M.finished)
    (server_app_read_material0:CS.traffic_key_material).
    server_successful_no_tail_semantic_trace_state_inputs
      server
      server_trace
      ch0
      selection0
      server_shared0
      sh0
      e50
      e60
      ee0
      cert0
      cv0
      sf0
      server_app_write_material0
      cf0
      server_app_read_material0
  with
    ch
    selection
    server_shared
    sh
    e5
    e6
    ee
    cert
    cv
    sf
    server_app_write_material
    cf
    server_app_read_material
  and ()

let lemma_server_successful_no_tail_semantic_trace_state_from_no_ccs_boundary
  (server:CS.connection_state)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        PNTPH.server_no_tail_no_ccs_application_ready_boundary server /\
        server_trace == server.CS.cs_event_log)
      (ensures
        PNTPH.server_no_tail_post_two_handshake_installs_tail_order server /\
        server_successful_no_tail_semantic_trace_state server server_trace)
=
  PNTPH.lemma_server_no_tail_no_ccs_post_two_handshake_installs_tail_order server;
  eliminate exists
    (ch:M.client_hello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:M.server_hello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (rest:list CS.conn_event).
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    PNTSFShape.server_post_two_handshake_installs_tail_order rest
  returns
    PNTPH.server_no_tail_post_two_handshake_installs_tail_order server /\
    server_successful_no_tail_semantic_trace_state server server_trace
  with _.
  (
    eliminate exists
      (ee:M.encrypted_extensions)
      (cert:M.certificate_msg)
      (cv:M.certificate_verify)
      (sf:M.finished)
      (cf:M.finished)
      (server_app_write_material:CS.traffic_key_material)
      (server_app_read_material:CS.traffic_key_material).
      rest ==
        [
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          };
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            });
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished cf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_app_read_material;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
        ]
    returns
      PNTPH.server_no_tail_post_two_handshake_installs_tail_order server /\
      server_successful_no_tail_semantic_trace_state server server_trace
    with _.
    (
      assert (server_trace == server.CS.cs_event_log);
      assert (SD.server_driver_application_ready server);
      lemma_server_successful_no_tail_semantic_trace_state_from_witnesses
        server
        server_trace
        ch
        selection
        server_shared
        sh
        e5
        e6
        ee
        cert
        cv
        sf
        server_app_write_material
        cf
        server_app_read_material;
      assert (server_successful_no_tail_semantic_trace_state server server_trace)
    )
  )

let lemma_paired_successful_no_tail_semantic_traces_from_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces_no_ccs_boundary
          client
          server
          client_trace
          server_trace)
      (ensures
        paired_successful_no_tail_semantic_traces
          client
          server
          client_trace
          server_trace)
=
  lemma_client_successful_no_tail_semantic_trace_state_from_boundary
    client
    client_trace;
  lemma_server_successful_no_tail_semantic_trace_state_from_no_ccs_boundary
    server
    server_trace;
  assert (SD.server_driver_application_ready server);
  assert
    (paired_successful_no_tail_semantic_traces
      client
      server
      client_trace
      server_trace)

let lemma_paired_successful_no_tail_semantic_traces_paired_handshake_message_states
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces
          client
          server
          client_trace
          server_trace)
      (ensures Pairing.paired_handshake_message_states client server)
=
  eliminate exists
    (c_start:CS.handshake_start)
    (c_ch:M.client_hello)
    (c_sh:M.server_hello)
    (c_shared:C.x25519_shared_secret)
    (c_e4:CS.conn_event)
    (c_e5:CS.conn_event)
    (c_ee:M.encrypted_extensions)
    (c_cert:M.certificate_msg)
    (c_peer:X.peer_identity)
    (c_cv:M.certificate_verify)
    (c_sf:M.finished)
    (c_e13:CS.conn_event)
    (c_e14:CS.conn_event)
    (c_cf:M.finished).
    client_successful_no_tail_semantic_trace_state_inputs
      client
      client_trace
      c_start
      c_ch
      c_sh
      c_shared
      c_e4
      c_e5
      c_ee
      c_cert
      c_peer
      c_cv
      c_sf
      c_e13
      c_e14
      c_cf
  returns
    Pairing.paired_handshake_message_states client server
  with _.
  eliminate exists
    (s_ch:M.client_hello)
    (s_selection:CS.server_handshake_selection)
    (s_shared:C.x25519_shared_secret)
    (s_sh:M.server_hello)
    (s_e5:CS.conn_event)
    (s_e6:CS.conn_event)
    (s_ee:M.encrypted_extensions)
    (s_cert:M.certificate_msg)
    (s_cv:M.certificate_verify)
    (s_sf:M.finished)
    (s_app_write:CS.traffic_key_material)
    (s_cf:M.finished)
    (s_app_read:CS.traffic_key_material).
    server_successful_no_tail_semantic_trace_state_inputs
      server
      server_trace
      s_ch
      s_selection
      s_shared
      s_sh
      s_e5
      s_e6
      s_ee
      s_cert
      s_cv
      s_sf
      s_app_write
      s_cf
      s_app_read
  returns
    Pairing.paired_handshake_message_states client server
  with _.
  ( assert
      (CS.sent_tls_messages client_trace ==
        [
          M.TlsHandshake (M.ClientHello c_ch);
          M.TlsHandshake (M.Finished c_cf)
        ]);
    assert
      (CS.received_tls_messages server_trace ==
        [
          M.TlsHandshake (M.ClientHello s_ch);
          M.TlsHandshake (M.Finished s_cf)
        ]);
    assert
      (CS.sent_tls_messages client_trace ==
        CS.received_tls_messages server_trace);
    assert
      ([
        M.TlsHandshake (M.ClientHello c_ch);
        M.TlsHandshake (M.Finished c_cf)
       ] ==
       [
        M.TlsHandshake (M.ClientHello s_ch);
        M.TlsHandshake (M.Finished s_cf)
       ]);
    assert (c_ch == s_ch);
    assert (c_cf == s_cf);
    assert
      (CS.sent_tls_messages server_trace ==
        [
          M.TlsHandshake (M.ServerHello s_sh);
          M.TlsHandshake (M.EncryptedExtensions s_ee);
          M.TlsHandshake (M.Certificate s_cert);
          M.TlsHandshake (M.CertificateVerify s_cv);
          M.TlsHandshake (M.Finished s_sf)
        ]);
    assert
      (CS.received_tls_messages client_trace ==
        [
          M.TlsHandshake (M.ServerHello c_sh);
          M.TlsHandshake (M.EncryptedExtensions c_ee);
          M.TlsHandshake (M.Certificate c_cert);
          M.TlsHandshake (M.CertificateVerify c_cv);
          M.TlsHandshake (M.Finished c_sf)
        ]);
    assert
      (CS.sent_tls_messages server_trace ==
        CS.received_tls_messages client_trace);
    assert
      ([
        M.TlsHandshake (M.ServerHello s_sh);
        M.TlsHandshake (M.EncryptedExtensions s_ee);
        M.TlsHandshake (M.Certificate s_cert);
        M.TlsHandshake (M.CertificateVerify s_cv);
        M.TlsHandshake (M.Finished s_sf)
       ] ==
       [
        M.TlsHandshake (M.ServerHello c_sh);
        M.TlsHandshake (M.EncryptedExtensions c_ee);
        M.TlsHandshake (M.Certificate c_cert);
        M.TlsHandshake (M.CertificateVerify c_cv);
        M.TlsHandshake (M.Finished c_sf)
       ]);
    assert (s_sh == c_sh);
    assert (s_ee == c_ee);
    assert (s_cert == c_cert);
    assert (s_cv == c_cv);
    assert (s_sf == c_sf);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some c_ch);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some s_ch);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some c_sh);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some s_sh);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
        Some c_ee);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions ==
        Some s_ee);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_certificate ==
        Some c_cert);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_certificate ==
        Some s_cert);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
        Some c_cv);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
        Some s_cv);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        Some c_sf);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        Some s_sf);
    assert
      (client.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
        Some c_cf);
    assert
      (server.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==
        Some s_cf);
    assert (Pairing.paired_handshake_message_states client server) )

let lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_traces
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces
          client
          server
          client_trace
          server_trace)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_paired_successful_no_tail_semantic_traces_paired_handshake_message_states
    client
    server
    client_trace
    server_trace;
  Pairing.lemma_client_server_application_record_material_agrees_from_paired_handshake_message_states
    client
    server

let lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_traces_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_trace:list CS.conn_event)
  (server_trace:list CS.conn_event)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_traces_no_ccs_boundary
          client
          server
          client_trace
          server_trace)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_paired_successful_no_tail_semantic_traces_from_no_ccs_boundary
    client
    server
    client_trace
    server_trace;
  lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_traces
    client
    server
    client_trace
    server_trace

noextract
let handshake_message_slots_equal_model
  (model0:CS.connection_model)
  (model1:CS.connection_model)
  : prop =
  model1.CS.model_handshake.CS.hs_client_hello ==
    model0.CS.model_handshake.CS.hs_client_hello /\
  model1.CS.model_handshake.CS.hs_server_hello ==
    model0.CS.model_handshake.CS.hs_server_hello /\
  model1.CS.model_handshake.CS.hs_encrypted_extensions ==
    model0.CS.model_handshake.CS.hs_encrypted_extensions /\
  model1.CS.model_handshake.CS.hs_certificate ==
    model0.CS.model_handshake.CS.hs_certificate /\
  model1.CS.model_handshake.CS.hs_certificate_verify ==
    model0.CS.model_handshake.CS.hs_certificate_verify /\
  model1.CS.model_handshake.CS.hs_server_finished ==
    model0.CS.model_handshake.CS.hs_server_finished /\
  model1.CS.model_handshake.CS.hs_client_finished ==
    model0.CS.model_handshake.CS.hs_client_finished

let lemma_application_data_step_preserves_handshake_message_slots
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlApplicationData /\
        CS.legal_event model ev /\
        CS.conn_event_is_key_update ev == false /\
        conn_event_is_ccs ev == false /\
        CS.step_model model ev == Some model1 /\
        model1.CS.model_control == CS.ControlApplicationData)
      (ensures handshake_message_slots_equal_model model model1)
=
  match ev with
  | CS.ConnLocalEvent local ->
    (match local with
     | CS.LocalDeliverApplicationData _ ->
       assert_norm (CS.step_model model ev == Some model1)
     | CS.LocalFail err ->
       assert_norm (CS.step_model model ev == Some (CS.fail_model model err));
       assert (model1 == CS.fail_model model err);
       assert (model1.CS.model_control == CS.ControlFailed err);
       assert False
     | _ ->
       assert_norm (CS.step_model model ev == None);
       assert False)
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsApplicationData _ ->
       assert_norm (CS.step_model model ev == Some model1)
     | M.TlsIgnoredPostHandshake _ ->
       (match msg.CL.message_direction with
        | CL.Received ->
          assert_norm (CS.step_model model ev == Some model1)
        | CL.Sent ->
          assert_norm (CS.step_model model ev == None);
          assert False)
     | M.TlsKeyUpdate _ ->
       assert_norm (CS.conn_event_is_key_update ev == true);
       assert False
     | M.TlsAlert alert ->
       (match alert with
        | T.CloseNotify ->
          (match msg.CL.message_direction with
           | CL.Sent ->
             assert_norm (CS.step_model model ev == Some model1);
             assert (model1.CS.model_control == CS.ControlClosing);
             assert False
           | CL.Received ->
             assert_norm (CS.step_model model ev == Some model1);
             assert (model1.CS.model_control == CS.ControlClosed);
             assert False)
        | _ ->
          assert_norm
            (CS.step_model model ev ==
              Some (CS.fail_model model (T.AlertError alert)));
          assert (model1 == CS.fail_model model (T.AlertError alert));
          assert (model1.CS.model_control == CS.ControlFailed (T.AlertError alert));
          assert False)
     | M.TlsChangeCipherSpec ->
       assert_norm (conn_event_is_ccs ev == true);
       assert False
     | M.TlsHandshake _ ->
       assert_norm (CS.step_model model ev == None);
       assert False)

let rec lemma_application_data_preserving_semantic_suffix_preserves_handshake_message_slots
  (model:CS.connection_model)
  (suffix:list CS.conn_event)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        application_data_preserving_semantic_suffix model suffix final_model)
      (ensures
        handshake_message_slots_equal_model model final_model /\
        final_model.CS.model_control == CS.ControlApplicationData)
      (decreases suffix)
=
  match suffix with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    match CS.step_model model ev with
    | Some model1 ->
      assert (model1.CS.model_control == CS.ControlApplicationData);
      lemma_application_data_step_preserves_handshake_message_slots
        model
        model1
        ev;
      lemma_application_data_preserving_semantic_suffix_preserves_handshake_message_slots
        model1
        rest
        final_model;
      assert (handshake_message_slots_equal_model model model1);
      assert (handshake_message_slots_equal_model model1 final_model);
      assert (handshake_message_slots_equal_model model final_model)
    | None ->
      assert False

let lemma_paired_handshake_message_states_preserved_by_application_suffixes
  (client_prefix:CS.connection_state)
  (server_prefix:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_suffix:list CS.conn_event)
  (server_suffix:list CS.conn_event)
  : Lemma
      (requires
        Pairing.paired_handshake_message_states client_prefix server_prefix /\
        application_data_preserving_semantic_suffix
          client_prefix.CS.cs_model
          client_suffix
          client.CS.cs_model /\
        application_data_preserving_semantic_suffix
          server_prefix.CS.cs_model
          server_suffix
          server.CS.cs_model)
      (ensures Pairing.paired_handshake_message_states client server)
=
  lemma_application_data_preserving_semantic_suffix_preserves_handshake_message_slots
    client_prefix.CS.cs_model
    client_suffix
    client.CS.cs_model;
  lemma_application_data_preserving_semantic_suffix_preserves_handshake_message_slots
    server_prefix.CS.cs_model
    server_suffix
    server.CS.cs_model;
  assert (handshake_message_slots_equal_model client_prefix.CS.cs_model client.CS.cs_model);
  assert (handshake_message_slots_equal_model server_prefix.CS.cs_model server.CS.cs_model);
  assert (Pairing.paired_handshake_message_states client server)

let lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_logs_no_ccs_exact_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_logs_no_ccs_exact_boundary
          client
          server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_traces_no_ccs_boundary
    client
    server
    client.CS.cs_event_log
    server.CS.cs_event_log

let lemma_client_server_application_record_material_agrees_from_paired_successful_no_tail_semantic_logs_no_ccs_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_successful_no_tail_semantic_logs_no_ccs_boundary
          client
          server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  eliminate exists
    (client_prefix:CS.connection_state)
    (server_prefix:CS.connection_state)
    (client_suffix:list CS.conn_event)
    (server_suffix:list CS.conn_event).
    paired_successful_no_tail_semantic_logs_no_ccs_exact_boundary
      client_prefix
      server_prefix /\
    client.CS.cs_event_log ==
      FStar.List.Tot.append client_prefix.CS.cs_event_log client_suffix /\
    server.CS.cs_event_log ==
      FStar.List.Tot.append server_prefix.CS.cs_event_log server_suffix /\
    application_data_preserving_semantic_suffix
      client_prefix.CS.cs_model
      client_suffix
      client.CS.cs_model /\
    application_data_preserving_semantic_suffix
      server_prefix.CS.cs_model
      server_suffix
      server.CS.cs_model
  returns
    CS.supported_profile_client_server_key_material_agrees client server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    CS.peer_record_material_agrees
      (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  (
    lemma_paired_successful_no_tail_semantic_traces_from_no_ccs_boundary
      client_prefix
      server_prefix
      client_prefix.CS.cs_event_log
      server_prefix.CS.cs_event_log;
    lemma_paired_successful_no_tail_semantic_traces_paired_handshake_message_states
      client_prefix
      server_prefix
      client_prefix.CS.cs_event_log
      server_prefix.CS.cs_event_log;
    lemma_paired_handshake_message_states_preserved_by_application_suffixes
      client_prefix
      server_prefix
      client
      server
      client_suffix
      server_suffix;
    Pairing.lemma_client_server_application_record_material_agrees_from_paired_handshake_message_states
      client
      server
  )
 
#pop-options
