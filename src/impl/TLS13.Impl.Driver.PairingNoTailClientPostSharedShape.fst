module TLS13.Impl.Driver.PairingNoTailClientPostSharedShape

#lang-pulse

open Pulse.Lib.Pervasives

module CL = TLS13.ConnectionLog
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module Sem   = TLS13.Wire.Semantics
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module Tr = TLS13.Transcript

let client_no_tail_handshake_write_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake /\
    install.CS.install_direction == CS.TrafficWrite
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ClientEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | _ ->
    False

let client_no_tail_handshake_read_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake /\
    install.CS.install_direction == CS.TrafficRead
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ClientEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | _ ->
    False

let client_no_tail_two_handshake_install_cover
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  : prop =
  (client_no_tail_handshake_write_install_event e4 /\
   client_no_tail_handshake_read_install_event e5) \/
  (client_no_tail_handshake_read_install_event e4 /\
   client_no_tail_handshake_write_install_event e5)

let lemma_client_no_tail_handshake_write_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_write_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficHandshake /\
          install.CS.install_direction == CS.TrafficWrite
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
        | _ ->
          False))
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> ()
  | _ -> assert False

let lemma_client_no_tail_handshake_read_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_read_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficHandshake /\
          install.CS.install_direction == CS.TrafficRead
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
        | _ ->
          False))
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> ()
  | _ -> assert False

let lemma_client_no_tail_handshake_write_install_event_implies_handshake_traffic_install_event
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_write_install_event ev)
      (ensures PNI.client_no_tail_handshake_traffic_install_event ev)
=
  lemma_client_no_tail_handshake_write_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> ()
  | _ -> assert False

let lemma_client_no_tail_handshake_read_install_event_implies_handshake_traffic_install_event
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_read_install_event ev)
      (ensures PNI.client_no_tail_handshake_traffic_install_event ev)
=
  lemma_client_no_tail_handshake_read_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> ()
  | _ -> assert False

let lemma_client_no_tail_two_handshake_install_cover_cases
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  : Lemma
      (requires client_no_tail_two_handshake_install_cover e4 e5)
      (ensures
        (client_no_tail_handshake_write_install_event e4 /\
         client_no_tail_handshake_read_install_event e5) \/
        (client_no_tail_handshake_read_install_event e4 /\
         client_no_tail_handshake_write_install_event e5))
=
  ()

let lemma_client_no_tail_handshake_write_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_handshake_write_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              })) == Some model1)
=
  lemma_client_no_tail_handshake_write_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficWrite);
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficWrite);
    assert_norm (
      CS.step_model model ev ==
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = install.CS.install_material;
          })));
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | _ ->
    assert False

let lemma_client_no_tail_handshake_read_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_handshake_read_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              })) == Some model1)
=
  lemma_client_no_tail_handshake_read_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficRead);
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficRead);
    assert_norm (
      CS.step_model model ev ==
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = install.CS.install_material;
          })));
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | _ ->
    assert False

let lemma_client_no_tail_handshake_install_event_direction_cases
  (ev:CS.conn_event)
  : Lemma
      (requires PNI.client_no_tail_handshake_traffic_install_event ev)
      (ensures
        client_no_tail_handshake_write_install_event ev \/
        client_no_tail_handshake_read_install_event ev)
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match install.CS.install_direction with
     | CS.TrafficWrite -> ()
     | CS.TrafficRead -> ())
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    (match role_install.CS.install_payload.CS.install_direction with
     | CS.TrafficWrite -> ()
     | CS.TrafficRead -> ())
  | _ ->
    assert False

(** The seven "late" client handshake stages between [EncryptedExtensions]
    receipt and the (as yet unconfirmed) server-finished verification,
    excluding [HsServerHelloReceived] itself. *)
noextract
let client_late_handshake_stage (stage:CS.handshake_stage) : prop =
  match stage with
  | CS.HsEncryptedExtensionsReceived
  | CS.HsCertificateReceived
  | CS.HsCertificateValidated
  | CS.HsCertificateVerifyReceived
  | CS.HsCertificateVerifyVerified
  | CS.HsServerFinishedReceived
  | CS.HsServerFinishedVerified ->
    True
  | _ ->
    False

(** A client-role model that is either already failed, or parked at one of
    the seven late handshake stages, with the client handshake-traffic key
    never installed. *)
noextract
let client_late_stuck (model:CS.connection_model) : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
  (match model.CS.model_control with
   | CS.ControlFailed _ -> True
   | CS.ControlHandshaking stage -> client_late_handshake_stage stage
   | _ -> False)

(** None of the seven late client handshake stages is [HsServerHelloReceived]. *)
let lemma_late_stage_not_server_hello_received
  (stage:CS.handshake_stage)
  : Lemma
      (requires client_late_handshake_stage stage)
      (ensures stage =!= CS.HsServerHelloReceived)
=
  match stage with
  | CS.HsServerHelloReceived -> assert False
  | _ -> ()

(**
  Single-step preservation of [client_late_stuck].

  We match first on [ev] (the [conn_event] under evaluation) and only then, if
  necessary, on [model.model_control]/[stage]: most [local_event]/
  [tls_message] constructors are directly illegal at any [ControlHandshaking]
  stage with client role (their [legal_local_event]/[legal_handshake_message]
  clauses require either [ControlNew]/[ControlApplicationData] or a server
  role or a handshake stage disjoint from the seven late stages), so those
  cases close by contradiction without needing to know exactly which late
  stage [model] is at. Only the traffic-key installs (stage-independent) and
  the six stage-specific "advancing" events need a genuine case split on
  [stage].
**)
#push-options "--split_queries always --z3rlimit 10"
let lemma_client_late_stuck_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model1:CS.connection_model)
  : Lemma
      (requires
        client_late_stuck model /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1)
      (ensures client_late_stuck model1)
=
  CSL.lemma_step_model_preserves_config model ev model1;
  match model.CS.model_control with
  | CS.ControlFailed _ ->
    (match ev with
     | CS.ConnLocalEvent local ->
       (match local with
        | CS.LocalFail err ->
          assert_norm (CS.step_model model ev == Some (CS.fail_model model err))
        | CS.LocalStartHandshake _ -> assert False
        | CS.LocalStartServer -> assert False
        | CS.LocalSelectServerParameters _ -> assert False
        | CS.LocalDeriveSharedSecret _ -> assert False
        | CS.LocalInstallTrafficKeys _ -> assert False
        | CS.LocalInstallTrafficKeysForRole _ -> assert False
        | CS.LocalValidateCertificate _ -> assert False
        | CS.LocalVerifyCertificateSignature _ -> assert False
        | CS.LocalSignCertificateVerify _ -> assert False
        | CS.LocalVerifyFinished _ -> assert False
        | CS.LocalVerifyClientFinished _ -> assert False
        | CS.LocalDeliverApplicationData _ -> assert False)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_value with
        | M.TlsAlert alert ->
          assert_norm (
            CS.step_model model ev == Some (CS.fail_model model (T.AlertError alert)))
        | M.TlsHandshake _ -> assert False
        | M.TlsApplicationData _ -> assert False
        | M.TlsIgnoredPostHandshake _ -> assert False
        | M.TlsKeyUpdate _ -> assert False
        | M.TlsChangeCipherSpec -> assert False))
  | CS.ControlHandshaking stage ->
    assert (client_late_handshake_stage stage);
    (match ev with
     | CS.ConnLocalEvent local ->
       (match local with
        | CS.LocalFail err ->
          assert_norm (CS.step_model model ev == Some (CS.fail_model model err))
        | CS.LocalStartHandshake _ -> assert False
        | CS.LocalStartServer -> assert False
        | CS.LocalSelectServerParameters _ -> assert False
        | CS.LocalDeriveSharedSecret _ ->
          lemma_late_stage_not_server_hello_received stage;
          assert False
        | CS.LocalInstallTrafficKeys install ->
          assert_norm (
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
          assert (CS.traffic_install_allowed_at_stage stage install);
          (match install.CS.install_epoch with
           | CS.TrafficHandshake ->
             lemma_late_stage_not_server_hello_received stage;
             assert False
           | CS.TrafficApplication ->
             assert (stage == CS.HsServerFinishedVerified);
             (match install.CS.install_direction with
              | CS.TrafficWrite ->
                assert_norm (
                  CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
                  CS.ClientTraffic);
                assert_norm (
                  CS.update_key_schedule_with_label
                    model.CS.model_handshake.CS.hs_keys
                    CS.TrafficApplication
                    CS.ClientTraffic
                    install.CS.install_material ==
                  { model.CS.model_handshake.CS.hs_keys with
                      CS.ks_client_application_traffic = Some install.CS.install_material });
                assert (
                  model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                  model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
              | CS.TrafficRead ->
                assert_norm (
                  CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
                  CS.ServerTraffic);
                assert_norm (
                  CS.update_key_schedule_with_label
                    model.CS.model_handshake.CS.hs_keys
                    CS.TrafficApplication
                    CS.ServerTraffic
                    install.CS.install_material ==
                  { model.CS.model_handshake.CS.hs_keys with
                      CS.ks_server_application_traffic = Some install.CS.install_material });
                assert (
                  model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                  model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)))
        | CS.LocalInstallTrafficKeysForRole role_install ->
          assert (role_install.CS.install_role == CS.ClientEndpoint);
          let install = role_install.CS.install_payload in
          assert_norm (
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
          assert (
            CS.traffic_install_allowed_at_stage_for_role
              role_install.CS.install_role
              stage
              install);
          assert (CS.traffic_install_allowed_at_stage stage install);
          (match install.CS.install_epoch with
           | CS.TrafficHandshake ->
             lemma_late_stage_not_server_hello_received stage;
             assert False
           | CS.TrafficApplication ->
             assert (stage == CS.HsServerFinishedVerified);
             (match install.CS.install_direction with
              | CS.TrafficWrite ->
                assert_norm (
                  CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
                  CS.ClientTraffic);
                assert_norm (
                  CS.update_key_schedule_with_label
                    model.CS.model_handshake.CS.hs_keys
                    CS.TrafficApplication
                    CS.ClientTraffic
                    install.CS.install_material ==
                  { model.CS.model_handshake.CS.hs_keys with
                      CS.ks_client_application_traffic = Some install.CS.install_material });
                assert (
                  model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                  model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)
              | CS.TrafficRead ->
                assert_norm (
                  CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
                  CS.ServerTraffic);
                assert_norm (
                  CS.update_key_schedule_with_label
                    model.CS.model_handshake.CS.hs_keys
                    CS.TrafficApplication
                    CS.ServerTraffic
                    install.CS.install_material ==
                  { model.CS.model_handshake.CS.hs_keys with
                      CS.ks_server_application_traffic = Some install.CS.install_material });
                assert (
                  model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                  model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic)))
        | CS.LocalValidateCertificate peer ->
          (match stage with
           | CS.HsCertificateReceived ->
             assert_norm (
               CS.step_model model ev ==
               Some (CS.with_handshake_stage
                 model
                 { model.CS.model_handshake with CS.hs_validated_peer = Some peer }
                 CS.HsCertificateValidated))
           | _ -> assert False)
        | CS.LocalVerifyCertificateSignature cv ->
          (match stage with
           | CS.HsCertificateVerifyReceived ->
             assert_norm (
               CS.step_model model ev ==
               Some (CS.with_handshake_stage
                 model
                 { model.CS.model_handshake with
                     CS.hs_certificate_verify = Some cv;
                     CS.hs_certificate_verify_verified = true;
                 }
                 CS.HsCertificateVerifyVerified))
           | _ -> assert False)
        | CS.LocalSignCertificateVerify _ -> assert False
        | CS.LocalVerifyFinished fin ->
          (match stage with
           | CS.HsServerFinishedReceived ->
             assert_norm (
               CS.step_model model ev ==
               Some (CS.with_handshake_stage
                 model
                 (CS.append_handshake_to_transcript
                   { model.CS.model_handshake with
                       CS.hs_server_finished = Some fin;
                       CS.hs_server_finished_verified = true;
                   }
                   (M.Finished fin))
                 CS.HsServerFinishedVerified))
           | _ -> assert False)
        | CS.LocalVerifyClientFinished _ -> assert False
        | CS.LocalDeliverApplicationData _ -> assert False)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_value with
        | M.TlsHandshake hmsg ->
          (match msg.CL.message_direction, hmsg with
           | CL.Sent, M.ClientHello _ -> assert False
           | CL.Received, M.ClientHello _ -> assert False
           | CL.Received, M.ServerHello _ -> assert False
           | CL.Sent, M.ServerHello _ -> assert False
           | CL.Sent, M.EncryptedExtensions _ -> assert False
           | CL.Sent, M.Certificate _ -> assert False
           | CL.Sent, M.CertificateVerify _ -> assert False
           | CL.Sent, M.Finished _ ->
             (match stage with
              | CS.HsServerFinishedVerified ->
                assert (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
                assert False
              | _ -> assert False)
           | CL.Received, M.EncryptedExtensions _ ->
             lemma_late_stage_not_server_hello_received stage;
             assert False
           | CL.Received, M.Certificate cert ->
             (match stage with
              | CS.HsEncryptedExtensionsReceived ->
                assert_norm (
                  CS.step_model model ev ==
                  Some (CS.with_handshake_stage
                    { model with
                        CS.model_record = {
                          model.CS.model_record with
                            CS.record_read = R.next_seq model.CS.model_record.CS.record_read;
                        };
                    }
                    (CS.append_handshake_to_transcript
                      { model.CS.model_handshake with
                          CS.hs_certificate = Some cert;
                          CS.hs_buffers = {
                            model.CS.model_handshake.CS.hs_buffers with
                              CS.hb_certificate_leaf_der =
                                (match (Sem.certificate_entries cert) with
                                 | leaf :: _ -> Some leaf
                                 | [] -> None);
                          };
                      }
                      (M.Certificate cert))
                    CS.HsCertificateReceived))
              | _ -> assert False)
           | CL.Received, M.CertificateVerify cv ->
             (match stage with
              | CS.HsCertificateValidated ->
                assert_norm (
                  CS.step_model model ev ==
                  Some (CS.with_handshake_stage
                    { model with
                        CS.model_record = {
                          model.CS.model_record with
                            CS.record_read = R.next_seq model.CS.model_record.CS.record_read;
                        };
                    }
                    (CS.append_handshake_to_transcript
                      { model.CS.model_handshake with
                          CS.hs_certificate_verify = Some cv;
                          CS.hs_buffers = {
                            model.CS.model_handshake.CS.hs_buffers with
                              CS.hb_certificate_verify_input =
                                Some (H.certificate_verify_input
                                  (Tr.hash model.CS.model_handshake.CS.hs_transcript));
                          };
                      }
                      (M.CertificateVerify cv))
                    CS.HsCertificateVerifyReceived))
              | _ -> assert False)
           | CL.Received, M.Finished fin ->
             (match stage with
              | CS.HsCertificateVerifyVerified ->
                assert_norm (
                  CS.step_model model ev ==
                  Some (CS.with_handshake_stage
                    { model with
                        CS.model_record = {
                          model.CS.model_record with
                            CS.record_read = R.next_seq model.CS.model_record.CS.record_read;
                        };
                    }
                    { model.CS.model_handshake with CS.hs_server_finished = Some fin }
                    CS.HsServerFinishedReceived))
              | _ -> assert False)
           | CL.Received, M.HelloRetryRequest -> assert False)
        | M.TlsApplicationData _ -> assert False
        | M.TlsIgnoredPostHandshake _ -> assert False
        | M.TlsKeyUpdate _ -> assert False
        | M.TlsAlert alert ->
          assert_norm (
            CS.step_model model ev == Some (CS.fail_model model (T.AlertError alert)))
        | M.TlsChangeCipherSpec ->
          assert_norm (CS.step_model model ev == Some model)))
  | _ -> assert False
#pop-options

(**
  Corollary of [lemma_client_late_stuck_step]: a [client_late_stuck] model can
  never raw-replay to [ControlApplicationData], by induction on [events].
**)
#push-options "--split_queries always --z3rlimit 10"
let rec lemma_client_late_stuck_replay_not_application_ready
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_late_stuck model /\
        CS.conn_events_raw_replay model events raw_sent raw_received final_model)
      (ensures ~ (final_model.CS.model_control == CS.ControlApplicationData))
      (decreases events)
=
  match events with
  | [] ->
    assert_norm (
      CS.conn_events_raw_replay model [] raw_sent raw_received final_model ==
      (Seq.equal raw_sent B.empty /\
       Seq.equal raw_received B.empty /\
       final_model == model));
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
    returns ~ (final_model.CS.model_control == CS.ControlApplicationData)
    with _.
    (
      lemma_client_late_stuck_step model ev model1;
      lemma_client_late_stuck_replay_not_application_ready
        model1
        rest
        tail_sent
        tail_received
        final_model
    )
#pop-options

(** [PNI.client_application_progress_rank] right after the first
    handshake-traffic install: exactly one of [ks_client_handshake_traffic]/
    [ks_server_handshake_traffic] is present, and it is always [11]. **)
let lemma_client_post_first_install_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic <==>
         None? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic) /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
      (ensures PNI.client_application_progress_rank model == 11)
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
    | Some _, None, Some _, None, None ->
      assert (PNI.option_missing keys.CS.ks_shared_secret == 0);
      assert (PNI.option_missing keys.CS.ks_client_handshake_traffic == 1);
      assert (PNI.option_missing keys.CS.ks_server_handshake_traffic == 0);
      assert (PNI.client_app_obligation_rank keys == 2);
      assert (PNI.client_early_obligation_rank keys == 3);
      assert (PNI.client_application_progress_rank model == 11)
    | Some _, Some _, None, None, None ->
      assert (PNI.option_missing keys.CS.ks_shared_secret == 0);
      assert (PNI.option_missing keys.CS.ks_client_handshake_traffic == 0);
      assert (PNI.option_missing keys.CS.ks_server_handshake_traffic == 1);
      assert (PNI.client_app_obligation_rank keys == 2);
      assert (PNI.client_early_obligation_rank keys == 3);
      assert (PNI.client_application_progress_rank model == 11)
    | _ ->
      assert False)
  | _ ->
    assert False

(** If, after the second local handshake install, the model still has only one
    handshake direction installed, the remaining ten events cannot reach
    application data. *)
#push-options "--split_queries always --z3rlimit 10"
let lemma_client_second_duplicate_install_tail10_contradiction
  (model6:CS.connection_model)
  (rest2:list CS.conn_event)
  (raw_sent raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model6.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        (Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic <==>
         None? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic) /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        CS.conn_events_raw_replay model6 rest2 raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest2 == 10)
      (ensures False)
=
  lemma_client_post_first_install_progress_rank model6;
  PNI.lemma_client_application_progress_rank_replay_lower_bound
    model6
    rest2
    raw_sent
    raw_received
    final_model;
  assert (PNI.client_application_progress_rank model6 == 11);
  assert (PNI.client_application_progress_rank model6 <= FStar.List.Tot.length rest2);
  assert (11 <= 10);
  assert False
#pop-options

(**
  Generalization of
  [PNI.lemma_client_post_derive_next_event_handshake_traffic_install] to the
  state right after the first handshake-traffic install ([model]): the next
  event [ev] is again a clean client handshake-traffic install event.

  The proof mirrors
  [PNI.lemma_client_post_derive_next_event_handshake_traffic_install] almost
  exactly (reusing the same exposed no-progress/illegality helpers), with one
  new case: [Received EncryptedExtensions] is legal here whenever
  [ks_server_handshake_traffic] is already [Some] (unlike at [model4], where
  it is always [None]). In that case the resulting model is
  [client_late_stuck] (it lands on [HsEncryptedExtensionsReceived] with
  [ks_client_handshake_traffic] still [None]), so
  [lemma_client_late_stuck_replay_not_application_ready] rules out the
  hypothesized application-ready continuation.
**)
#push-options "--split_queries always --z3rlimit 10"
let lemma_client_post_first_install_next_event_handshake_traffic_install
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
        (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic <==>
         None? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic) /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        CS.conn_events_raw_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 10)
      (ensures PNI.client_no_tail_handshake_traffic_install_event ev)
=
  lemma_client_post_first_install_progress_rank model;
  assert (PNI.client_application_progress_rank model == 11);
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
    PNI.client_no_tail_handshake_traffic_install_event ev
  with _.
  (
    CSL.lemma_step_model_preserves_config model ev model1;
    assert (model1.CS.model_config == model.CS.model_config);
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
         assert (
           model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
           model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
         assert (
           model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic ==
           model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
         assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
         assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
         assert (
           Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic <==>
           None? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
         lemma_client_post_first_install_progress_rank model1;
         PNI.lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (PNI.client_application_progress_rank model1 == 11);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (FStar.List.Tot.length rest == 10);
         assert (11 <= 10);
         assert False
       | CS.LocalInstallTrafficKeys install ->
         assert (ev == CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install));
         assert (CS.legal_local_event model local);
         assert (CS.traffic_install_allowed_at_stage CS.HsServerHelloReceived install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake ->
            assert (PNI.client_no_tail_handshake_traffic_install_event ev)
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
            assert (PNI.client_no_tail_handshake_traffic_install_event ev)
          | CS.TrafficApplication ->
            assert_norm (CS.traffic_install_allowed_at_stage_for_role
              CS.ClientEndpoint
              CS.HsServerHelloReceived
              role_install.CS.install_payload == False);
            assert False)
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
         assert (final_model.CS.model_control == CS.ControlApplicationData);
         assert False
       | M.TlsChangeCipherSpec ->
         assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == Some model);
         assert (model1 == model);
         PNI.lemma_client_application_progress_rank_replay_lower_bound
           model1
           rest
           tail_sent
           tail_received
           final_model;
         assert (PNI.client_application_progress_rank model1 == 11);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (FStar.List.Tot.length rest == 10);
         assert (11 <= 10);
         assert False
       | M.TlsHandshake handshake_msg ->
         (match msg.CL.message_direction, handshake_msg with
          | CL.Received, M.EncryptedExtensions ee ->
            (match model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
             | None ->
               PNI.lemma_client_hs_server_hello_received_empty_keys_encrypted_extensions_illegal
                 model
                 ee;
               assert False
             | Some _ ->
               assert_norm (
                 CS.step_model model (CS.ConnNetworkEvent msg) ==
                 Some (CS.with_handshake_stage
                   { model with
                       CS.model_record = {
                         model.CS.model_record with
                           CS.record_read = R.next_seq model.CS.model_record.CS.record_read;
                       };
                   }
                   (CS.append_handshake_to_transcript
                     { model.CS.model_handshake with CS.hs_encrypted_extensions = Some ee }
                     (M.EncryptedExtensions ee))
                   CS.HsEncryptedExtensionsReceived));
               assert (model1.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived);
               assert (
                 model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==
                 model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
               assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
               assert (client_late_handshake_stage CS.HsEncryptedExtensionsReceived);
               assert (client_late_stuck model1);
               lemma_client_late_stuck_replay_not_application_ready
                 model1
                 rest
                 tail_sent
                 tail_received
                 final_model;
               assert (~ (final_model.CS.model_control == CS.ControlApplicationData));
               assert (final_model.CS.model_control == CS.ControlApplicationData);
               assert False)
          | _, _ ->
            PNI.lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
              model
              msg;
            assert (CS.step_model model ev == None);
            assert False)
       | M.TlsApplicationData _ ->
         PNI.lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False
       | M.TlsIgnoredPostHandshake _ ->
         PNI.lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False
       | M.TlsKeyUpdate _ ->
         PNI.lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
           model
           msg;
         assert (CS.step_model model ev == None);
         assert False)
  )
#pop-options

(**
  Isolated (small-context) shape lemma: once [e4] is known to be a clean
  handshake-traffic install event and [model4] is the abstract post-derive
  state, pin down the key-schedule shape of the resulting [model5] without
  needing this reasoning inline inside a larger proof context.
**)
#push-options "--split_queries always --z3rlimit 10"
let lemma_client_post_first_install_model_shape
  (model4 model5:CS.connection_model)
  (e4:CS.conn_event)
  : Lemma
      (requires
        model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        PNI.client_no_tail_handshake_traffic_install_event e4 /\
        CS.step_model model4 e4 == Some model5)
      (ensures
        model5.CS.model_config == model4.CS.model_config /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        (Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic <==>
         None? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic) /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
=
  CSL.lemma_step_model_preserves_config model4 e4 model5;
  (match e4 with
   | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
     assert (
       CS.step_model model4 e4 ==
       Some {
         model4 with
           CS.model_record = CS.install_record_keys model4.CS.model_record install;
           CS.model_handshake = {
             model4.CS.model_handshake with
               CS.hs_keys =
                 CS.update_key_schedule_with_install
                   model4.CS.model_handshake.CS.hs_keys
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
            model4.CS.model_handshake.CS.hs_keys
            CS.TrafficHandshake
            CS.ClientTraffic
            install.CS.install_material ==
          { model4.CS.model_handshake.CS.hs_keys with
              CS.ks_client_handshake_traffic = Some install.CS.install_material })
      | CS.TrafficRead ->
        assert_norm (
          CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
          CS.ServerTraffic);
        assert_norm (
          CS.update_key_schedule_with_label
            model4.CS.model_handshake.CS.hs_keys
            CS.TrafficHandshake
            CS.ServerTraffic
            install.CS.install_material ==
          { model4.CS.model_handshake.CS.hs_keys with
              CS.ks_server_handshake_traffic = Some install.CS.install_material }))
   | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
     assert (role_install.CS.install_role == CS.ClientEndpoint);
     let install = role_install.CS.install_payload in
     assert (
       CS.step_model model4 e4 ==
       Some {
         model4 with
           CS.model_record =
             CS.install_record_keys_for_role
               role_install.CS.install_role
               model4.CS.model_record
               install;
           CS.model_handshake = {
             model4.CS.model_handshake with
               CS.hs_keys =
                 CS.update_key_schedule_with_install_for_role
                   role_install.CS.install_role
                   model4.CS.model_handshake.CS.hs_keys
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
            model4.CS.model_handshake.CS.hs_keys
            CS.TrafficHandshake
            CS.ClientTraffic
            install.CS.install_material ==
          { model4.CS.model_handshake.CS.hs_keys with
              CS.ks_client_handshake_traffic = Some install.CS.install_material })
      | CS.TrafficRead ->
        assert_norm (
          CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
          CS.ServerTraffic);
        assert_norm (
          CS.update_key_schedule_with_label
            model4.CS.model_handshake.CS.hs_keys
            CS.TrafficHandshake
            CS.ServerTraffic
            install.CS.install_material ==
          { model4.CS.model_handshake.CS.hs_keys with
              CS.ks_server_handshake_traffic = Some install.CS.install_material }))
   | _ ->
     assert (PNI.client_no_tail_handshake_traffic_install_event e4);
     assert False)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_post_first_install_direction_shape
  (model4 model5:CS.connection_model)
  (e4:CS.conn_event)
  : Lemma
     (requires
       model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
       Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
       Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
       model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
       model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
       model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
       model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
       PNI.client_no_tail_handshake_traffic_install_event e4 /\
       CS.step_model model4 e4 == Some model5)
     (ensures
       (client_no_tail_handshake_write_install_event e4 ==>
         Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
         None? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic) /\
       (client_no_tail_handshake_read_install_event e4 ==>
         None? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
         Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic))
=
  match e4 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
   assert (
     CS.step_model model4 e4 ==
     Some {
       model4 with
         CS.model_record = CS.install_record_keys model4.CS.model_record install;
         CS.model_handshake = {
           model4.CS.model_handshake with
             CS.hs_keys =
               CS.update_key_schedule_with_install
                 model4.CS.model_handshake.CS.hs_keys
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
          model4.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ClientTraffic
          install.CS.install_material ==
        { model4.CS.model_handshake.CS.hs_keys with
            CS.ks_client_handshake_traffic = Some install.CS.install_material })
    | CS.TrafficRead ->
      assert_norm (
        CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
        CS.ServerTraffic);
      assert_norm (
        CS.update_key_schedule_with_label
          model4.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ServerTraffic
          install.CS.install_material ==
        { model4.CS.model_handshake.CS.hs_keys with
            CS.ks_server_handshake_traffic = Some install.CS.install_material }))
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
   assert (role_install.CS.install_role == CS.ClientEndpoint);
   let install = role_install.CS.install_payload in
   assert (
     CS.step_model model4 e4 ==
     Some {
       model4 with
         CS.model_record =
           CS.install_record_keys_for_role
             role_install.CS.install_role
             model4.CS.model_record
             install;
         CS.model_handshake = {
           model4.CS.model_handshake with
             CS.hs_keys =
               CS.update_key_schedule_with_install_for_role
                 role_install.CS.install_role
                 model4.CS.model_handshake.CS.hs_keys
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
          model4.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ClientTraffic
          install.CS.install_material ==
        { model4.CS.model_handshake.CS.hs_keys with
            CS.ks_client_handshake_traffic = Some install.CS.install_material })
    | CS.TrafficRead ->
      assert_norm (
        CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
        CS.ServerTraffic);
      assert_norm (
        CS.update_key_schedule_with_label
          model4.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ServerTraffic
          install.CS.install_material ==
        { model4.CS.model_handshake.CS.hs_keys with
            CS.ks_server_handshake_traffic = Some install.CS.install_material }))
  | _ ->
   assert (PNI.client_no_tail_handshake_traffic_install_event e4);
   assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_duplicate_second_install_progress_rank
  (model5 model6:CS.connection_model)
  (e5:CS.conn_event)
  : Lemma
     (requires
       model5.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
       Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
       Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
       model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
       model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
       PNI.client_no_tail_handshake_traffic_install_event e5 /\
       CS.step_model model5 e5 == Some model6 /\
       ((Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
         None? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
         client_no_tail_handshake_write_install_event e5) \/
        (None? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
         Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
         client_no_tail_handshake_read_install_event e5)))
     (ensures PNI.client_application_progress_rank model6 == 11)
=
  match e5 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
   assert (
     CS.step_model model5 e5 ==
     Some {
       model5 with
         CS.model_record = CS.install_record_keys model5.CS.model_record install;
         CS.model_handshake = {
           model5.CS.model_handshake with
             CS.hs_keys =
               CS.update_key_schedule_with_install
                 model5.CS.model_handshake.CS.hs_keys
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
          model5.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ClientTraffic
          install.CS.install_material ==
        { model5.CS.model_handshake.CS.hs_keys with
            CS.ks_client_handshake_traffic = Some install.CS.install_material });
      assert (None? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
    | CS.TrafficRead ->
      assert_norm (
        CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
        CS.ServerTraffic);
      assert_norm (
        CS.update_key_schedule_with_label
          model5.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ServerTraffic
          install.CS.install_material ==
        { model5.CS.model_handshake.CS.hs_keys with
            CS.ks_server_handshake_traffic = Some install.CS.install_material });
      assert (None? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic))
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
   assert (role_install.CS.install_role == CS.ClientEndpoint);
   let install = role_install.CS.install_payload in
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
        CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
        CS.ClientTraffic);
      assert_norm (
        CS.update_key_schedule_with_label
          model5.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ClientTraffic
          install.CS.install_material ==
        { model5.CS.model_handshake.CS.hs_keys with
            CS.ks_client_handshake_traffic = Some install.CS.install_material });
      assert (None? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic)
    | CS.TrafficRead ->
      assert_norm (
        CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
        CS.ServerTraffic);
      assert_norm (
        CS.update_key_schedule_with_label
          model5.CS.model_handshake.CS.hs_keys
          CS.TrafficHandshake
          CS.ServerTraffic
          install.CS.install_material ==
        { model5.CS.model_handshake.CS.hs_keys with
            CS.ks_server_handshake_traffic = Some install.CS.install_material });
      assert (None? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic))
  | _ ->
   assert (PNI.client_no_tail_handshake_traffic_install_event e5);
   assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_second_write_install_model_shape
  (model5 model6:CS.connection_model)
  (e5:CS.conn_event)
  : Lemma
      (requires
        model5.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        PNI.client_no_tail_handshake_traffic_install_event e5 /\
        client_no_tail_handshake_write_install_event e5 /\
        CS.step_model model5 e5 == Some model6)
      (ensures
        model6.CS.model_config == model5.CS.model_config /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
=
  CSL.lemma_step_model_preserves_config model5 e5 model6;
  lemma_client_no_tail_handshake_write_install_event_cases e5;
  match e5 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (
      CS.step_model model5 e5 ==
      Some {
        model5 with
          CS.model_record = CS.install_record_keys model5.CS.model_record install;
          CS.model_handshake = {
            model5.CS.model_handshake with
              CS.hs_keys =
                CS.update_key_schedule_with_install
                  model5.CS.model_handshake.CS.hs_keys
                  install;
          };
      });
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficWrite);
    assert_norm (
      CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
      CS.ClientTraffic);
    assert_norm (
      CS.update_key_schedule_with_label
        model5.CS.model_handshake.CS.hs_keys
        CS.TrafficHandshake
        CS.ClientTraffic
        install.CS.install_material ==
      { model5.CS.model_handshake.CS.hs_keys with
          CS.ks_client_handshake_traffic = Some install.CS.install_material })
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
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
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficWrite);
    assert_norm (
      CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficWrite ==
      CS.ClientTraffic);
    assert_norm (
      CS.update_key_schedule_with_label
        model5.CS.model_handshake.CS.hs_keys
        CS.TrafficHandshake
        CS.ClientTraffic
        install.CS.install_material ==
      { model5.CS.model_handshake.CS.hs_keys with
          CS.ks_client_handshake_traffic = Some install.CS.install_material })
  | _ ->
    assert False

let lemma_client_second_read_install_model_shape
  (model5 model6:CS.connection_model)
  (e5:CS.conn_event)
  : Lemma
      (requires
        model5.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model5.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        PNI.client_no_tail_handshake_traffic_install_event e5 /\
        client_no_tail_handshake_read_install_event e5 /\
        CS.step_model model5 e5 == Some model6)
      (ensures
        model6.CS.model_config == model5.CS.model_config /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
=
  CSL.lemma_step_model_preserves_config model5 e5 model6;
  lemma_client_no_tail_handshake_read_install_event_cases e5;
  match e5 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (
      CS.step_model model5 e5 ==
      Some {
        model5 with
          CS.model_record = CS.install_record_keys model5.CS.model_record install;
          CS.model_handshake = {
            model5.CS.model_handshake with
              CS.hs_keys =
                CS.update_key_schedule_with_install
                  model5.CS.model_handshake.CS.hs_keys
                  install;
          };
      });
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficRead);
    assert_norm (
      CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
      CS.ServerTraffic);
    assert_norm (
      CS.update_key_schedule_with_label
        model5.CS.model_handshake.CS.hs_keys
        CS.TrafficHandshake
        CS.ServerTraffic
        install.CS.install_material ==
      { model5.CS.model_handshake.CS.hs_keys with
          CS.ks_server_handshake_traffic = Some install.CS.install_material })
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
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
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficRead);
    assert_norm (
      CS.traffic_label_for_endpoint_direction CS.ClientEndpoint CS.TrafficRead ==
      CS.ServerTraffic);
    assert_norm (
      CS.update_key_schedule_with_label
        model5.CS.model_handshake.CS.hs_keys
        CS.TrafficHandshake
        CS.ServerTraffic
        install.CS.install_material ==
      { model5.CS.model_handshake.CS.hs_keys with
          CS.ks_server_handshake_traffic = Some install.CS.install_material })
  | _ ->
    assert False

let lemma_client_two_handshake_install_cover_model_shape
  (model4 model5 model6:CS.connection_model)
  (e4 e5:CS.conn_event)
  : Lemma
      (requires
        model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        PNI.client_no_tail_handshake_traffic_install_event e4 /\
        PNI.client_no_tail_handshake_traffic_install_event e5 /\
        client_no_tail_two_handshake_install_cover e4 e5 /\
        CS.step_model model4 e4 == Some model5 /\
        CS.step_model model5 e5 == Some model6)
      (ensures
        model6.CS.model_config == model4.CS.model_config /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
=
  lemma_client_post_first_install_model_shape model4 model5 e4;
  lemma_client_post_first_install_direction_shape model4 model5 e4;
  lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  if client_no_tail_handshake_write_install_event e4 then (
    assert (client_no_tail_handshake_read_install_event e5);
    assert (Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    assert (None? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    lemma_client_second_read_install_model_shape model5 model6 e5
  ) else (
    assert (client_no_tail_handshake_read_install_event e4);
    assert (client_no_tail_handshake_write_install_event e5);
    assert (None? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
    assert (Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
    lemma_client_second_write_install_model_shape model5 model6 e5
  );
  assert (model5.CS.model_config == model4.CS.model_config);
  assert (model6.CS.model_config == model5.CS.model_config)
#pop-options

(**
  The order-insensitive milestone: after the mandatory prefix, [e4] and [e5]
  are both clean client handshake-traffic install events.
**)
#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_fifth_and_sixth_events_handshake_traffic_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 rest.
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
            rest /\
          PNI.client_no_tail_handshake_traffic_install_event e4 /\
          PNI.client_no_tail_handshake_traffic_install_event e5)
=
  PNI.lemma_client_no_tail_model4_witness client;
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
    exists start ch sh client_shared e4 e5 rest.
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
        rest /\
      PNI.client_no_tail_handshake_traffic_install_event e4 /\
      PNI.client_no_tail_handshake_traffic_install_event e5
  with _.
  (
    PNI.lemma_client_post_derive_next_event_handshake_traffic_install
      model4
      e4
      rest
      tail_sent
      tail_received
      client.CS.cs_model;
    assert (PNI.client_no_tail_handshake_traffic_install_event e4);
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
      exists start ch sh client_shared e4 e5 rest.
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
          rest /\
        PNI.client_no_tail_handshake_traffic_install_event e4 /\
        PNI.client_no_tail_handshake_traffic_install_event e5
    with _.
    (
      lemma_client_post_first_install_model_shape model4 model5 e4;
      assert (
        Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic <==>
        None? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
      assert (FStar.List.Tot.length rest == 11);
      (match rest with
       | e5 :: rest2 ->
         assert (FStar.List.Tot.length rest2 == 10);
         lemma_client_post_first_install_next_event_handshake_traffic_install
           model5
           e5
           rest2
           tail_sent2
           tail_received2
           client.CS.cs_model;
         assert (PNI.client_no_tail_handshake_traffic_install_event e5)
      )
    )
  )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_no_tail_fifth_and_sixth_events_handshake_install_cover_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 rest.
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
            rest /\
          client_no_tail_two_handshake_install_cover e4 e5)
=
  PNI.lemma_client_no_tail_model4_witness client;
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
    exists start ch sh client_shared e4 e5 rest.
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
        rest /\
      client_no_tail_two_handshake_install_cover e4 e5
  with _.
  (
    PNI.lemma_client_post_derive_next_event_handshake_traffic_install
      model4
      e4
      rest
      tail_sent
      tail_received
      client.CS.cs_model;
    assert (PNI.client_no_tail_handshake_traffic_install_event e4);
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
      exists start ch sh client_shared e4 e5 rest.
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
          rest /\
        client_no_tail_two_handshake_install_cover e4 e5
    with _.
    (
      lemma_client_post_first_install_model_shape model4 model5 e4;
      lemma_client_post_first_install_direction_shape model4 model5 e4;
      assert (FStar.List.Tot.length rest == 11);
      match rest with
      | e5 :: rest2 ->
        assert (FStar.List.Tot.length rest2 == 10);
        lemma_client_post_first_install_next_event_handshake_traffic_install
          model5
          e5
          rest2
          tail_sent2
          tail_received2
          client.CS.cs_model;
        assert (PNI.client_no_tail_handshake_traffic_install_event e5);
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
          exists start ch sh client_shared e4 e5 rest.
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
              rest /\
            client_no_tail_two_handshake_install_cover e4 e5
        with _.
        (
          let e4_write = client_no_tail_handshake_write_install_event e4 in
          let e4_read = client_no_tail_handshake_read_install_event e4 in
          let e5_write = client_no_tail_handshake_write_install_event e5 in
          let e5_read = client_no_tail_handshake_read_install_event e5 in
          lemma_client_no_tail_handshake_install_event_direction_cases e4;
          lemma_client_no_tail_handshake_install_event_direction_cases e5;
          assert (e4_write \/ e4_read);
          assert (e5_write \/ e5_read);
          if e4_write /\ e5_write then (
            assert (Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
            assert (None? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
            lemma_client_duplicate_second_install_progress_rank model5 model6 e5;
            PNI.lemma_client_application_progress_rank_replay_lower_bound
              model6
              rest2
              tail_sent3
              tail_received3
              client.CS.cs_model;
            assert False
          );
          if e4_read /\ e5_read then (
            assert (None? model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
            assert (Some? model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
            lemma_client_duplicate_second_install_progress_rank model5 model6 e5;
            PNI.lemma_client_application_progress_rank_replay_lower_bound
              model6
              rest2
              tail_sent3
              tail_received3
              client.CS.cs_model;
            assert False
          );
          assert (client_no_tail_two_handshake_install_cover e4 e5);
          introduce exists (start':CS.handshake_start)
            (ch':GCH.clientHello)
            (sh':GSH.serverHello)
            (client_shared':C.x25519_shared_secret)
            (e4':CS.conn_event)
            (e5':CS.conn_event)
            (rest':list CS.conn_event).
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
            client_no_tail_two_handshake_install_cover e4' e5'
          with start ch sh client_shared e4 e5 rest2 and ()
        )
    )
  )
#pop-options
