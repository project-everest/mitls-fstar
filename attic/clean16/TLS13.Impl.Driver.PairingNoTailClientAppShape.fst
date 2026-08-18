module TLS13.Impl.Driver.PairingNoTailClientAppShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedShape
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module X = TLS13.X509.Spec

let client_no_tail_application_write_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficApplication /\
    install.CS.install_direction == CS.TrafficWrite
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ClientEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | _ ->
    False

let client_no_tail_application_read_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficApplication /\
    install.CS.install_direction == CS.TrafficRead
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ClientEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | _ ->
    False

let client_no_tail_application_install_event
  (ev:CS.conn_event)
  : prop =
  client_no_tail_application_write_install_event ev \/
  client_no_tail_application_read_install_event ev

let client_no_tail_application_install_cover
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : prop =
  (client_no_tail_application_write_install_event e13 /\
   client_no_tail_application_read_install_event e14) \/
  (client_no_tail_application_read_install_event e13 /\
   client_no_tail_application_write_install_event e14)

let lemma_client_no_tail_application_write_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_write_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficApplication /\
          install.CS.install_direction == CS.TrafficWrite
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
        | _ ->
          False))
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> ()
  | _ -> assert False

let lemma_client_no_tail_application_read_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_read_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficApplication /\
          install.CS.install_direction == CS.TrafficRead
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficApplication /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
        | _ ->
          False))
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> ()
  | _ -> assert False

let lemma_client_no_tail_application_install_event_direction_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_install_event ev)
      (ensures
        client_no_tail_application_write_install_event ev \/
        client_no_tail_application_read_install_event ev)
=
  ()

let lemma_client_no_tail_application_install_cover_cases
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : Lemma
      (requires client_no_tail_application_install_cover e13 e14)
      (ensures
        (client_no_tail_application_write_install_event e13 /\
         client_no_tail_application_read_install_event e14) \/
        (client_no_tail_application_read_install_event e13 /\
         client_no_tail_application_write_install_event e14))
=
  ()

let lemma_client_no_tail_application_write_read_events_disjoint
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_write_install_event ev /\
        client_no_tail_application_read_install_event ev)
      (ensures False)
=
  lemma_client_no_tail_application_write_install_event_cases ev;
  lemma_client_no_tail_application_read_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (install.CS.install_direction == CS.TrafficWrite);
    assert (install.CS.install_direction == CS.TrafficRead)
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite);
    assert (role_install.CS.install_payload.CS.install_direction == CS.TrafficRead)
  | _ ->
    assert False

let lemma_client_no_tail_application_install_cover_write_first
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_install_cover e13 e14 /\
        client_no_tail_application_write_install_event e13)
      (ensures client_no_tail_application_read_install_event e14)
=
  lemma_client_no_tail_application_install_cover_cases e13 e14;
  if client_no_tail_application_read_install_event e13 then (
    lemma_client_no_tail_application_write_read_events_disjoint e13;
    assert False
  );
  assert (client_no_tail_application_read_install_event e14)

let lemma_client_no_tail_application_install_cover_read_first
  (e13:CS.conn_event)
  (e14:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_install_cover e13 e14 /\
        client_no_tail_application_read_install_event e13)
      (ensures client_no_tail_application_write_install_event e14)
=
  lemma_client_no_tail_application_install_cover_cases e13 e14;
  if client_no_tail_application_write_install_event e13 then (
    lemma_client_no_tail_application_write_read_events_disjoint e13;
    assert False
  );
  assert (client_no_tail_application_write_install_event e14)

let lemma_client_no_tail_application_write_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_write_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              })) == Some model1)
=
  lemma_client_no_tail_application_write_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (install.CS.install_epoch == CS.TrafficApplication);
    assert (install.CS.install_direction == CS.TrafficWrite);
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    assert (install.CS.install_epoch == CS.TrafficApplication);
    assert (install.CS.install_direction == CS.TrafficWrite);
    assert_norm (
      CS.step_model model ev ==
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = install.CS.install_material;
          })));
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | _ ->
    assert False

let lemma_client_no_tail_application_read_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_application_read_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              })) == Some model1)
=
  lemma_client_no_tail_application_read_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    assert (install.CS.install_epoch == CS.TrafficApplication);
    assert (install.CS.install_direction == CS.TrafficRead);
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    assert (install.CS.install_epoch == CS.TrafficApplication);
    assert (install.CS.install_direction == CS.TrafficRead);
    assert_norm (
      CS.step_model model ev ==
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = install.CS.install_material;
          })));
    introduce exists (material:CS.traffic_key_material).
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          })) == Some model1
    with install.CS.install_material and ()
  | _ ->
    assert False

noextract
let client_after_one_application_install_model
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
  ((Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
    model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None) \/
   (model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
    Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic))

noextract
let client_after_application_installs_model
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
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic

let lemma_client_after_one_application_install_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_one_application_install_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        (((Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic) /\
          model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None) \/
         (model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
          Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)))
=
  ()

let lemma_client_after_application_installs_model_facts
  (model:CS.connection_model)
  : Lemma
      (requires client_after_application_installs_model model)
      (ensures
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
=
  ()

let lemma_client_after_server_finished_verified_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires PNTCFS.client_after_server_finished_verified_model model)
      (ensures PNI.client_application_progress_rank model == 3)
=
  PNTCFS.lemma_client_after_server_finished_verified_model_facts model;
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    ()
  | _ ->
    assert False

let lemma_client_after_one_application_install_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_one_application_install_model model)
      (ensures PNI.client_application_progress_rank model == 2)
=
  lemma_client_after_one_application_install_model_facts model;
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    ()
  | _ ->
    assert False

let lemma_client_after_application_installs_progress_rank
  (model:CS.connection_model)
  : Lemma
      (requires client_after_application_installs_model model)
      (ensures PNI.client_application_progress_rank model == 1)
=
  lemma_client_after_application_installs_model_facts model;
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    ()
  | _ ->
    assert False

#push-options "--z3rlimit 10"
let lemma_client_first_application_install_step_model_shape
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        PNTCFS.client_after_server_finished_verified_model model /\
        client_no_tail_application_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        client_after_one_application_install_model model1 /\
        (client_no_tail_application_write_install_event ev ==>
          (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
           model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)) /\
        (client_no_tail_application_read_install_event ev ==>
          (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
           Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)))
=
  PNTCFS.lemma_client_after_server_finished_verified_model_facts model;
  lemma_client_no_tail_application_install_event_direction_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert False
     | CS.TrafficApplication ->
       (match install.CS.install_direction with
        | CS.TrafficWrite ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys model.CS.model_record install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
        | CS.TrafficRead ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys model.CS.model_record install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)))
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert False
     | CS.TrafficApplication ->
       (match install.CS.install_direction with
        | CS.TrafficWrite ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys_for_role
                    role_install.CS.install_role
                    model.CS.model_record
                    install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install_for_role
                          role_install.CS.install_role
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
        | CS.TrafficRead ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys_for_role
                    role_install.CS.install_role
                    model.CS.model_record
                    install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install_for_role
                          role_install.CS.install_role
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)))
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_application_install_cover_step_model_shape
  (model13 model14 model15:CS.connection_model)
  (e13 e14:CS.conn_event)
  : Lemma
      (requires
        PNTCFS.client_after_server_finished_verified_model model13 /\
        client_no_tail_application_install_cover e13 e14 /\
        CS.step_model model13 e13 == Some model14 /\
        CS.step_model model14 e14 == Some model15)
      (ensures client_after_application_installs_model model15)
=
  lemma_client_no_tail_application_install_cover_cases e13 e14;
  if client_no_tail_application_write_install_event e13 then (
    lemma_client_no_tail_application_write_install_event_cases e13;
    lemma_client_no_tail_application_read_install_event_cases e14;
    lemma_client_first_application_install_step_model_shape model13 model14 e13;
    assert (Some? model14.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
    assert (model14.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
    match e14 with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficRead);
      assert_norm (
        CS.step_model model14 e14 ==
        Some {
          model14 with
            CS.model_record =
              CS.install_record_keys model14.CS.model_record install;
            CS.model_handshake =
              { model14.CS.model_handshake with
                  CS.hs_keys =
                    CS.update_key_schedule_with_install
                      model14.CS.model_handshake.CS.hs_keys
                      install;
              };
        });
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      assert (role_install.CS.install_role == CS.ClientEndpoint);
      let install = role_install.CS.install_payload in
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficRead);
      assert_norm (
        CS.step_model model14 e14 ==
        Some {
          model14 with
            CS.model_record =
              CS.install_record_keys_for_role
                role_install.CS.install_role
                model14.CS.model_record
                install;
            CS.model_handshake =
              { model14.CS.model_handshake with
                  CS.hs_keys =
                    CS.update_key_schedule_with_install_for_role
                      role_install.CS.install_role
                      model14.CS.model_handshake.CS.hs_keys
                      install;
              };
        });
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | _ ->
      assert False
  )
  else (
    assert (client_no_tail_application_read_install_event e13);
    assert (client_no_tail_application_write_install_event e14);
    lemma_client_no_tail_application_read_install_event_cases e13;
    lemma_client_no_tail_application_write_install_event_cases e14;
    lemma_client_first_application_install_step_model_shape model13 model14 e13;
    assert (model14.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
    assert (Some? model14.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
    match e14 with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficWrite);
      assert_norm (
        CS.step_model model14 e14 ==
        Some {
          model14 with
            CS.model_record =
              CS.install_record_keys model14.CS.model_record install;
            CS.model_handshake =
              { model14.CS.model_handshake with
                  CS.hs_keys =
                    CS.update_key_schedule_with_install
                      model14.CS.model_handshake.CS.hs_keys
                      install;
              };
        });
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      assert (role_install.CS.install_role == CS.ClientEndpoint);
      let install = role_install.CS.install_payload in
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficWrite);
      assert_norm (
        CS.step_model model14 e14 ==
        Some {
          model14 with
            CS.model_record =
              CS.install_record_keys_for_role
                role_install.CS.install_role
                model14.CS.model_record
                install;
            CS.model_handshake =
              { model14.CS.model_handshake with
                  CS.hs_keys =
                    CS.update_key_schedule_with_install_for_role
                      role_install.CS.install_role
                      model14.CS.model_handshake.CS.hs_keys
                      install;
              };
        });
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
      assert (Some? model15.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
    | _ ->
      assert False
  )
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_duplicate_application_second_install_progress_rank
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_after_one_application_install_model model /\
        client_no_tail_application_install_event ev /\
        CS.step_model model ev == Some model1 /\
        (((Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic) /\
          model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
          client_no_tail_application_write_install_event ev) \/
         (model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
          Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
          client_no_tail_application_read_install_event ev)))
      (ensures
        model1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        PNI.client_application_progress_rank model1 == 2)
=
  lemma_client_after_one_application_install_model_facts model;
  lemma_client_no_tail_application_install_event_direction_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert False
     | CS.TrafficApplication ->
       (match install.CS.install_direction with
        | CS.TrafficWrite ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys model.CS.model_record install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
          assert (client_after_one_application_install_model model1);
          lemma_client_after_one_application_install_progress_rank model1
        | CS.TrafficRead ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys model.CS.model_record install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
          assert (client_after_one_application_install_model model1);
          lemma_client_after_one_application_install_progress_rank model1))
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert False
     | CS.TrafficApplication ->
       (match install.CS.install_direction with
        | CS.TrafficWrite ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys_for_role
                    role_install.CS.install_role
                    model.CS.model_record
                    install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install_for_role
                          role_install.CS.install_role
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
          assert (client_after_one_application_install_model model1);
          lemma_client_after_one_application_install_progress_rank model1
        | CS.TrafficRead ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys_for_role
                    role_install.CS.install_role
                    model.CS.model_record
                    install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install_for_role
                          role_install.CS.install_role
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
          assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
          assert (client_after_one_application_install_model model1);
          lemma_client_after_one_application_install_progress_rank model1))
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_after_application_installs_extra_install_progress_rank
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_after_application_installs_model model /\
        client_no_tail_application_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        model1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        PNI.client_application_progress_rank model1 == 1)
=
  lemma_client_after_application_installs_model_facts model;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert False
     | CS.TrafficApplication ->
       (match install.CS.install_direction with
        | CS.TrafficWrite
        | CS.TrafficRead ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys model.CS.model_record install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (client_after_application_installs_model model1);
          lemma_client_after_application_installs_progress_rank model1))
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    assert (role_install.CS.install_role == CS.ClientEndpoint);
    let install = role_install.CS.install_payload in
    (match install.CS.install_epoch with
     | CS.TrafficHandshake ->
       assert False
     | CS.TrafficApplication ->
       (match install.CS.install_direction with
        | CS.TrafficWrite
        | CS.TrafficRead ->
          assert_norm (
            CS.step_model model ev ==
            Some {
              model with
                CS.model_record =
                  CS.install_record_keys_for_role
                    role_install.CS.install_role
                    model.CS.model_record
                    install;
                CS.model_handshake =
                  { model.CS.model_handshake with
                      CS.hs_keys =
                        CS.update_key_schedule_with_install_for_role
                          role_install.CS.install_role
                          model.CS.model_handshake.CS.hs_keys
                          install;
                  };
            });
          assert (client_after_application_installs_model model1);
          lemma_client_after_application_installs_progress_rank model1))
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_after_server_finished_verified_next_event_application_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        PNTCFS.client_after_server_finished_verified_model model /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 2)
      (ensures client_no_tail_application_install_event ev)
=
  PNTCFS.lemma_client_after_server_finished_verified_model_facts model;
  lemma_client_after_server_finished_verified_progress_rank model;
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
         assert (CS.traffic_install_allowed_at_stage CS.HsServerFinishedVerified install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication ->
            (match install.CS.install_direction with
             | CS.TrafficWrite -> ()
             | CS.TrafficRead -> ()))
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsServerFinishedVerified
           role_install.CS.install_payload);
         (match role_install.CS.install_payload.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication ->
            (match role_install.CS.install_payload.CS.install_direction with
             | CS.TrafficWrite -> ()
             | CS.TrafficRead -> ()))
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
         assert (PNI.client_application_progress_rank model1 == 3);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (3 <= 2);
         assert False
       | M.TlsHandshake _
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_after_one_application_install_next_event_application_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_one_application_install_model model /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 1)
      (ensures client_no_tail_application_install_event ev)
=
  lemma_client_after_one_application_install_model_facts model;
  lemma_client_after_one_application_install_progress_rank model;
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
         assert (CS.traffic_install_allowed_at_stage CS.HsServerFinishedVerified install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication ->
            (match install.CS.install_direction with
             | CS.TrafficWrite -> ()
             | CS.TrafficRead -> ()))
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsServerFinishedVerified
           role_install.CS.install_payload);
         (match role_install.CS.install_payload.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication ->
            (match role_install.CS.install_payload.CS.install_direction with
             | CS.TrafficWrite -> ()
             | CS.TrafficRead -> ()))
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
         assert (PNI.client_application_progress_rank model1 == 2);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (2 <= 1);
         assert False
       | M.TlsHandshake _
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_after_application_installs_next_event_client_finished
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        client_after_application_installs_model model /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNI.client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 0)
      (ensures
        exists cf.
          ev == CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished cf);
          })
=
  lemma_client_after_application_installs_model_facts model;
  lemma_client_after_application_installs_progress_rank model;
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
         assert (CS.traffic_install_allowed_at_stage CS.HsServerFinishedVerified install);
         (match install.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication ->
            (match install.CS.install_direction with
             | CS.TrafficWrite
             | CS.TrafficRead ->
               lemma_client_after_application_installs_extra_install_progress_rank
                 model
                 model1
                 ev;
               PNI.lemma_client_application_progress_rank_replay_lower_bound
                 model1
                 rest
                 tail_sent
                 tail_received
                 final_model;
               assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
               assert (1 <= 0);
               assert False))
       | CS.LocalInstallTrafficKeysForRole role_install ->
         assert (CS.legal_local_event model local);
         assert (role_install.CS.install_role == CS.ClientEndpoint);
         assert (CS.traffic_install_allowed_at_stage_for_role
           CS.ClientEndpoint
           CS.HsServerFinishedVerified
           role_install.CS.install_payload);
         (match role_install.CS.install_payload.CS.install_epoch with
          | CS.TrafficHandshake -> assert False
          | CS.TrafficApplication ->
            (match role_install.CS.install_payload.CS.install_direction with
             | CS.TrafficWrite
             | CS.TrafficRead ->
               lemma_client_after_application_installs_extra_install_progress_rank
                 model
                 model1
                 ev;
               PNI.lemma_client_application_progress_rank_replay_lower_bound
                 model1
                 rest
                 tail_sent
                 tail_received
                 final_model;
               assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
               assert (1 <= 0);
               assert False))
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
         assert (PNI.client_application_progress_rank model1 == 1);
         assert (PNI.client_application_progress_rank model1 <= FStar.List.Tot.length rest);
         assert (1 <= 0);
         assert False
       | M.TlsHandshake (M.Finished cf) ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         (match msg.CL.message_direction with
          | CL.Sent ->
            introduce exists (cf':GFin.finished).
              ev == CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf');
              }
            with cf and ()
          | CL.Received ->
            assert False)
       | M.TlsHandshake _
       | M.TlsApplicationData _
       | M.TlsIgnoredPostHandshake _
       | M.TlsKeyUpdate _ ->
         assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
         assert False)
  )
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_no_tail_model15_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest11 model15 tail_sent tail_received.
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
            rest11 /\
          FStar.List.Tot.length rest11 == 1 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_no_tail_application_install_cover e13 e14 /\
          client_after_application_installs_model model15 /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
            model15
            rest11
            tail_sent
            tail_received
            client.CS.cs_model /\
          PNI.client_application_progress_rank client.CS.cs_model == 0)
=
  PNTCFS.lemma_client_no_tail_model13_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf rest9 model13 tail_sent tail_received.
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
    PNTCFS.client_after_server_finished_verified_model model13 /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      model13
      rest9
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  with
  (
    match rest9 with
    | e13 :: rest10 ->
      assert (FStar.List.Tot.length rest10 == 2);
      lemma_client_after_server_finished_verified_next_event_application_install
        model13
        e13
        rest10
        tail_sent
        tail_received
        client.CS.cs_model;
      assert (client_no_tail_application_install_event e13);
      assert_norm (
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model13 (e13 :: rest10) tail_sent tail_received client.CS.cs_model ==
        (exists model14 delta_sent delta_received tail_sent2 tail_received2.
          CS.legal_event model13 e13 /\
          CS.step_model model13 e13 == Some model14 /\
          CS.event_raw_delta_legal model13 e13 delta_sent delta_received /\
          Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
          Seq.equal tail_received (B.append delta_received tail_received2) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model14 rest10 tail_sent2 tail_received2 client.CS.cs_model));
      eliminate exists model14 delta_sent delta_received tail_sent2 tail_received2.
        CS.legal_event model13 e13 /\
        CS.step_model model13 e13 == Some model14 /\
        CS.event_raw_delta_legal model13 e13 delta_sent delta_received /\
        Seq.equal tail_sent (B.append delta_sent tail_sent2) /\
        Seq.equal tail_received (B.append delta_received tail_received2) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model14 rest10 tail_sent2 tail_received2 client.CS.cs_model
      with
      (
        lemma_client_first_application_install_step_model_shape model13 model14 e13;
        assert (client_after_one_application_install_model model14);
        match rest10 with
        | e14 :: rest11 ->
          assert (FStar.List.Tot.length rest11 == 1);
          lemma_client_after_one_application_install_next_event_application_install
            model14
            e14
            rest11
            tail_sent2
            tail_received2
            client.CS.cs_model;
          assert (client_no_tail_application_install_event e14);
          assert_norm (
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model14 (e14 :: rest11) tail_sent2 tail_received2 client.CS.cs_model ==
            (exists model15 delta_sent2 delta_received2 tail_sent3 tail_received3.
              CS.legal_event model14 e14 /\
              CS.step_model model14 e14 == Some model15 /\
              CS.event_raw_delta_legal model14 e14 delta_sent2 delta_received2 /\
              Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
              Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model15 rest11 tail_sent3 tail_received3 client.CS.cs_model));
          eliminate exists model15 delta_sent2 delta_received2 tail_sent3 tail_received3.
            CS.legal_event model14 e14 /\
            CS.step_model model14 e14 == Some model15 /\
            CS.event_raw_delta_legal model14 e14 delta_sent2 delta_received2 /\
            Seq.equal tail_sent2 (B.append delta_sent2 tail_sent3) /\
            Seq.equal tail_received2 (B.append delta_received2 tail_received3) /\
            TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model15 rest11 tail_sent3 tail_received3 client.CS.cs_model
          with
          (
            let e13_write = client_no_tail_application_write_install_event e13 in
            let e13_read = client_no_tail_application_read_install_event e13 in
            let e14_write = client_no_tail_application_write_install_event e14 in
            let e14_read = client_no_tail_application_read_install_event e14 in
            lemma_client_no_tail_application_install_event_direction_cases e13;
            lemma_client_no_tail_application_install_event_direction_cases e14;
            assert (e13_write \/ e13_read);
            assert (e14_write \/ e14_read);
            if e13_write then (
              assert (Some? model14.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic);
              assert (model14.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
              if e14_write then (
                lemma_client_duplicate_application_second_install_progress_rank model14 model15 e14;
                PNI.lemma_client_application_progress_rank_replay_lower_bound
                  model15
                  rest11
                  tail_sent3
                  tail_received3
                  client.CS.cs_model;
                assert (PNI.client_application_progress_rank model15 <= FStar.List.Tot.length rest11);
                assert (2 <= 1);
                assert False
              );
              assert (e14_read);
              assert (client_no_tail_application_install_cover e13 e14)
            )
            else (
              assert (e13_read);
              assert (model14.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
              assert (Some? model14.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
              if e14_read then (
                lemma_client_duplicate_application_second_install_progress_rank model14 model15 e14;
                PNI.lemma_client_application_progress_rank_replay_lower_bound
                  model15
                  rest11
                  tail_sent3
                  tail_received3
                  client.CS.cs_model;
                assert (PNI.client_application_progress_rank model15 <= FStar.List.Tot.length rest11);
                assert (2 <= 1);
                assert False
              );
              assert (e14_write);
              assert (client_no_tail_application_install_cover e13 e14)
            );
            assert (client_no_tail_application_install_cover e13 e14);
            lemma_client_application_install_cover_step_model_shape model13 model14 model15 e13 e14;
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
              (sf0:GFin.finished)
              (e130:CS.conn_event)
              (e140:CS.conn_event)
              (rest110:list CS.conn_event)
              (model150:CS.connection_model)
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
                e130 ::
                e140 ::
                rest110 /\
              FStar.List.Tot.length rest110 == 1 /\
              PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
              client_no_tail_application_install_cover e130 e140 /\
              client_after_application_installs_model model150 /\
              TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
                model150
                rest110
                tail_sent0
                tail_received0
                client.CS.cs_model /\
              PNI.client_application_progress_rank client.CS.cs_model == 0
            with start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest11 model15 tail_sent3 tail_received3 and ()
          )
      )
  )
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_no_tail_fourteenth_and_fifteenth_events_application_install_cover_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_application_installs_shape client)
=
  lemma_client_no_tail_model15_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest11 model15 tail_sent tail_received.
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
      rest11 /\
    FStar.List.Tot.length rest11 == 1 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_no_tail_application_install_cover e13 e14 /\
    client_after_application_installs_model model15 /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      model15
      rest11
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  with
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
      (sf0:GFin.finished)
      (e130:CS.conn_event)
      (e140:CS.conn_event)
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
        e130 ::
        e140 ::
        rest0 /\
      FStar.List.Tot.length rest0 == 1 /\
      PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
      client_no_tail_application_install_cover e130 e140
    with start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest11 and ()
  )
#pop-options

#push-options "--z3rlimit 10"
let lemma_client_no_tail_sixteenth_event_client_finished_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_finished_sent_shape client)
=
  lemma_client_no_tail_model15_witness client;
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 rest11 model15 tail_sent tail_received.
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
      rest11 /\
    FStar.List.Tot.length rest11 == 1 /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    client_no_tail_application_install_cover e13 e14 /\
    client_after_application_installs_model model15 /\
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
      model15
      rest11
      tail_sent
      tail_received
      client.CS.cs_model /\
    PNI.client_application_progress_rank client.CS.cs_model == 0
  with
  (
    match rest11 with
    | e15 :: rest12 ->
      assert (FStar.List.Tot.length rest12 == 0);
      lemma_client_after_application_installs_next_event_client_finished
        model15
        e15
        rest12
        tail_sent
        tail_received
        client.CS.cs_model;
      eliminate exists cf.
        e15 == CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        }
      with
      (
        match rest12 with
        | [] ->
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
            (sf0:GFin.finished)
            (e130:CS.conn_event)
            (e140:CS.conn_event)
            (cf0:GFin.finished).
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
              e130 ::
              e140 ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf0);
              }) ::
              [] /\
            PCPS.client_no_tail_two_handshake_install_cover e40 e50 /\
            client_no_tail_application_install_cover e130 e140
          with start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf and ()
        | _ :: _ ->
          assert False
      )
  )
#pop-options
