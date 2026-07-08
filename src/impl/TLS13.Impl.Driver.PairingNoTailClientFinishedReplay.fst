module TLS13.Impl.Driver.PairingNoTailClientFinishedReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module PWL = TLS13.ConnectionState.ProtectedWireBase
module ListP = FStar.List.Tot.Properties
module Seq = FStar.Seq
module Tac = FStar.Tactics
module T = TLS13.Types
module X = TLS13.X509.Spec

#push-options "--split_queries always --z3rlimit 10"

let lemma_application_install_event_sent_delta_empty
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        (PNTCAS.client_no_tail_application_write_install_event ev \/
         PNTCAS.client_no_tail_application_read_install_event ev) /\
        CS.event_raw_delta_legal model ev delta_sent delta_received)
      (ensures Seq.equal delta_sent B.empty)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ ->
    if PNTCAS.client_no_tail_application_write_install_event ev then (
      PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev;
      assert False
    ) else (
      PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev;
      assert False
    )

let lemma_application_install_event_deltas_empty
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        (PNTCAS.client_no_tail_application_write_install_event ev \/
         PNTCAS.client_no_tail_application_read_install_event ev) /\
        CS.event_raw_delta_legal model ev delta_sent delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        Seq.equal delta_received B.empty)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ ->
    if PNTCAS.client_no_tail_application_write_install_event ev then (
      PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev;
      assert False
    ) else (
      PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev;
      assert False
    )

let lemma_client_application_write_install_event_step_model_as_plain_legal
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_write_install_event ev /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.legal_event
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              })) /\
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              })) == Some model1)
=
  PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev;
  PNTCAS.lemma_client_no_tail_application_write_install_event_step_model_as_plain
    model
    model1
    ev;
  eliminate exists material.
    CS.step_model
      model
      (CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })) == Some model1
  returns
    exists material'.
      CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material';
          })) /\
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material';
          })) == Some model1
  with _.
  (
    match ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficWrite);
      assert (material == install.CS.install_material);
      assert (CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          })))
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      assert (role_install.CS.install_role == CS.ClientEndpoint);
      let install = role_install.CS.install_payload in
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficWrite);
      assert (material == install.CS.install_material);
      assert_norm (CS.legal_event model ev);
      assert_norm (CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          })))
    | _ ->
      assert False;
    introduce exists material'.
      CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material';
          })) /\
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material';
          })) == Some model1
    with material and ()
  )

let lemma_client_application_read_install_event_step_model_as_plain_legal
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_read_install_event ev /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.legal_event
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              })) /\
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              })) == Some model1)
=
  PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev;
  PNTCAS.lemma_client_no_tail_application_read_install_event_step_model_as_plain
    model
    model1
    ev;
  eliminate exists material.
    CS.step_model
      model
      (CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })) == Some model1
  returns
    exists material'.
      CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material';
          })) /\
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material';
          })) == Some model1
  with _.
  (
    match ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficRead);
      assert (material == install.CS.install_material);
      assert (CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          })))
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      assert (role_install.CS.install_role == CS.ClientEndpoint);
      let install = role_install.CS.install_payload in
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficRead);
      assert (material == install.CS.install_material);
      assert_norm (CS.legal_event model ev);
      assert_norm (CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          })))
    | _ ->
      assert False;
    introduce exists material'.
      CS.legal_event
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material';
          })) /\
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material';
          })) == Some model1
    with material and ()
  )

let lemma_client_application_install_cover_step_model_canonical_write_read
  (model0 model1 model2:CS.connection_model)
  (e0 e1:CS.conn_event)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e0 e1 /\
        CS.legal_event model0 e0 /\
        CS.legal_event model1 e1 /\
        CS.step_model model0 e0 == Some model1 /\
        CS.step_model model1 e1 == Some model2)
      (ensures
        exists
          (write_material:CS.traffic_key_material)
          (read_material:CS.traffic_key_material)
          (after_write:CS.connection_model).
          CS.legal_event
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material;
              })) /\
          CS.step_model
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material;
              })) == Some after_write /\
          CS.legal_event
            after_write
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material;
              })) /\
          CS.step_model
            after_write
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material;
              })) == Some model2)
=
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e0 e1;
  if PNTCAS.client_no_tail_application_write_install_event e0 then (
    PNTCAS.lemma_client_no_tail_application_install_cover_write_first e0 e1;
    assert (PNTCAS.client_no_tail_application_read_install_event e1);
    lemma_client_application_write_install_event_step_model_as_plain_legal
      model0
      model1
      e0;
    eliminate exists write_material.
      CS.legal_event
        model0
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = write_material;
          })) /\
      CS.step_model
        model0
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = write_material;
          })) == Some model1
    returns
      exists
        (write_material':CS.traffic_key_material)
        (read_material':CS.traffic_key_material)
        (after_write':CS.connection_model).
        CS.legal_event
          model0
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material';
            })) /\
        CS.step_model
          model0
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material';
            })) == Some after_write' /\
        CS.legal_event
          after_write'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material';
            })) /\
        CS.step_model
          after_write'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material';
            })) == Some model2
    with _.
    (
      lemma_client_application_read_install_event_step_model_as_plain_legal
        model1
        model2
        e1;
      eliminate exists read_material.
        CS.legal_event
          model1
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material;
            })) /\
        CS.step_model
          model1
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material;
            })) == Some model2
      returns
        exists
          (write_material':CS.traffic_key_material)
          (read_material':CS.traffic_key_material)
          (after_write':CS.connection_model).
          CS.legal_event
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              })) /\
          CS.step_model
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              })) == Some after_write' /\
          CS.legal_event
            after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              })) /\
          CS.step_model
            after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              })) == Some model2
      with _.
      (
        introduce exists
          (write_material':CS.traffic_key_material)
          (read_material':CS.traffic_key_material)
          (after_write':CS.connection_model).
          CS.legal_event
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              })) /\
          CS.step_model
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              })) == Some after_write' /\
          CS.legal_event
            after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              })) /\
          CS.step_model
            after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              })) == Some model2
        with write_material read_material model1 and ()
      )
    )
  )
  else (
    assert (PNTCAS.client_no_tail_application_read_install_event e0);
    PNTCAS.lemma_client_no_tail_application_install_cover_read_first e0 e1;
    assert (PNTCAS.client_no_tail_application_write_install_event e1);
    lemma_client_application_read_install_event_step_model_as_plain_legal
      model0
      model1
      e0;
    eliminate exists read_material.
      CS.legal_event
        model0
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = read_material;
          })) /\
      CS.step_model
        model0
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = read_material;
          })) == Some model1
    returns
      exists
        (write_material':CS.traffic_key_material)
        (read_material':CS.traffic_key_material)
        (after_write':CS.connection_model).
        CS.legal_event
          model0
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material';
            })) /\
        CS.step_model
          model0
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material';
            })) == Some after_write' /\
        CS.legal_event
          after_write'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material';
            })) /\
        CS.step_model
          after_write'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material';
            })) == Some model2
    with _.
    (
      lemma_client_application_write_install_event_step_model_as_plain_legal
        model1
        model2
        e1;
      eliminate exists write_material.
        CS.legal_event
          model1
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material;
            })) /\
        CS.step_model
          model1
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material;
            })) == Some model2
      returns
        exists
          (write_material':CS.traffic_key_material)
          (read_material':CS.traffic_key_material)
          (after_write':CS.connection_model).
          CS.legal_event
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              })) /\
          CS.step_model
            model0
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              })) == Some after_write' /\
          CS.legal_event
            after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              })) /\
          CS.step_model
            after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              })) == Some model2
      with _.
      (
        let write_ev =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material;
            }) in
        let read_ev =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material;
            }) in
        assert_norm (CS.legal_event model0 write_ev);
        match CS.step_model model0 write_ev with
        | Some after_write ->
          assert_norm (CS.legal_event after_write read_ev);
          assert_norm (CS.step_model after_write read_ev == Some model2);
          assert (CS.step_model after_write read_ev == Some model2);
          introduce exists
            (write_material':CS.traffic_key_material)
            (read_material':CS.traffic_key_material)
            (after_write':CS.connection_model).
            CS.legal_event
              model0
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material';
                })) /\
            CS.step_model
              model0
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material';
                })) == Some after_write' /\
            CS.legal_event
              after_write'
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material';
                })) /\
            CS.step_model
              after_write'
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material';
                })) == Some model2
          with write_material read_material after_write and ()
        | None ->
          assert False
      )
    )
  )

let lemma_client_finished_sent_seal_replay_canonicalize_application_installs
  (model12:CS.connection_model)
  (sf:M.finished)
  (e13 e14:CS.conn_event)
  (cf:M.finished)
  (suffix_sent:B.bytes)
  (suffix_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        CS.conn_events_sent_seal_replay
          model12
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
           e13 ::
           e14 ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf);
           }) ::
           [])
          suffix_sent
          suffix_received
          final_model /\
        client_finished_sent_seal_suffix_head_steps
          model12
          sf
          e13
          e14
          cf
          final_model)
      (ensures
        exists
          (after_verify:CS.connection_model)
          (after_app_write:CS.connection_model)
          (after_app_read:CS.connection_model)
          (client_app_write_material:CS.traffic_key_material)
          (client_app_read_material:CS.traffic_key_material).
          CS.conn_events_sent_seal_replay
            model12
            (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
             CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeys {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficWrite;
                 CS.install_material = client_app_write_material;
               }) ::
             CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeys {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficRead;
                 CS.install_material = client_app_read_material;
               }) ::
             CS.ConnNetworkEvent ({
               CL.message_direction = CL.Sent;
               CL.message_value = M.TlsHandshake (M.Finished cf);
             }) ::
             [])
            suffix_sent
            suffix_received
            final_model /\
          CS.step_model
            model12
            (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) ==
            Some after_verify /\
          CS.step_model
            after_verify
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = client_app_write_material;
              })) == Some after_app_write /\
          CS.step_model
            after_app_write
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = client_app_read_material;
              })) == Some after_app_read /\
          CS.step_model
            after_app_read
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf);
            })) == Some final_model)
=
  let verify_ev = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let sent_ev =
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished cf);
    }) in
  eliminate exists
    (after_verify:CS.connection_model)
    (after_e13:CS.connection_model)
    (after_e14:CS.connection_model).
    CS.step_model model12 verify_ev == Some after_verify /\
    CS.step_model after_verify e13 == Some after_e13 /\
    CS.step_model after_e13 e14 == Some after_e14 /\
    CS.step_model after_e14 sent_ev == Some final_model
  returns
    exists
      (after_verify':CS.connection_model)
      (after_app_write':CS.connection_model)
      (after_app_read':CS.connection_model)
      (client_app_write_material':CS.traffic_key_material)
      (client_app_read_material':CS.traffic_key_material).
      CS.conn_events_sent_seal_replay
        model12
        (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
         CS.ConnLocalEvent
           (CS.LocalInstallTrafficKeys {
             CS.install_epoch = CS.TrafficApplication;
             CS.install_direction = CS.TrafficWrite;
             CS.install_material = client_app_write_material';
           }) ::
         CS.ConnLocalEvent
           (CS.LocalInstallTrafficKeys {
             CS.install_epoch = CS.TrafficApplication;
             CS.install_direction = CS.TrafficRead;
             CS.install_material = client_app_read_material';
           }) ::
         sent_ev ::
         [])
        suffix_sent
        suffix_received
        final_model /\
      CS.step_model model12 verify_ev == Some after_verify' /\
      CS.step_model
        after_verify'
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_app_write_material';
          })) == Some after_app_write' /\
      CS.step_model
        after_app_write'
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_app_read_material';
          })) == Some after_app_read' /\
      CS.step_model after_app_read' sent_ev == Some final_model
  with _.
  (
    PWR.lemma_conn_events_sent_seal_replay_head
      model12
      verify_ev
      (e13 :: e14 :: sent_ev :: [])
      suffix_sent
      suffix_received
      final_model;
    eliminate exists
      (model1:CS.connection_model)
      delta0_sent
      delta0_received
      tail0_sent
      tail0_received.
      CS.legal_event model12 verify_ev /\
      CS.step_model model12 verify_ev == Some model1 /\
      CS.event_raw_delta_legal model12 verify_ev delta0_sent delta0_received /\
      CS.sent_event_nonempty_seal_projection model12 verify_ev delta0_sent /\
      Seq.equal suffix_sent (B.append delta0_sent tail0_sent) /\
      Seq.equal suffix_received (B.append delta0_received tail0_received) /\
      CS.conn_events_sent_seal_replay
        model1
        (e13 :: e14 :: sent_ev :: [])
        tail0_sent
        tail0_received
        final_model
    returns
      exists
        (after_verify':CS.connection_model)
        (after_app_write':CS.connection_model)
        (after_app_read':CS.connection_model)
        (client_app_write_material':CS.traffic_key_material)
        (client_app_read_material':CS.traffic_key_material).
        CS.conn_events_sent_seal_replay
          model12
          (verify_ev ::
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeys {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficWrite;
               CS.install_material = client_app_write_material';
             }) ::
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeys {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficRead;
               CS.install_material = client_app_read_material';
             }) ::
           sent_ev ::
           [])
          suffix_sent
          suffix_received
          final_model /\
        CS.step_model model12 verify_ev == Some after_verify' /\
        CS.step_model
          after_verify'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_app_write_material';
            })) == Some after_app_write' /\
        CS.step_model
          after_app_write'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_app_read_material';
            })) == Some after_app_read' /\
        CS.step_model after_app_read' sent_ev == Some final_model
    with _.
    (
      assert (model1 == after_verify);
      PWR.lemma_conn_events_sent_seal_replay_head
        model1
        e13
        (e14 :: sent_ev :: [])
        tail0_sent
        tail0_received
        final_model;
      eliminate exists
        (model2:CS.connection_model)
        delta1_sent
        delta1_received
        tail1_sent
        tail1_received.
        CS.legal_event model1 e13 /\
        CS.step_model model1 e13 == Some model2 /\
        CS.event_raw_delta_legal model1 e13 delta1_sent delta1_received /\
        CS.sent_event_nonempty_seal_projection model1 e13 delta1_sent /\
        Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
        Seq.equal tail0_received (B.append delta1_received tail1_received) /\
        CS.conn_events_sent_seal_replay
          model2
          (e14 :: sent_ev :: [])
          tail1_sent
          tail1_received
          final_model
      returns
        exists
          (after_verify':CS.connection_model)
          (after_app_write':CS.connection_model)
          (after_app_read':CS.connection_model)
          (client_app_write_material':CS.traffic_key_material)
          (client_app_read_material':CS.traffic_key_material).
          CS.conn_events_sent_seal_replay
            model12
            (verify_ev ::
             CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeys {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficWrite;
                 CS.install_material = client_app_write_material';
               }) ::
             CS.ConnLocalEvent
               (CS.LocalInstallTrafficKeys {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficRead;
                 CS.install_material = client_app_read_material';
               }) ::
             sent_ev ::
             [])
            suffix_sent
            suffix_received
            final_model /\
          CS.step_model model12 verify_ev == Some after_verify' /\
          CS.step_model
            after_verify'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = client_app_write_material';
              })) == Some after_app_write' /\
          CS.step_model
            after_app_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = client_app_read_material';
              })) == Some after_app_read' /\
          CS.step_model after_app_read' sent_ev == Some final_model
      with _.
      (
        assert (model2 == after_e13);
        PWR.lemma_conn_events_sent_seal_replay_head
          model2
          e14
          (sent_ev :: [])
          tail1_sent
          tail1_received
          final_model;
        eliminate exists
          (model3:CS.connection_model)
          delta2_sent
          delta2_received
          tail2_sent
          tail2_received.
          CS.legal_event model2 e14 /\
          CS.step_model model2 e14 == Some model3 /\
          CS.event_raw_delta_legal model2 e14 delta2_sent delta2_received /\
          CS.sent_event_nonempty_seal_projection model2 e14 delta2_sent /\
          Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
          Seq.equal tail1_received (B.append delta2_received tail2_received) /\
          CS.conn_events_sent_seal_replay
            model3
            (sent_ev :: [])
            tail2_sent
            tail2_received
            final_model
        returns
          exists
            (after_verify':CS.connection_model)
            (after_app_write':CS.connection_model)
            (after_app_read':CS.connection_model)
            (client_app_write_material':CS.traffic_key_material)
            (client_app_read_material':CS.traffic_key_material).
            CS.conn_events_sent_seal_replay
              model12
              (verify_ev ::
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeys {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = client_app_write_material';
                 }) ::
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeys {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = client_app_read_material';
                 }) ::
               sent_ev ::
               [])
              suffix_sent
              suffix_received
              final_model /\
            CS.step_model model12 verify_ev == Some after_verify' /\
            CS.step_model
              after_verify'
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = client_app_write_material';
                })) == Some after_app_write' /\
            CS.step_model
              after_app_write'
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = client_app_read_material';
                })) == Some after_app_read' /\
            CS.step_model after_app_read' sent_ev == Some final_model
        with _.
        (
          assert (model3 == after_e14);
          PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
          lemma_application_install_event_deltas_empty
            model1
            e13
            delta1_sent
            delta1_received;
          lemma_application_install_event_deltas_empty
            model2
            e14
            delta2_sent
            delta2_received;
          Seq.lemma_eq_elim delta1_sent B.empty;
          Seq.lemma_eq_elim delta1_received B.empty;
          Seq.lemma_eq_elim delta2_sent B.empty;
          Seq.lemma_eq_elim delta2_received B.empty;
          lemma_client_application_install_cover_step_model_canonical_write_read
            model1
            model2
            model3
            e13
            e14;
          eliminate exists
            (write_material:CS.traffic_key_material)
            (read_material:CS.traffic_key_material)
            (after_write:CS.connection_model).
            CS.legal_event
              model1
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                })) /\
            CS.step_model
              model1
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                })) == Some after_write /\
            CS.legal_event
              after_write
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                })) /\
            CS.step_model
              after_write
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                })) == Some model3
          returns
            exists
              (after_verify':CS.connection_model)
              (after_app_write':CS.connection_model)
              (after_app_read':CS.connection_model)
              (client_app_write_material':CS.traffic_key_material)
              (client_app_read_material':CS.traffic_key_material).
              CS.conn_events_sent_seal_replay
                model12
                (verify_ev ::
                 CS.ConnLocalEvent
                   (CS.LocalInstallTrafficKeys {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficWrite;
                     CS.install_material = client_app_write_material';
                   }) ::
                 CS.ConnLocalEvent
                   (CS.LocalInstallTrafficKeys {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficRead;
                     CS.install_material = client_app_read_material';
                   }) ::
                 sent_ev ::
                 [])
                suffix_sent
                suffix_received
                final_model /\
              CS.step_model model12 verify_ev == Some after_verify' /\
              CS.step_model
                after_verify'
                (CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeys {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = client_app_write_material';
                  })) == Some after_app_write' /\
              CS.step_model
                after_app_write'
                (CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeys {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = client_app_read_material';
                  })) == Some after_app_read' /\
              CS.step_model after_app_read' sent_ev == Some final_model
          with _.
          (
            let write_ev =
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                }) in
            let read_ev =
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                }) in
            assert_norm (CS.event_raw_delta_legal model1 write_ev delta1_sent delta1_received);
            assert_norm (CS.event_raw_delta_legal after_write read_ev delta2_sent delta2_received);
            assert_norm (CS.sent_event_nonempty_seal_projection model1 write_ev delta1_sent);
            assert_norm (CS.sent_event_nonempty_seal_projection after_write read_ev delta2_sent);
            assert (CS.step_model model3 sent_ev == Some final_model);
            assert (CS.conn_events_sent_seal_replay
              model3
              (sent_ev :: [])
              tail2_sent
              tail2_received
              final_model);
            assert (CS.legal_event after_write read_ev);
            assert (CS.step_model after_write read_ev == Some model3);
            assert (CS.event_raw_delta_legal
              after_write
              read_ev
              delta2_sent
              delta2_received);
            assert (CS.sent_event_nonempty_seal_projection
              after_write
              read_ev
              delta2_sent);
            assert (Seq.equal tail1_sent (B.append delta2_sent tail2_sent));
            assert (Seq.equal tail1_received
              (B.append delta2_received tail2_received));
            PWR.lemma_conn_events_sent_seal_replay_cons
              after_write
              read_ev
              (sent_ev :: [])
              tail1_sent
              tail1_received
              final_model
              model3
              delta2_sent
              delta2_received
              tail2_sent
              tail2_received;
            assert (CS.legal_event model1 write_ev);
            assert (CS.step_model model1 write_ev == Some after_write);
            assert (CS.event_raw_delta_legal
              model1
              write_ev
              delta1_sent
              delta1_received);
            assert (CS.sent_event_nonempty_seal_projection
              model1
              write_ev
              delta1_sent);
            assert (Seq.equal tail0_sent (B.append delta1_sent tail1_sent));
            assert (Seq.equal tail0_received
              (B.append delta1_received tail1_received));
            PWR.lemma_conn_events_sent_seal_replay_cons
              model1
              write_ev
              (read_ev :: sent_ev :: [])
              tail0_sent
              tail0_received
              final_model
              after_write
              delta1_sent
              delta1_received
              tail1_sent
              tail1_received;
            PWR.lemma_conn_events_sent_seal_replay_cons
              model12
              verify_ev
              (write_ev :: read_ev :: sent_ev :: [])
              suffix_sent
              suffix_received
              final_model
              model1
              delta0_sent
              delta0_received
              tail0_sent
              tail0_received;
            introduce exists
              (after_verify':CS.connection_model)
              (after_app_write':CS.connection_model)
              (after_app_read':CS.connection_model)
              (client_app_write_material':CS.traffic_key_material)
              (client_app_read_material':CS.traffic_key_material).
              CS.conn_events_sent_seal_replay
                model12
                (verify_ev ::
                 CS.ConnLocalEvent
                   (CS.LocalInstallTrafficKeys {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficWrite;
                     CS.install_material = client_app_write_material';
                   }) ::
                 CS.ConnLocalEvent
                   (CS.LocalInstallTrafficKeys {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficRead;
                     CS.install_material = client_app_read_material';
                   }) ::
                 sent_ev ::
                 [])
                suffix_sent
                suffix_received
                final_model /\
              CS.step_model model12 verify_ev == Some after_verify' /\
              CS.step_model
                after_verify'
                (CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeys {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = client_app_write_material';
                  })) == Some after_app_write' /\
              CS.step_model
                after_app_write'
                (CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeys {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = client_app_read_material';
                  })) == Some after_app_read' /\
              CS.step_model after_app_read' sent_ev == Some final_model
            with model1 after_write model3 write_material read_material and ()
          )
        )
      )
    )
  )
let lemma_client_finished_exact_suffix_sent_seal_raw_slice
  (model:CS.connection_model)
  (sf:M.finished)
  (e13 e14:CS.conn_event)
  (cf:M.finished)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        CS.conn_events_sent_seal_replay
          model
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
           e13 ::
           e14 ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf);
           }) ::
           [])
          raw_sent
          raw_received
          final_model)
      (ensures CS.raw_records_exactly raw_sent T.ApplicationData 1)
=
  let verify_ev = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let sent_ev =
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished cf);
    }) in
  PWR.lemma_conn_events_sent_seal_replay_head
    model
    verify_ev
    (e13 :: e14 :: sent_ev :: [])
    raw_sent
    raw_received
    final_model;
  eliminate exists
    (model1:CS.connection_model)
    delta0_sent
    delta0_received
    tail0_sent
    tail0_received.
    CS.legal_event model verify_ev /\
    CS.step_model model verify_ev == Some model1 /\
    CS.event_raw_delta_legal model verify_ev delta0_sent delta0_received /\
    CS.sent_event_nonempty_seal_projection model verify_ev delta0_sent /\
    Seq.equal raw_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal raw_received (B.append delta0_received tail0_received) /\
    CS.conn_events_sent_seal_replay
      model1
      (e13 :: e14 :: sent_ev :: [])
      tail0_sent
      tail0_received
      final_model
  returns CS.raw_records_exactly raw_sent T.ApplicationData 1
  with _.
  (
    PWR.lemma_conn_events_sent_seal_replay_head
      model1
      e13
      (e14 :: sent_ev :: [])
      tail0_sent
      tail0_received
      final_model;
    eliminate exists
      (model2:CS.connection_model)
      delta1_sent
      delta1_received
      tail1_sent
      tail1_received.
      CS.legal_event model1 e13 /\
      CS.step_model model1 e13 == Some model2 /\
      CS.event_raw_delta_legal model1 e13 delta1_sent delta1_received /\
      CS.sent_event_nonempty_seal_projection model1 e13 delta1_sent /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_sent_seal_replay
        model2
        (e14 :: sent_ev :: [])
        tail1_sent
        tail1_received
        final_model
    returns CS.raw_records_exactly raw_sent T.ApplicationData 1
    with _.
    (
      PWR.lemma_conn_events_sent_seal_replay_head
        model2
        e14
        (sent_ev :: [])
        tail1_sent
        tail1_received
        final_model;
      eliminate exists
        (model3:CS.connection_model)
        delta2_sent
        delta2_received
        tail2_sent
        tail2_received.
        CS.legal_event model2 e14 /\
        CS.step_model model2 e14 == Some model3 /\
        CS.event_raw_delta_legal model2 e14 delta2_sent delta2_received /\
        CS.sent_event_nonempty_seal_projection model2 e14 delta2_sent /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_sent_seal_replay
          model3
          (sent_ev :: [])
          tail2_sent
          tail2_received
          final_model
      returns CS.raw_records_exactly raw_sent T.ApplicationData 1
      with _.
      (
        PWR.lemma_conn_events_sent_seal_replay_head
          model3
          sent_ev
          []
          tail2_sent
          tail2_received
          final_model;
        eliminate exists
          (model4:CS.connection_model)
          delta3_sent
          delta3_received
          tail3_sent
          tail3_received.
          CS.legal_event model3 sent_ev /\
          CS.step_model model3 sent_ev == Some model4 /\
          CS.event_raw_delta_legal model3 sent_ev delta3_sent delta3_received /\
          CS.sent_event_nonempty_seal_projection model3 sent_ev delta3_sent /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_sent_seal_replay
            model4
            []
            tail3_sent
            tail3_received
            final_model
        returns CS.raw_records_exactly raw_sent T.ApplicationData 1
        with _.
        (
          PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
          assert (
            PNTCAS.client_no_tail_application_write_install_event e13 \/
            PNTCAS.client_no_tail_application_read_install_event e13);
          assert (
            PNTCAS.client_no_tail_application_write_install_event e14 \/
            PNTCAS.client_no_tail_application_read_install_event e14);
          assert_norm (Seq.equal delta0_sent B.empty);
          lemma_application_install_event_sent_delta_empty
            model1
            e13
            delta1_sent
            delta1_received;
          lemma_application_install_event_sent_delta_empty
            model2
            e14
            delta2_sent
            delta2_received;
          assert_norm (CS.network_message_is_cleartext
            CL.Sent
            (M.TlsHandshake (M.Finished cf)) == false);
          assert_norm (CS.protected_record_count
            CL.Sent
            (M.TlsHandshake (M.Finished cf)) == 1);
          assert (CS.raw_records_exactly delta3_sent T.ApplicationData 1);
          assert (Seq.equal tail3_sent B.empty);
          Seq.lemma_eq_elim tail3_sent B.empty;
          Seq.append_empty_r delta3_sent;
          assert (Seq.equal tail2_sent delta3_sent);
          Seq.lemma_eq_elim delta2_sent B.empty;
          CL.lemma_append_empty_left tail2_sent;
          assert (Seq.equal tail1_sent tail2_sent);
          Seq.lemma_eq_elim tail1_sent tail2_sent;
          Seq.lemma_eq_elim tail2_sent delta3_sent;
          Seq.lemma_eq_elim delta1_sent B.empty;
          CL.lemma_append_empty_left tail1_sent;
          assert (Seq.equal tail0_sent tail1_sent);
          Seq.lemma_eq_elim tail0_sent tail1_sent;
          Seq.lemma_eq_elim tail1_sent delta3_sent;
          Seq.lemma_eq_elim delta0_sent B.empty;
          CL.lemma_append_empty_left tail0_sent;
          assert (Seq.equal raw_sent tail0_sent);
          Seq.lemma_eq_elim raw_sent tail0_sent;
          Seq.lemma_eq_elim tail0_sent delta3_sent
        )
      )
    )
  )

let lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        CS.connection_state_sent_seal_replay_consistent client)
      (ensures
        client_finished_exact_suffix_sent_seal_replay_slice client)
=
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
    TLS13.Impl.Driver.PairingNoTailClientPostSharedShape.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14
  returns
    client_finished_exact_suffix_sent_seal_replay_slice client
  with _.
  (
    let ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
    let ev1 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) in
    let ev2 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) in
    let ev3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
    let ev4 = e4 in
    let ev5 = e5 in
    let ev6 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) in
    let ev7 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) in
    let ev8 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
    let ev9 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) in
    let ev10 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
    let ev11 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) in
    let ev12 = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
    let ev13 = e13 in
    let ev14 = e14 in
    let ev15 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) in
    let prefix : list CS.conn_event =
      ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
      ev8 :: ev9 :: ev10 :: ev11 :: [] in
    let suffix : list CS.conn_event =
      ev12 :: ev13 :: ev14 :: ev15 :: [] in
    ListP.append_cons_l
      ev0
      (ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
       ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev1
      (ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
       ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev2
      (ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
       ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev3
      (ev4 :: ev5 :: ev6 :: ev7 ::
       ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev4
      (ev5 :: ev6 :: ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev5
      (ev6 :: ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev6
      (ev7 :: ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev7
      (ev8 :: ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev8
      (ev9 :: ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l
      ev9
      (ev10 :: ev11 :: [])
      suffix;
    ListP.append_cons_l ev10 (ev11 :: []) suffix;
    ListP.append_cons_l ev11 [] suffix;
    ListP.append_nil_l suffix;
    assert (
      FStar.List.Tot.append prefix suffix ==
        ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
        ev8 :: ev9 :: ev10 :: ev11 :: suffix);
    assert (
      FStar.List.Tot.append prefix suffix ==
        ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
        ev8 :: ev9 :: ev10 :: ev11 :: ev12 :: ev13 :: ev14 :: ev15 :: []);
    assert (
      ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 ::
      ev8 :: ev9 :: ev10 :: ev11 :: ev12 :: ev13 :: ev14 :: ev15 :: [] ==
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
        []);
    assert (
      client.CS.cs_event_log ==
        FStar.List.Tot.append prefix suffix);
    assert (
      CS.conn_events_sent_seal_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        (FStar.List.Tot.append prefix suffix)
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model);
    PWR.lemma_conn_events_sent_seal_replay_append_split
      (CS.initial_model client.CS.cs_model.CS.model_config)
      prefix
      suffix
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model;
    eliminate exists
      (mid:CS.connection_model)
      (prefix_sent:B.bytes)
      (prefix_received:B.bytes)
      (suffix_sent:B.bytes)
      (suffix_received:B.bytes).
      Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        (B.append prefix_sent suffix_sent) /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_received
        (B.append prefix_received suffix_received) /\
      CS.conn_events_sent_seal_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        prefix
        prefix_sent
        prefix_received
        mid /\
      CS.conn_events_sent_seal_replay
        mid
        suffix
        suffix_sent
        suffix_received
        client.CS.cs_model
    returns
      client_finished_exact_suffix_sent_seal_replay_slice client
    with _.
    (
      introduce exists
        (start':CS.handshake_start)
        (ch':M.client_hello)
        (sh':M.server_hello)
        (client_shared':C.x25519_shared_secret)
        (e4':CS.conn_event)
        (e5':CS.conn_event)
        (ee':M.encrypted_extensions)
        (cert':M.certificate_msg)
        (peer':X.peer_identity)
        (cv':M.certificate_verify)
        (sf':M.finished)
        (e13':CS.conn_event)
        (e14':CS.conn_event)
        (cf':M.finished)
        (model12':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
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
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
          }) ::
          CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv') ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished sf');
          }) ::
          CS.ConnLocalEvent (CS.LocalVerifyFinished sf') ::
          e13' ::
          e14' ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished cf');
          }) ::
          [] /\
        TLS13.Impl.Driver.PairingNoTailClientPostSharedShape.client_no_tail_two_handshake_install_cover
          e4'
          e5' /\
        PNTCAS.client_no_tail_application_install_cover e13' e14' /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_sent_seal_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
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
             CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
           }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv') ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.Finished sf');
           }) ::
           [])
          prefix_sent'
          prefix_received'
          model12' /\
        CS.conn_events_sent_seal_replay
          model12'
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf') ::
           e13' ::
           e14' ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf');
           }) ::
           [])
          suffix_sent'
          suffix_received'
          client.CS.cs_model
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
        mid
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_client_finished_exact_suffix_sent_seal_raw_record_slice_from_replay_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_exact_suffix_sent_seal_replay_slice client)
      (ensures client_finished_exact_suffix_sent_seal_raw_record_slice client)
=
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
    (cf:M.finished)
    (model12:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
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
    TLS13.Impl.Driver.PairingNoTailClientPostSharedShape.client_no_tail_two_handshake_install_cover
      e4
      e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
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
       [])
      prefix_sent
      prefix_received
      model12 /\
    CS.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model
  returns
    client_finished_exact_suffix_sent_seal_raw_record_slice client
  with _.
  (
    lemma_client_finished_exact_suffix_sent_seal_raw_slice
      model12
      sf
      e13
      e14
      cf
      suffix_sent
      suffix_received
      client.CS.cs_model;
    introduce exists
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
      model12
      prefix_sent
      prefix_received
      suffix_sent
      suffix_received.
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
      TLS13.Impl.Driver.PairingNoTailClientPostSharedShape.client_no_tail_two_handshake_install_cover
        e4
        e5 /\
      PNTCAS.client_no_tail_application_install_cover e13 e14 /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        (B.append prefix_sent suffix_sent) /\
      Seq.equal
        client.CS.cs_wire_log.CL.raw_received
        (B.append prefix_received suffix_received) /\
      CS.conn_events_sent_seal_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
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
         [])
        prefix_sent
        prefix_received
        model12 /\
      CS.conn_events_sent_seal_replay
        model12
        (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
         e13 ::
         e14 ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.Finished cf);
         }) ::
         [])
        suffix_sent
        suffix_received
        client.CS.cs_model /\
      CS.raw_records_exactly suffix_sent T.ApplicationData 1
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
      model12
      prefix_sent
      prefix_received
      suffix_sent
      suffix_received
    and ()
  )

let lemma_client_finished_sent_seal_suffix_head_steps
  (model12:CS.connection_model)
  (sf:M.finished)
  (e13 e14:CS.conn_event)
  (cf:M.finished)
  (suffix_sent:B.bytes)
  (suffix_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          model12
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
           e13 ::
           e14 ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf);
           }) ::
           [])
          suffix_sent
          suffix_received
          final_model)
      (ensures
        client_finished_sent_seal_suffix_head_steps
          model12
          sf
          e13
          e14
          cf
          final_model)
=
  let verify_ev = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let sent_ev =
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.Finished cf);
    }) in
  assert (CS.conn_events_sent_seal_replay
    model12
    (verify_ev :: e13 :: e14 :: sent_ev :: [])
    suffix_sent
    suffix_received
    final_model);
  PWR.lemma_conn_events_sent_seal_replay_head
    model12
    verify_ev
    (e13 :: e14 :: sent_ev :: [])
    suffix_sent
    suffix_received
    final_model;
  eliminate exists
    (after_verify:CS.connection_model)
    delta0_sent
    delta0_received
    tail0_sent
    tail0_received.
    CS.legal_event model12 verify_ev /\
    CS.step_model model12 verify_ev == Some after_verify /\
    CS.event_raw_delta_legal model12 verify_ev delta0_sent delta0_received /\
    CS.sent_event_nonempty_seal_projection model12 verify_ev delta0_sent /\
    Seq.equal suffix_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal suffix_received (B.append delta0_received tail0_received) /\
    CS.conn_events_sent_seal_replay
      after_verify
      (e13 :: e14 :: sent_ev :: [])
      tail0_sent
      tail0_received
      final_model
  returns client_finished_sent_seal_suffix_head_steps model12 sf e13 e14 cf final_model
  with _.
  (
    PWR.lemma_conn_events_sent_seal_replay_head
      after_verify
      e13
      (e14 :: sent_ev :: [])
      tail0_sent
      tail0_received
      final_model;
    eliminate exists
      (after_e13:CS.connection_model)
      delta1_sent
      delta1_received
      tail1_sent
      tail1_received.
      CS.legal_event after_verify e13 /\
      CS.step_model after_verify e13 == Some after_e13 /\
      CS.event_raw_delta_legal after_verify e13 delta1_sent delta1_received /\
      CS.sent_event_nonempty_seal_projection after_verify e13 delta1_sent /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_sent_seal_replay
        after_e13
        (e14 :: sent_ev :: [])
        tail1_sent
        tail1_received
        final_model
    returns client_finished_sent_seal_suffix_head_steps model12 sf e13 e14 cf final_model
    with _.
    (
      PWR.lemma_conn_events_sent_seal_replay_head
        after_e13
        e14
        (sent_ev :: [])
        tail1_sent
        tail1_received
        final_model;
      eliminate exists
        (after_e14:CS.connection_model)
        delta2_sent
        delta2_received
        tail2_sent
        tail2_received.
        CS.legal_event after_e13 e14 /\
        CS.step_model after_e13 e14 == Some after_e14 /\
        CS.event_raw_delta_legal after_e13 e14 delta2_sent delta2_received /\
        CS.sent_event_nonempty_seal_projection after_e13 e14 delta2_sent /\
        Seq.equal tail1_sent (B.append delta2_sent tail2_sent) /\
        Seq.equal tail1_received (B.append delta2_received tail2_received) /\
        CS.conn_events_sent_seal_replay
          after_e14
          (sent_ev :: [])
          tail2_sent
          tail2_received
          final_model
      returns client_finished_sent_seal_suffix_head_steps model12 sf e13 e14 cf final_model
      with _.
      (
        PWR.lemma_conn_events_sent_seal_replay_head
          after_e14
          sent_ev
          []
          tail2_sent
          tail2_received
          final_model;
        eliminate exists
          (after_finished:CS.connection_model)
          delta3_sent
          delta3_received
          tail3_sent
          tail3_received.
          CS.legal_event after_e14 sent_ev /\
          CS.step_model after_e14 sent_ev == Some after_finished /\
          CS.event_raw_delta_legal after_e14 sent_ev delta3_sent delta3_received /\
          CS.sent_event_nonempty_seal_projection after_e14 sent_ev delta3_sent /\
          Seq.equal tail2_sent (B.append delta3_sent tail3_sent) /\
          Seq.equal tail2_received (B.append delta3_received tail3_received) /\
          CS.conn_events_sent_seal_replay
            after_finished
            []
            tail3_sent
            tail3_received
            final_model
        returns client_finished_sent_seal_suffix_head_steps model12 sf e13 e14 cf final_model
        with _.
        (
          assert_norm (
            CS.conn_events_sent_seal_replay
              after_finished
              []
              tail3_sent
              tail3_received
              final_model ==
            (Seq.equal tail3_sent B.empty /\
             Seq.equal tail3_received B.empty /\
             final_model == after_finished));
          assert (after_finished == final_model);
          introduce exists
            (after_verify':CS.connection_model)
            (after_e13':CS.connection_model)
            (after_e14':CS.connection_model).
            CS.step_model
              model12
              (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) ==
              Some after_verify' /\
            CS.step_model after_verify' e13 == Some after_e13' /\
            CS.step_model after_e13' e14 == Some after_e14' /\
            CS.step_model
              after_e14'
              (CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf);
              })) == Some final_model
          with after_verify after_e13 after_e14 and ()
        )
      )
    )
  )

let lemma_client_finished_exact_suffix_sent_seal_head_step_slice_from_replay_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_exact_suffix_sent_seal_replay_slice client)
      (ensures client_finished_exact_suffix_sent_seal_head_step_slice client)
=
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
    (cf:M.finished)
    (model12:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
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
    TLS13.Impl.Driver.PairingNoTailClientPostSharedShape.client_no_tail_two_handshake_install_cover
      e4
      e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
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
       [])
      prefix_sent
      prefix_received
      model12 /\
    CS.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model
  returns
    client_finished_exact_suffix_sent_seal_head_step_slice client
  with _.
  (
    lemma_client_finished_exact_suffix_sent_seal_raw_slice
      model12
      sf
      e13
      e14
      cf
      suffix_sent
      suffix_received
      client.CS.cs_model;
    lemma_client_finished_sent_seal_suffix_head_steps
      model12
      sf
      e13
      e14
      cf
      suffix_sent
      suffix_received
      client.CS.cs_model;
    introduce exists
      (sf':M.finished)
      (e13':CS.conn_event)
      (e14':CS.conn_event)
      (cf':M.finished)
      (model12':CS.connection_model)
      (suffix_sent':B.bytes)
      (suffix_received':B.bytes).
      PNTCAS.client_no_tail_application_install_cover e13' e14' /\
      CS.conn_events_sent_seal_replay
        model12'
        (CS.ConnLocalEvent (CS.LocalVerifyFinished sf') ::
         e13' ::
         e14' ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.Finished cf');
         }) ::
         [])
        suffix_sent'
        suffix_received'
        client.CS.cs_model /\
      client_finished_sent_seal_suffix_head_steps
        model12'
        sf'
        e13'
        e14'
        cf'
        client.CS.cs_model /\
      CS.raw_records_exactly suffix_sent' T.ApplicationData 1
    with sf e13 e14 cf model12 suffix_sent suffix_received and ()
  )

let lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
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
        client_finished_exact_suffix_sent_seal_replay_slice client)
=
  PNTCFS.lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_replay_consistent
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone
    client
    server

let lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_raw_record_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
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
        client_finished_exact_suffix_sent_seal_raw_record_slice client)
=
  lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_client_finished_exact_suffix_sent_seal_raw_record_slice_from_replay_slice client

let lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_head_step_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
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
        client_finished_exact_suffix_sent_seal_head_step_slice client)
=
  lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_client_finished_exact_suffix_sent_seal_head_step_slice_from_replay_slice
    client

let lemma_client_finished_canonical_sent_seal_replay_slice_from_head_step_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_exact_suffix_sent_seal_head_step_slice client)
      (ensures client_finished_canonical_sent_seal_replay_slice client)
=
  eliminate exists
    (sf:M.finished)
    (e13 e14:CS.conn_event)
    (cf:M.finished)
    (model12:CS.connection_model)
    suffix_sent
    suffix_received.
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    CS.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model /\
    client_finished_sent_seal_suffix_head_steps
      model12
      sf
      e13
      e14
      cf
      client.CS.cs_model /\
    CS.raw_records_exactly suffix_sent T.ApplicationData 1
  returns client_finished_canonical_sent_seal_replay_slice client
  with _.
  (
    lemma_client_finished_sent_seal_replay_canonicalize_application_installs
      model12
      sf
      e13
      e14
      cf
      suffix_sent
      suffix_received
      client.CS.cs_model;
    eliminate exists
      (after_verify:CS.connection_model)
      (after_app_write:CS.connection_model)
      (after_app_read:CS.connection_model)
      (client_app_write_material:CS.traffic_key_material)
      (client_app_read_material:CS.traffic_key_material).
      CS.conn_events_sent_seal_replay
        model12
        (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
         CS.ConnLocalEvent
           (CS.LocalInstallTrafficKeys {
             CS.install_epoch = CS.TrafficApplication;
             CS.install_direction = CS.TrafficWrite;
             CS.install_material = client_app_write_material;
           }) ::
         CS.ConnLocalEvent
           (CS.LocalInstallTrafficKeys {
             CS.install_epoch = CS.TrafficApplication;
             CS.install_direction = CS.TrafficRead;
             CS.install_material = client_app_read_material;
           }) ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.Finished cf);
         }) ::
         [])
        suffix_sent
        suffix_received
        client.CS.cs_model /\
      CS.step_model
        model12
        (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) ==
        Some after_verify /\
      CS.step_model
        after_verify
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_app_write_material;
          })) == Some after_app_write /\
      CS.step_model
        after_app_write
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_app_read_material;
          })) == Some after_app_read /\
      CS.step_model
        after_app_read
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        })) == Some client.CS.cs_model
    returns client_finished_canonical_sent_seal_replay_slice client
    with _.
    (
      introduce exists
        (sf':M.finished)
        (cf':M.finished)
        (model12':CS.connection_model)
        (after_verify':CS.connection_model)
        (after_app_write':CS.connection_model)
        (after_app_read':CS.connection_model)
        (client_app_write_material':CS.traffic_key_material)
        (client_app_read_material':CS.traffic_key_material)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        CS.conn_events_sent_seal_replay
          model12'
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf') ::
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeys {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficWrite;
               CS.install_material = client_app_write_material';
             }) ::
           CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeys {
               CS.install_epoch = CS.TrafficApplication;
               CS.install_direction = CS.TrafficRead;
               CS.install_material = client_app_read_material';
             }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf');
           }) ::
           [])
          suffix_sent'
          suffix_received'
          client.CS.cs_model /\
        CS.step_model
          model12'
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf')) == Some after_verify' /\
        CS.step_model
          after_verify'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_app_write_material';
            })) == Some after_app_write' /\
        CS.step_model
          after_app_write'
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_app_read_material';
            })) == Some after_app_read' /\
        CS.step_model
          after_app_read'
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished cf');
          })) == Some client.CS.cs_model /\
        CS.raw_records_exactly suffix_sent' T.ApplicationData 1
      with
        sf
        cf
        model12
        after_verify
        after_app_write
        after_app_read
        client_app_write_material
        client_app_read_material
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_client_finished_canonical_sent_seal_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
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
        client_finished_canonical_sent_seal_replay_slice client)
=
  lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_head_step_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_client_finished_canonical_sent_seal_replay_slice_from_head_step_slice
    client

let lemma_client_finished_staged_replay_fragment_from_staged_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (s:PSNB.staged_replay_witnesses)
  : Lemma
      (requires
        PSNB.paired_supported_normalized_staged_replay_boundary_inputs
          client
          server
          w
          s)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)
=
  let r = {
    cfr_client_finished_write_install_source =
      s.PSNB.snb_client_finished_write_install_source;
    cfr_client_finished_read_install_source =
      s.PSNB.snb_client_finished_read_install_source;
    cfr_client_finished_client_write_material =
      s.PSNB.snb_client_finished_client_write_material;
    cfr_client_finished_server_read_material =
      s.PSNB.snb_client_finished_server_read_material;
    cfr_client_finished_sender =
      s.PSNB.snb_client_finished_sender;
    cfr_client_finished_receiver =
      s.PSNB.snb_client_finished_receiver;
    cfr_client_finished_raw_sent =
      s.PSNB.snb_client_finished_raw_sent;
    cfr_client_finished_raw_received =
      s.PSNB.snb_client_finished_raw_received;
    cfr_server_finished_raw_sent =
      s.PSNB.snb_server_finished_raw_sent;
    cfr_server_finished_raw_received =
      s.PSNB.snb_server_finished_raw_received;
    cfr_client_finished_final =
      s.PSNB.snb_client_finished_final;
    cfr_server_finished_final =
      s.PSNB.snb_server_finished_final;
  } in
  assert (client_finished_staged_replay_fragment client server w r)
  by (
    Tac.norm
      [delta_only
        [`%PSNB.paired_supported_normalized_staged_replay_boundary_inputs;
         `%client_finished_staged_replay_fragment]];
    Tac.smt ());
  introduce exists (r':client_finished_replay_witnesses).
    client_finished_staged_replay_fragment client server w r'
  with r and ()

let lemma_clean16_client_finished_staged_replay_fragment_from_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        PNTCFRE.paired_client_finished_raw_record_equality client server /\
        clean16_client_finished_semantic_replay_completion client server w)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)
=
  assert (exists r.
    client_finished_staged_replay_fragment client server w r)

let lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_replay_fragment_from_completion
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (w:PCB.handshake_complete_boundary_witnesses)
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
          server_sent /\
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        clean16_client_finished_semantic_replay_completion client server w)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)
=
  PNTCFS.lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFRE.lemma_clean16_no_tail_valid_byte_traces_client_finished_raw_record_equality
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_client_finished_staged_replay_fragment_from_completion
    client
    server
    w

#pop-options
