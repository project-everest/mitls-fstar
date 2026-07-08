module TLS13.Impl.Driver.PairingNoTailServerFlightReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module ListP = FStar.List.Tot.Properties
module M = TLS13.Messages
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module Tac = FStar.Tactics
module X = TLS13.X509.Spec

#push-options "--split_queries always --z3rlimit 10"

let lemma_server_handshake_install_event_deltas_empty
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        (PNTSS.server_no_tail_handshake_write_install_event ev \/
         PNTSS.server_no_tail_handshake_read_install_event ev) /\
        CS.event_raw_delta_legal model ev delta_sent delta_received)
      (ensures
        Seq.equal delta_sent B.empty /\
        Seq.equal delta_received B.empty)
=
  match ev with
  | CS.ConnLocalEvent _ -> ()
  | _ -> assert False

let lemma_server_handshake_install_cover_step_model_canonical_write_read
  (model0 model1 model2:CS.connection_model)
  (e0 e1:CS.conn_event)
  : Lemma
      (requires
        PNTSS.server_no_tail_two_handshake_install_cover e0 e1 /\
        CS.legal_event model0 e0 /\
        CS.legal_event model1 e1 /\
        CS.step_model model0 e0 == Some model1 /\
        CS.step_model model1 e1 == Some model2)
      (ensures
        exists
          (write_material:CS.traffic_key_material)
          (read_material:CS.traffic_key_material)
          (after_write:CS.connection_model).
          let write_ev =
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              }) in
          let read_ev =
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              }) in
          CS.legal_event model0 write_ev /\
          CS.step_model model0 write_ev == Some after_write /\
          CS.legal_event after_write read_ev /\
          CS.step_model after_write read_ev == Some model2)
=
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e0 e1;
  match e0, e1 with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install0),
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install1) ->
    let install0 = role_install0.CS.install_payload in
    let install1 = role_install1.CS.install_payload in
    if PNTSS.server_no_tail_handshake_write_install_event e0 then (
      assert (PNTSS.server_no_tail_handshake_read_install_event e1);
      assert (role_install0.CS.install_role == CS.ServerEndpoint);
      assert (install0.CS.install_epoch == CS.TrafficHandshake);
      assert (install0.CS.install_direction == CS.TrafficWrite);
      assert (role_install1.CS.install_role == CS.ServerEndpoint);
      assert (install1.CS.install_epoch == CS.TrafficHandshake);
      assert (install1.CS.install_direction == CS.TrafficRead);
      let write_material = install0.CS.install_material in
      let read_material = install1.CS.install_material in
      let write_ev =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material;
            };
          }) in
      let read_ev =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material;
            };
          }) in
      assert (write_ev == e0);
      assert (read_ev == e1);
      introduce exists
        (write_material':CS.traffic_key_material)
        (read_material':CS.traffic_key_material)
        (after_write':CS.connection_model).
        (let write_ev' =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = write_material';
              };
            }) in
         let read_ev' =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material';
              };
            }) in
         CS.legal_event model0 write_ev' /\
         CS.step_model model0 write_ev' == Some after_write' /\
         CS.legal_event after_write' read_ev' /\
         CS.step_model after_write' read_ev' == Some model2)
      with write_material read_material model1 and ()
    )
    else (
      assert (PNTSS.server_no_tail_handshake_read_install_event e0);
      assert (PNTSS.server_no_tail_handshake_write_install_event e1);
      assert (role_install0.CS.install_role == CS.ServerEndpoint);
      assert (install0.CS.install_epoch == CS.TrafficHandshake);
      assert (install0.CS.install_direction == CS.TrafficRead);
      assert (role_install1.CS.install_role == CS.ServerEndpoint);
      assert (install1.CS.install_epoch == CS.TrafficHandshake);
      assert (install1.CS.install_direction == CS.TrafficWrite);
      let read_material = install0.CS.install_material in
      let write_material = install1.CS.install_material in
      let read_ev =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = read_material;
            };
          }) in
      let write_ev =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = write_material;
            };
          }) in
      assert (read_ev == e0);
      assert (write_ev == e1);
      assert_norm (CS.legal_event model0 write_ev);
      match CS.step_model model0 write_ev with
      | Some after_write ->
        assert_norm (CS.legal_event after_write read_ev);
        assert_norm (CS.step_model after_write read_ev == Some model2);
        introduce exists
          (write_material':CS.traffic_key_material)
          (read_material':CS.traffic_key_material)
          (after_write':CS.connection_model).
          (let write_ev' =
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material';
                };
              }) in
           let read_ev' =
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material';
                };
              }) in
           CS.legal_event model0 write_ev' /\
           CS.step_model model0 write_ev' == Some after_write' /\
           CS.legal_event after_write' read_ev' /\
           CS.step_model after_write' read_ev' == Some model2)
        with write_material read_material after_write and ()
      | None ->
        assert False
    )
  | _, _ ->
    assert False

noextract
let normalized_replay_boundary_server_flight_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  : prop =
  Seq.equal server_raw_sent client_raw_received /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_server_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_verify_skip /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg3 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg3 /\
  CS.step_model
    w.PCB.hcb_server_model5
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_material;
        };
      })) == Some w.PCB.hcb_server_after_install /\
  CS.step_model
    w.PCB.hcb_client_model4
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_material;
      })) == Some w.PCB.hcb_client_after_install /\
  CS.step_model
    w.PCB.hcb_server_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg0;
    }) == Some w.PCB.hcb_server_after0 /\
  CS.step_model
    w.PCB.hcb_client_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg0;
    }) == Some w.PCB.hcb_client_after0 /\
  w.PCB.hcb_server_after0.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after_install.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after0.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_install.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_server_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg1;
    }) == Some w.PCB.hcb_server_after1 /\
  CS.step_model
    w.PCB.hcb_client_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg1;
    }) == Some w.PCB.hcb_client_after1 /\
  w.PCB.hcb_server_after1.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after0.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after1.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after0.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_server_after1
    (CS.ConnLocalEvent w.PCB.hcb_server_auth_skip) ==
    Some w.PCB.hcb_server_after_auth_skip /\
  CS.step_model
    w.PCB.hcb_client_after1
    (CS.ConnLocalEvent w.PCB.hcb_client_auth_skip) ==
    Some w.PCB.hcb_client_after_auth_skip /\
  CS.step_model
    w.PCB.hcb_server_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg2;
    }) == Some w.PCB.hcb_server_after2 /\
  CS.step_model
    w.PCB.hcb_client_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg2;
    }) == Some w.PCB.hcb_client_after2 /\
  w.PCB.hcb_server_after2.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after_auth_skip.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after2.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_auth_skip.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_client_after2
    (CS.ConnLocalEvent w.PCB.hcb_client_verify_skip) ==
    Some w.PCB.hcb_client_after_verify_skip /\
  CS.step_model
    w.PCB.hcb_server_after2
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg3;
    }) == Some w.PCB.hcb_server_after3 /\
  CS.step_model
    w.PCB.hcb_client_after_verify_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg3;
    }) == Some w.PCB.hcb_client_after3 /\
  w.PCB.hcb_server_after3.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after2.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after3.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_verify_skip.CS.model_record.CS.record_read /\
  PWL.paired_protected_handshake_contiguous_replay_views
    w.PCB.hcb_server_model5
    w.PCB.hcb_client_model4
    w.PCB.hcb_server_material
    w.PCB.hcb_client_material
    w.PCB.hcb_sent_msg0
    w.PCB.hcb_received_msg0
    w.PCB.hcb_sent_msg1
    w.PCB.hcb_received_msg1
    w.PCB.hcb_server_auth_skip
    w.PCB.hcb_client_auth_skip
    w.PCB.hcb_sent_msg2
    w.PCB.hcb_received_msg2
    w.PCB.hcb_client_verify_skip
    w.PCB.hcb_sent_msg3
    w.PCB.hcb_received_msg3
    w.PCB.hcb_verified_server_finished
    w.PCB.hcb_client_app_write_material
    w.PCB.hcb_client_app_read_material
    w.PCB.hcb_server_app_write_material
    w.PCB.hcb_sent_msg4
    w.PCB.hcb_received_msg4
    w.PCB.hcb_client_finished_rest
    w.PCB.hcb_server_finished_rest
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server.CS.cs_model
    client.CS.cs_model

let lemma_server_post_server_hello_sent_seal_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTSFS.clean16_server_encrypted_flight_staged_milestone client server /\
        CS.connection_state_sent_seal_replay_consistent server)
      (ensures server_post_server_hello_sent_seal_replay_slice server)
=
  assert (TLS13.Impl.Driver.PairingNoTailServerPostHelloShape.server_no_tail_post_server_hello_suffix_shape server);
  assert (PNTSS.server_no_tail_next_two_events_handshake_install_cover server);
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
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6
  returns server_post_server_hello_sent_seal_replay_slice server
  with _.
  (
    let prefix =
      PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh in
    let suffix = e5 :: e6 :: rest in
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
    assert (prefix == ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: []);
    ListP.append_cons_l
      ev0
      (ev1 :: ev2 :: ev3 :: ev4 :: [])
      suffix;
    ListP.append_cons_l
      ev1
      (ev2 :: ev3 :: ev4 :: [])
      suffix;
    ListP.append_cons_l
      ev2
      (ev3 :: ev4 :: [])
      suffix;
    ListP.append_cons_l ev3 (ev4 :: []) suffix;
    ListP.append_cons_l ev4 [] suffix;
    ListP.append_nil_l suffix;
    assert (FStar.List.Tot.append prefix suffix ==
      ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: suffix);
    assert (server.CS.cs_event_log ==
      FStar.List.Tot.append prefix suffix);
    assert (
      CS.conn_events_sent_seal_replay
        (CS.initial_model server.CS.cs_model.CS.model_config)
        (FStar.List.Tot.append prefix suffix)
        server.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        server.CS.cs_model);
    PWR.lemma_conn_events_sent_seal_replay_append_split
      (CS.initial_model server.CS.cs_model.CS.model_config)
      prefix
      suffix
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists
      (model5:CS.connection_model)
      (prefix_sent:B.bytes)
      (prefix_received:B.bytes)
      (suffix_sent:B.bytes)
      (suffix_received:B.bytes).
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append prefix_sent suffix_sent) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append prefix_received suffix_received) /\
      CS.conn_events_sent_seal_replay
        (CS.initial_model server.CS.cs_model.CS.model_config)
        prefix
        prefix_sent
        prefix_received
        model5 /\
      CS.conn_events_sent_seal_replay
        model5
        suffix
        suffix_sent
        suffix_received
        server.CS.cs_model
    returns server_post_server_hello_sent_seal_replay_slice server
    with _.
    (
      introduce exists
        (ch':M.client_hello)
        (selection':CS.server_handshake_selection)
        (server_shared':C.x25519_shared_secret)
        (sh':M.server_hello)
        (e5':CS.conn_event)
        (e6':CS.conn_event)
        (rest':list CS.conn_event)
        (model5':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch'
              selection'
              server_shared'
              sh')
            (e5' :: e6' :: rest') /\
        PNTSS.server_no_tail_two_handshake_install_cover e5' e6' /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_sent_seal_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events
            ch'
            selection'
            server_shared'
            sh')
          prefix_sent'
          prefix_received'
          model5' /\
        CS.conn_events_sent_seal_replay
          model5'
          (e5' :: e6' :: rest')
          suffix_sent'
          suffix_received'
          server.CS.cs_model
      with
        ch
        selection
        server_shared
        sh
        e5
        e6
        rest
        model5
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_server_post_server_hello_ordered_sent_seal_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires
        server_post_server_hello_sent_seal_replay_slice server /\
        PNTPH.server_no_tail_post_two_handshake_installs_tail_order server)
      (ensures server_post_server_hello_ordered_sent_seal_replay_slice server)
=
  eliminate exists
    (ch:M.client_hello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:M.server_hello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (rest:list CS.conn_event)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_sent_seal_replay
      model5
      (e5 :: e6 :: rest)
      suffix_sent
      suffix_received
      server.CS.cs_model
  returns server_post_server_hello_ordered_sent_seal_replay_slice server
  with _.
  (
    PNTPH.lemma_server_no_tail_post_two_handshake_installs_tail_order_for_split
      server
      ch
      selection
      server_shared
      sh
      e5
      e6
      rest;
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
    returns server_post_server_hello_ordered_sent_seal_replay_slice server
    with _.
    (
      let ordered_rest =
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
        ] in
      assert (rest == ordered_rest);
      assert (e5 :: e6 :: rest == e5 :: e6 :: ordered_rest);
      introduce exists
        (ch':M.client_hello)
        (selection':CS.server_handshake_selection)
        (server_shared':C.x25519_shared_secret)
        (sh':M.server_hello)
        (e5':CS.conn_event)
        (e6':CS.conn_event)
        (ee':M.encrypted_extensions)
        (cert':M.certificate_msg)
        (cv':M.certificate_verify)
        (sf':M.finished)
        (cf':M.finished)
        (server_app_write_material':CS.traffic_key_material)
        (server_app_read_material':CS.traffic_key_material)
        (model5':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch'
              selection'
              server_shared'
              sh')
            (e5' :: e6' ::
              [
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Certificate cert');
                };
                CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv');
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Finished sf');
                };
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = server_app_write_material';
                    };
                  });
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.Finished cf');
                };
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = server_app_read_material';
                    };
                  });
                CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf')
              ]) /\
        PNTSS.server_no_tail_two_handshake_install_cover e5' e6' /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_sent_seal_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events
            ch'
            selection'
            server_shared'
            sh')
          prefix_sent'
          prefix_received'
          model5' /\
        CS.conn_events_sent_seal_replay
          model5'
          (e5' :: e6' ::
            [
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert');
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv');
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf');
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material';
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf');
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material';
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf')
            ])
          suffix_sent'
          suffix_received'
          server.CS.cs_model
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
        cf
        server_app_write_material
        server_app_read_material
        model5
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice_from_ordered_witnesses
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
  (cf:M.finished)
  (server_app_write_material:CS.traffic_key_material)
  (server_app_read_material:CS.traffic_key_material)
  (model5:CS.connection_model)
  (prefix_sent:B.bytes)
  (prefix_received:B.bytes)
  (suffix_sent:B.bytes)
  (suffix_received:B.bytes)
  : Lemma
      (requires (
        let ordered_rest =
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
          ] in
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch
              selection
              server_shared
              sh)
            (e5 :: e6 :: ordered_rest) /\
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent suffix_sent) /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received suffix_received) /\
        CS.conn_events_sent_seal_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh)
          prefix_sent
          prefix_received
          model5 /\
        CS.conn_events_sent_seal_replay
          model5
          (e5 :: e6 :: ordered_rest)
          suffix_sent
          suffix_received
          server.CS.cs_model))
      (ensures
        server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
          server)
=
  let ordered_rest =
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
    ] in
  PWR.lemma_conn_events_sent_seal_replay_head
    model5
    e5
    (e6 :: ordered_rest)
    suffix_sent
    suffix_received
    server.CS.cs_model;
  eliminate exists
    (model6:CS.connection_model)
    delta0_sent
    delta0_received
    tail0_sent
    tail0_received.
    CS.legal_event model5 e5 /\
    CS.step_model model5 e5 == Some model6 /\
    CS.event_raw_delta_legal model5 e5 delta0_sent delta0_received /\
    CS.sent_event_nonempty_seal_projection model5 e5 delta0_sent /\
    Seq.equal suffix_sent (B.append delta0_sent tail0_sent) /\
    Seq.equal suffix_received (B.append delta0_received tail0_received) /\
    CS.conn_events_sent_seal_replay
      model6
      (e6 :: ordered_rest)
      tail0_sent
      tail0_received
      server.CS.cs_model
  returns
    server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
      server
  with _.
  (
    PWR.lemma_conn_events_sent_seal_replay_head
      model6
      e6
      ordered_rest
      tail0_sent
      tail0_received
      server.CS.cs_model;
    eliminate exists
      (model7:CS.connection_model)
      delta1_sent
      delta1_received
      tail1_sent
      tail1_received.
      CS.legal_event model6 e6 /\
      CS.step_model model6 e6 == Some model7 /\
      CS.event_raw_delta_legal model6 e6 delta1_sent delta1_received /\
      CS.sent_event_nonempty_seal_projection model6 e6 delta1_sent /\
      Seq.equal tail0_sent (B.append delta1_sent tail1_sent) /\
      Seq.equal tail0_received (B.append delta1_received tail1_received) /\
      CS.conn_events_sent_seal_replay
        model7
        ordered_rest
        tail1_sent
        tail1_received
        server.CS.cs_model
    returns
      server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
        server
    with _.
    (
      PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5 e6;
      assert (
        PNTSS.server_no_tail_handshake_write_install_event e5 \/
        PNTSS.server_no_tail_handshake_read_install_event e5);
      assert (
        PNTSS.server_no_tail_handshake_write_install_event e6 \/
        PNTSS.server_no_tail_handshake_read_install_event e6);
      lemma_server_handshake_install_event_deltas_empty
        model5
        e5
        delta0_sent
        delta0_received;
      lemma_server_handshake_install_event_deltas_empty
        model6
        e6
        delta1_sent
        delta1_received;
      Seq.lemma_eq_elim delta0_sent B.empty;
      Seq.lemma_eq_elim delta0_received B.empty;
      Seq.lemma_eq_elim delta1_sent B.empty;
      Seq.lemma_eq_elim delta1_received B.empty;
      lemma_server_handshake_install_cover_step_model_canonical_write_read
        model5
        model6
        model7
        e5
        e6;
      eliminate exists
        (server_material:CS.traffic_key_material)
        (server_read_material:CS.traffic_key_material)
        (server_after_write:CS.connection_model).
        (let server_write_install =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) in
         let server_read_install =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_read_material;
              };
            }) in
         CS.legal_event model5 server_write_install /\
         CS.step_model model5 server_write_install == Some server_after_write /\
         CS.legal_event server_after_write server_read_install /\
         CS.step_model server_after_write server_read_install == Some model7)
      returns
        server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
          server
      with _.
      (
        let server_write_install =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) in
        let server_read_install =
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_read_material;
              };
            }) in
        assert_norm (CS.event_raw_delta_legal
          server_after_write
          server_read_install
          delta1_sent
          delta1_received);
        assert_norm (CS.sent_event_nonempty_seal_projection
          server_after_write
          server_read_install
          delta1_sent);
        PWR.lemma_conn_events_sent_seal_replay_cons
          server_after_write
          server_read_install
          ordered_rest
          tail0_sent
          tail0_received
          server.CS.cs_model
          model7
          delta1_sent
          delta1_received
          tail1_sent
          tail1_received;
        assert_norm (CS.event_raw_delta_legal
          model5
          server_write_install
          delta0_sent
          delta0_received);
        assert_norm (CS.sent_event_nonempty_seal_projection
          model5
          server_write_install
          delta0_sent);
        PWR.lemma_conn_events_sent_seal_replay_cons
          model5
          server_write_install
          (server_read_install :: ordered_rest)
          suffix_sent
          suffix_received
          server.CS.cs_model
          server_after_write
          delta0_sent
          delta0_received
          tail0_sent
          tail0_received;
        assert (
          server_post_server_hello_ordered_sent_seal_replay_slice server);
        introduce exists
          (ch':M.client_hello)
          (selection':CS.server_handshake_selection)
          (server_shared':C.x25519_shared_secret)
          (sh':M.server_hello)
          (ee':M.encrypted_extensions)
          (cert':M.certificate_msg)
          (cv':M.certificate_verify)
          (sf':M.finished)
          (cf':M.finished)
          (server_material':CS.traffic_key_material)
          (server_read_material':CS.traffic_key_material)
          (server_app_write_material':CS.traffic_key_material)
          (server_app_read_material':CS.traffic_key_material)
          (model5':CS.connection_model)
          (server_after_write':CS.connection_model)
          (server_after_read':CS.connection_model)
          (prefix_sent':B.bytes)
          (prefix_received':B.bytes)
          (suffix_sent':B.bytes)
          (suffix_received':B.bytes).
          server_post_server_hello_ordered_sent_seal_replay_slice server /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append prefix_sent' suffix_sent') /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append prefix_received' suffix_received') /\
          CS.conn_events_sent_seal_replay
            (CS.initial_model server.CS.cs_model.CS.model_config)
            (PWSeg.server_cleartext_handshake_prefix_events
              ch'
              selection'
              server_shared'
              sh')
            prefix_sent'
            prefix_received'
            model5' /\
          CS.step_model
            model5'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = server_material';
                };
              })) == Some server_after_write' /\
          CS.step_model
            server_after_write'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_read_material';
                };
              })) == Some server_after_read' /\
          CS.conn_events_sent_seal_replay
            model5'
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = server_material';
                };
              }) ::
             CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_read_material';
                };
              }) ::
             [
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
               };
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.Certificate cert');
               };
               CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv');
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
               };
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.Finished sf');
               };
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeysForRole {
                   CS.install_role = CS.ServerEndpoint;
                   CS.install_payload = {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficWrite;
                     CS.install_material = server_app_write_material';
                   };
                 });
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.Finished cf');
               };
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeysForRole {
                   CS.install_role = CS.ServerEndpoint;
                   CS.install_payload = {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficRead;
                     CS.install_material = server_app_read_material';
                   };
                 });
               CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf')
             ])
            suffix_sent'
            suffix_received'
            server.CS.cs_model
        with
          ch
          selection
          server_shared
          sh
          ee
          cert
          cv
          sf
          cf
          server_material
          server_read_material
          server_app_write_material
          server_app_read_material
          model5
          server_after_write
          model7
          prefix_sent
          prefix_received
          suffix_sent
          suffix_received
        and ()
      )
    )
  )

let lemma_server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires server_post_server_hello_ordered_sent_seal_replay_slice server)
      (ensures
        server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
          server)
=
  eliminate exists
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
    (cf:M.finished)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    let ordered_rest =
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
      ] in
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: ordered_rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_sent_seal_replay
      model5
      (e5 :: e6 :: ordered_rest)
      suffix_sent
      suffix_received
      server.CS.cs_model
  returns
    server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
      server
  with _.
  (
    lemma_server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice_from_ordered_witnesses
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
      cf
      server_app_write_material
      server_app_read_material
      model5
      prefix_sent
      prefix_received
      suffix_sent
      suffix_received
  )

let lemma_server_after_handshake_installs_sent_seal_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires
        server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
          server)
      (ensures server_after_handshake_installs_sent_seal_replay_slice server)
=
  eliminate exists
    (ch:M.client_hello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:M.server_hello)
    (ee:M.encrypted_extensions)
    (cert:M.certificate_msg)
    (cv:M.certificate_verify)
    (sf:M.finished)
    (cf:M.finished)
    (server_material:CS.traffic_key_material)
    (server_read_material:CS.traffic_key_material)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (server_after_write:CS.connection_model)
    (server_after_read:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    (let server_write_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          };
        }) in
     let server_read_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_read_material;
          };
        }) in
     let ordered_rest =
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
      ] in
     server_post_server_hello_ordered_sent_seal_replay_slice server /\
     Seq.equal
       server.CS.cs_wire_log.CL.raw_sent
       (B.append prefix_sent suffix_sent) /\
     Seq.equal
       server.CS.cs_wire_log.CL.raw_received
       (B.append prefix_received suffix_received) /\
     CS.conn_events_sent_seal_replay
       (CS.initial_model server.CS.cs_model.CS.model_config)
       (PWSeg.server_cleartext_handshake_prefix_events
         ch
         selection
         server_shared
         sh)
       prefix_sent
       prefix_received
       model5 /\
     CS.step_model model5 server_write_install == Some server_after_write /\
     CS.step_model server_after_write server_read_install == Some server_after_read /\
     CS.conn_events_sent_seal_replay
       model5
       (server_write_install :: server_read_install :: ordered_rest)
       suffix_sent
       suffix_received
       server.CS.cs_model)
  returns server_after_handshake_installs_sent_seal_replay_slice server
  with _.
  (
    let server_write_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          };
        }) in
    let server_read_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_read_material;
          };
        }) in
    let ordered_rest =
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
      ] in
    PWR.lemma_conn_events_sent_seal_replay_head
      model5
      server_write_install
      (server_read_install :: ordered_rest)
      suffix_sent
      suffix_received
      server.CS.cs_model;
    eliminate exists
      (model_after_write:CS.connection_model)
      delta_write_sent
      delta_write_received
      tail_write_sent
      tail_write_received.
      CS.legal_event model5 server_write_install /\
      CS.step_model model5 server_write_install == Some model_after_write /\
      CS.event_raw_delta_legal model5 server_write_install delta_write_sent delta_write_received /\
      CS.sent_event_nonempty_seal_projection model5 server_write_install delta_write_sent /\
      Seq.equal suffix_sent (B.append delta_write_sent tail_write_sent) /\
      Seq.equal suffix_received (B.append delta_write_received tail_write_received) /\
      CS.conn_events_sent_seal_replay
        model_after_write
        (server_read_install :: ordered_rest)
        tail_write_sent
        tail_write_received
        server.CS.cs_model
    returns server_after_handshake_installs_sent_seal_replay_slice server
    with _.
    (
      assert (model_after_write == server_after_write);
      PWR.lemma_conn_events_sent_seal_replay_head
        server_after_write
        server_read_install
        ordered_rest
        tail_write_sent
        tail_write_received
        server.CS.cs_model;
      eliminate exists
        (model_after_read:CS.connection_model)
        delta_read_sent
        delta_read_received
        tail_read_sent
        tail_read_received.
        CS.legal_event server_after_write server_read_install /\
        CS.step_model server_after_write server_read_install == Some model_after_read /\
        CS.event_raw_delta_legal server_after_write server_read_install delta_read_sent delta_read_received /\
        CS.sent_event_nonempty_seal_projection server_after_write server_read_install delta_read_sent /\
        Seq.equal tail_write_sent (B.append delta_read_sent tail_read_sent) /\
        Seq.equal tail_write_received (B.append delta_read_received tail_read_received) /\
        CS.conn_events_sent_seal_replay
          model_after_read
          ordered_rest
          tail_read_sent
          tail_read_received
          server.CS.cs_model
      returns server_after_handshake_installs_sent_seal_replay_slice server
      with _.
      (
        assert (model_after_read == server_after_read);
        introduce exists
          (ch':M.client_hello)
          (selection':CS.server_handshake_selection)
          (server_shared':C.x25519_shared_secret)
          (sh':M.server_hello)
          (ee':M.encrypted_extensions)
          (cert':M.certificate_msg)
          (cv':M.certificate_verify)
          (sf':M.finished)
          (cf':M.finished)
          (server_material':CS.traffic_key_material)
          (server_read_material':CS.traffic_key_material)
          (server_app_write_material':CS.traffic_key_material)
          (server_app_read_material':CS.traffic_key_material)
          (model5':CS.connection_model)
          (server_after_write':CS.connection_model)
          (server_after_read':CS.connection_model)
          (installed_suffix_sent':B.bytes)
          (installed_suffix_received':B.bytes).
          (let server_write_install' =
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = server_material';
                };
              }) in
           let server_read_install' =
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_read_material';
                };
              }) in
           let ordered_rest' =
            [
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert');
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv');
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf');
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material';
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf');
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material';
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf')
            ] in
           CS.step_model model5' server_write_install' == Some server_after_write' /\
           CS.step_model server_after_write' server_read_install' == Some server_after_read' /\
           CS.conn_events_sent_seal_replay
             server_after_read'
             ordered_rest'
             installed_suffix_sent'
             installed_suffix_received'
             server.CS.cs_model)
        with
          ch
          selection
          server_shared
          sh
          ee
          cert
          cv
          sf
          cf
          server_material
          server_read_material
          server_app_write_material
          server_app_read_material
          model5
          server_after_write
          server_after_read
          tail_read_sent
          tail_read_received
        and ()
      )
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_sent_seal_replay_slice
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
      (ensures server_post_server_hello_sent_seal_replay_slice server)
=
  PNTSFS.lemma_clean16_no_tail_valid_byte_traces_server_encrypted_flight_staged_milestone
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
  lemma_server_post_server_hello_sent_seal_replay_slice_from_staged_milestone
    client
    server

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_sent_seal_replay_slice
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
      (ensures server_post_server_hello_ordered_sent_seal_replay_slice server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_sent_seal_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTPH.lemma_clean16_no_tail_valid_byte_traces_server_post_two_handshake_installs_tail_order
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_server_post_server_hello_ordered_sent_seal_replay_slice server

let lemma_server_post_server_hello_received_decode_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTSFS.clean16_server_encrypted_flight_staged_milestone client server /\
        CS.connection_state_received_decode_replay_consistent server)
      (ensures server_post_server_hello_received_decode_replay_slice server)
=
  assert (TLS13.Impl.Driver.PairingNoTailServerPostHelloShape.server_no_tail_post_server_hello_suffix_shape server);
  assert (PNTSS.server_no_tail_next_two_events_handshake_install_cover server);
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
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6
  returns server_post_server_hello_received_decode_replay_slice server
  with _.
  (
    let prefix =
      PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh in
    let suffix = e5 :: e6 :: rest in
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
    assert (prefix == ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: []);
    ListP.append_cons_l
      ev0
      (ev1 :: ev2 :: ev3 :: ev4 :: [])
      suffix;
    ListP.append_cons_l
      ev1
      (ev2 :: ev3 :: ev4 :: [])
      suffix;
    ListP.append_cons_l
      ev2
      (ev3 :: ev4 :: [])
      suffix;
    ListP.append_cons_l ev3 (ev4 :: []) suffix;
    ListP.append_cons_l ev4 [] suffix;
    ListP.append_nil_l suffix;
    assert (FStar.List.Tot.append prefix suffix ==
      ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: suffix);
    assert (server.CS.cs_event_log ==
      FStar.List.Tot.append prefix suffix);
    assert (
      CS.conn_events_received_decode_replay
        (CS.initial_model server.CS.cs_model.CS.model_config)
        (FStar.List.Tot.append prefix suffix)
        server.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        server.CS.cs_model);
    PWR.lemma_conn_events_received_decode_replay_append_split
      (CS.initial_model server.CS.cs_model.CS.model_config)
      prefix
      suffix
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists
      (model5:CS.connection_model)
      (prefix_sent:B.bytes)
      (prefix_received:B.bytes)
      (suffix_sent:B.bytes)
      (suffix_received:B.bytes).
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append prefix_sent suffix_sent) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append prefix_received suffix_received) /\
      CS.conn_events_received_decode_replay
        (CS.initial_model server.CS.cs_model.CS.model_config)
        prefix
        prefix_sent
        prefix_received
        model5 /\
      CS.conn_events_received_decode_replay
        model5
        suffix
        suffix_sent
        suffix_received
        server.CS.cs_model
    returns server_post_server_hello_received_decode_replay_slice server
    with _.
    (
      introduce exists
        (ch':M.client_hello)
        (selection':CS.server_handshake_selection)
        (server_shared':C.x25519_shared_secret)
        (sh':M.server_hello)
        (e5':CS.conn_event)
        (e6':CS.conn_event)
        (rest':list CS.conn_event)
        (model5':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch'
              selection'
              server_shared'
              sh')
            (e5' :: e6' :: rest') /\
        PNTSS.server_no_tail_two_handshake_install_cover e5' e6' /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_received_decode_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events
            ch'
            selection'
            server_shared'
            sh')
          prefix_sent'
          prefix_received'
          model5' /\
        CS.conn_events_received_decode_replay
          model5'
          (e5' :: e6' :: rest')
          suffix_sent'
          suffix_received'
          server.CS.cs_model
      with
        ch
        selection
        server_shared
        sh
        e5
        e6
        rest
        model5
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_server_post_server_hello_ordered_received_decode_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires
        server_post_server_hello_received_decode_replay_slice server /\
        PNTPH.server_no_tail_post_two_handshake_installs_tail_order server)
      (ensures server_post_server_hello_ordered_received_decode_replay_slice server)
=
  eliminate exists
    (ch:M.client_hello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:M.server_hello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (rest:list CS.conn_event)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_received_decode_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_received_decode_replay
      model5
      (e5 :: e6 :: rest)
      suffix_sent
      suffix_received
      server.CS.cs_model
  returns server_post_server_hello_ordered_received_decode_replay_slice server
  with _.
  (
    PNTPH.lemma_server_no_tail_post_two_handshake_installs_tail_order_for_split
      server
      ch
      selection
      server_shared
      sh
      e5
      e6
      rest;
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
    returns server_post_server_hello_ordered_received_decode_replay_slice server
    with _.
    (
      let ordered_rest =
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
        ] in
      assert (rest == ordered_rest);
      assert (e5 :: e6 :: rest == e5 :: e6 :: ordered_rest);
      introduce exists
        (ch':M.client_hello)
        (selection':CS.server_handshake_selection)
        (server_shared':C.x25519_shared_secret)
        (sh':M.server_hello)
        (e5':CS.conn_event)
        (e6':CS.conn_event)
        (ee':M.encrypted_extensions)
        (cert':M.certificate_msg)
        (cv':M.certificate_verify)
        (sf':M.finished)
        (cf':M.finished)
        (server_app_write_material':CS.traffic_key_material)
        (server_app_read_material':CS.traffic_key_material)
        (model5':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              ch'
              selection'
              server_shared'
              sh')
            (e5' :: e6' ::
              [
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Certificate cert');
                };
                CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv');
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Finished sf');
                };
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = server_app_write_material';
                    };
                  });
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.Finished cf');
                };
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = server_app_read_material';
                    };
                  });
                CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf')
              ]) /\
        PNTSS.server_no_tail_two_handshake_install_cover e5' e6' /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_received_decode_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events
            ch'
            selection'
            server_shared'
            sh')
          prefix_sent'
          prefix_received'
          model5' /\
        CS.conn_events_received_decode_replay
          model5'
          (e5' :: e6' ::
            [
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert');
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv');
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf');
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material';
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf');
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material';
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf')
            ])
          suffix_sent'
          suffix_received'
          server.CS.cs_model
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
        cf
        server_app_write_material
        server_app_read_material
        model5
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_received_decode_replay_slice
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
      (ensures server_post_server_hello_received_decode_replay_slice server)
=
  PNTSFS.lemma_clean16_no_tail_valid_byte_traces_server_encrypted_flight_staged_milestone
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
  lemma_server_post_server_hello_received_decode_replay_slice_from_staged_milestone
    client
    server

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_received_decode_replay_slice
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
      (ensures server_post_server_hello_ordered_received_decode_replay_slice server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTPH.lemma_clean16_no_tail_valid_byte_traces_server_post_two_handshake_installs_tail_order
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_server_post_server_hello_ordered_received_decode_replay_slice server

let lemma_client_post_derive_received_decode_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone
          client
          server /\
        CS.connection_state_received_decode_replay_consistent client)
      (ensures client_post_derive_received_decode_replay_slice client)
=
  assert (PNTCFS.paired_no_tail_client_finished_staged_milestone client server);
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
    (ce13:CS.conn_event)
    (ce14:CS.conn_event)
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
      ce13 ::
      ce14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5
  returns client_post_derive_received_decode_replay_slice client
  with _.
  (
    let prefix =
      PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared in
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
    let ev15 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) in
    let suffix =
      e4 ::
      e5 ::
      ev6 ::
      ev7 ::
      ev8 ::
      ev9 ::
      ev10 ::
      ev11 ::
      ev12 ::
      ce13 ::
      ce14 ::
      ev15 ::
      [] in
    assert (prefix == ev0 :: ev1 :: ev2 :: ev3 :: []);
    ListP.append_cons_l ev0 (ev1 :: ev2 :: ev3 :: []) suffix;
    ListP.append_cons_l ev1 (ev2 :: ev3 :: []) suffix;
    ListP.append_cons_l ev2 (ev3 :: []) suffix;
    ListP.append_cons_l ev3 [] suffix;
    ListP.append_nil_l suffix;
    assert (FStar.List.Tot.append prefix suffix ==
      ev0 :: ev1 :: ev2 :: ev3 :: suffix);
    assert (client.CS.cs_event_log ==
      FStar.List.Tot.append prefix suffix);
    assert (
      CS.conn_events_received_decode_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        (FStar.List.Tot.append prefix suffix)
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model);
    PWR.lemma_conn_events_received_decode_replay_append_split
      (CS.initial_model client.CS.cs_model.CS.model_config)
      prefix
      suffix
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model;
    eliminate exists
      (model4:CS.connection_model)
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
      CS.conn_events_received_decode_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        prefix
        prefix_sent
        prefix_received
        model4 /\
      CS.conn_events_received_decode_replay
        model4
        suffix
        suffix_sent
        suffix_received
        client.CS.cs_model
    returns client_post_derive_received_decode_replay_slice client
    with _.
    (
      introduce exists
        (start':CS.handshake_start)
        (ch':M.client_hello)
        (sh':M.server_hello)
        (client_shared':C.x25519_shared_secret)
        (e4':CS.conn_event)
        (e5':CS.conn_event)
        (rest':list CS.conn_event)
        (model4':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        client.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.client_cleartext_handshake_prefix_events
              start'
              ch'
              sh'
              client_shared')
            (e4' :: e5' :: rest') /\
        PCPS.client_no_tail_two_handshake_install_cover e4' e5' /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_received_decode_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (PWSeg.client_cleartext_handshake_prefix_events
            start'
            ch'
            sh'
            client_shared')
          prefix_sent'
          prefix_received'
          model4' /\
        CS.conn_events_received_decode_replay
          model4'
          (e4' :: e5' :: rest')
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
        (ev6 ::
         ev7 ::
         ev8 ::
         ev9 ::
         ev10 ::
         ev11 ::
         ev12 ::
         ce13 ::
         ce14 ::
         ev15 ::
         [])
        model4
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_client_post_derive_ordered_received_decode_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone
          client
          server /\
        CS.connection_state_received_decode_replay_consistent client)
      (ensures client_post_derive_ordered_received_decode_replay_slice client)
=
  assert (PNTCFS.paired_no_tail_client_finished_staged_milestone client server);
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
    (ce13:CS.conn_event)
    (ce14:CS.conn_event)
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
      ce13 ::
      ce14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover ce13 ce14
  returns client_post_derive_ordered_received_decode_replay_slice client
  with _.
  (
    let prefix =
      PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared in
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
    let ev15 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) in
    let ordered_rest =
      ev6 ::
      ev7 ::
      ev8 ::
      ev9 ::
      ev10 ::
      ev11 ::
      ev12 ::
      ce13 ::
      ce14 ::
      ev15 ::
      [] in
    let suffix = e4 :: e5 :: ordered_rest in
    assert (prefix == ev0 :: ev1 :: ev2 :: ev3 :: []);
    ListP.append_cons_l ev0 (ev1 :: ev2 :: ev3 :: []) suffix;
    ListP.append_cons_l ev1 (ev2 :: ev3 :: []) suffix;
    ListP.append_cons_l ev2 (ev3 :: []) suffix;
    ListP.append_cons_l ev3 [] suffix;
    ListP.append_nil_l suffix;
    assert (FStar.List.Tot.append prefix suffix ==
      ev0 :: ev1 :: ev2 :: ev3 :: suffix);
    assert (client.CS.cs_event_log ==
      FStar.List.Tot.append prefix suffix);
    assert (
      CS.conn_events_received_decode_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        (FStar.List.Tot.append prefix suffix)
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model);
    PWR.lemma_conn_events_received_decode_replay_append_split
      (CS.initial_model client.CS.cs_model.CS.model_config)
      prefix
      suffix
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model;
    eliminate exists
      (model4:CS.connection_model)
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
      CS.conn_events_received_decode_replay
        (CS.initial_model client.CS.cs_model.CS.model_config)
        prefix
        prefix_sent
        prefix_received
        model4 /\
      CS.conn_events_received_decode_replay
        model4
        suffix
        suffix_sent
        suffix_received
        client.CS.cs_model
    returns client_post_derive_ordered_received_decode_replay_slice client
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
        (model4':CS.connection_model)
        (prefix_sent':B.bytes)
        (prefix_received':B.bytes)
        (suffix_sent':B.bytes)
        (suffix_received':B.bytes).
        client.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.client_cleartext_handshake_prefix_events
              start'
              ch'
              sh'
              client_shared')
            (e4' :: e5' :: [
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert');
              };
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer');
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              };
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv');
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf');
              };
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf');
              e13';
              e14';
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf');
              }
            ]) /\
        PCPS.client_no_tail_two_handshake_install_cover e4' e5' /\
        PNTCAS.client_no_tail_application_install_cover e13' e14' /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent' suffix_sent') /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received' suffix_received') /\
        CS.conn_events_received_decode_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (PWSeg.client_cleartext_handshake_prefix_events
            start'
            ch'
            sh'
            client_shared')
          prefix_sent'
          prefix_received'
          model4' /\
        CS.conn_events_received_decode_replay
          model4'
          (e4' :: e5' :: [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert');
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer');
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv');
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf');
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf');
            e13';
            e14';
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf');
            }
          ])
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
        ce13
        ce14
        cf
        model4
        prefix_sent
        prefix_received
        suffix_sent
        suffix_received
      and ()
    )
  )

let lemma_client_after_handshake_installs_received_decode_replay_slice_from_ordered_witnesses
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
  (ce13:CS.conn_event)
  (ce14:CS.conn_event)
  (cf:M.finished)
  (model4:CS.connection_model)
  (suffix_sent:B.bytes)
  (suffix_received:B.bytes)
  : Lemma
      (requires
        (let ordered_rest =
          [
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
            ce13;
            ce14;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf);
            }
          ] in
         client.CS.cs_event_log ==
           FStar.List.Tot.append
             (PWSeg.client_cleartext_handshake_prefix_events
               start
               ch
               sh
               client_shared)
             (e4 :: e5 :: ordered_rest) /\
         PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
         PNTCAS.client_no_tail_application_install_cover ce13 ce14 /\
         CS.conn_events_received_decode_replay
           model4
           (e4 :: e5 :: ordered_rest)
           suffix_sent
           suffix_received
           client.CS.cs_model))
      (ensures client_after_handshake_installs_received_decode_replay_slice client)
=
  let ordered_rest =
    [
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
      ce13;
      ce14;
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }
    ] in
  eliminate exists
    (client_after_e4:CS.connection_model)
    delta4_sent
    delta4_received
    tail4_sent
    tail4_received.
    CS.legal_event model4 e4 /\
    CS.step_model model4 e4 == Some client_after_e4 /\
    CS.event_raw_delta_legal model4 e4 delta4_sent delta4_received /\
    CS.received_event_nonempty_decode_projection model4 e4 delta4_received /\
    Seq.equal suffix_sent (B.append delta4_sent tail4_sent) /\
    Seq.equal suffix_received (B.append delta4_received tail4_received) /\
    CS.conn_events_received_decode_replay
      client_after_e4
      (e5 :: ordered_rest)
      tail4_sent
      tail4_received
      client.CS.cs_model
  returns client_after_handshake_installs_received_decode_replay_slice client
  with _.
  (
    eliminate exists
      (client_after_installs:CS.connection_model)
      delta5_sent
      delta5_received
      tail5_sent
      tail5_received.
      CS.legal_event client_after_e4 e5 /\
      CS.step_model client_after_e4 e5 == Some client_after_installs /\
      CS.event_raw_delta_legal client_after_e4 e5 delta5_sent delta5_received /\
      CS.received_event_nonempty_decode_projection client_after_e4 e5 delta5_received /\
      Seq.equal tail4_sent (B.append delta5_sent tail5_sent) /\
      Seq.equal tail4_received (B.append delta5_received tail5_received) /\
      CS.conn_events_received_decode_replay
        client_after_installs
        ordered_rest
        tail5_sent
        tail5_received
        client.CS.cs_model
    returns client_after_handshake_installs_received_decode_replay_slice client
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
        (model4':CS.connection_model)
        (client_after_e4':CS.connection_model)
        (client_after_installs':CS.connection_model)
        (installed_suffix_sent':B.bytes)
        (installed_suffix_received':B.bytes).
        (let ordered_rest' =
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee');
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert');
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer');
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv');
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf');
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf');
            e13';
            e14';
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf');
            }
          ] in
         client.CS.cs_event_log ==
           FStar.List.Tot.append
             (PWSeg.client_cleartext_handshake_prefix_events
               start'
               ch'
               sh'
               client_shared')
             (e4' :: e5' :: ordered_rest') /\
         PCPS.client_no_tail_two_handshake_install_cover e4' e5' /\
         PNTCAS.client_no_tail_application_install_cover e13' e14' /\
         CS.step_model model4' e4' == Some client_after_e4' /\
         CS.step_model client_after_e4' e5' == Some client_after_installs' /\
         CS.conn_events_received_decode_replay
           client_after_installs'
           ordered_rest'
           installed_suffix_sent'
           installed_suffix_received'
           client.CS.cs_model)
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
        ce13
        ce14
        cf
        model4
        client_after_e4
        client_after_installs
        tail5_sent
        tail5_received
      and ()
    )
  )

let lemma_client_after_handshake_installs_received_decode_replay_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_post_derive_ordered_received_decode_replay_slice client)
      (ensures client_after_handshake_installs_received_decode_replay_slice client)
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
    (ce13:CS.conn_event)
    (ce14:CS.conn_event)
    (cf:M.finished)
    (model4:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    (let ordered_rest =
      [
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
        ce13;
        ce14;
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        }
      ] in
     client.CS.cs_event_log ==
       FStar.List.Tot.append
         (PWSeg.client_cleartext_handshake_prefix_events
           start
           ch
           sh
           client_shared)
         (e4 :: e5 :: ordered_rest) /\
     PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
     PNTCAS.client_no_tail_application_install_cover ce13 ce14 /\
     Seq.equal
       client.CS.cs_wire_log.CL.raw_sent
       (B.append prefix_sent suffix_sent) /\
     Seq.equal
       client.CS.cs_wire_log.CL.raw_received
       (B.append prefix_received suffix_received) /\
     CS.conn_events_received_decode_replay
       (CS.initial_model client.CS.cs_model.CS.model_config)
       (PWSeg.client_cleartext_handshake_prefix_events
         start
         ch
         sh
         client_shared)
       prefix_sent
       prefix_received
       model4 /\
     CS.conn_events_received_decode_replay
       model4
       (e4 :: e5 :: ordered_rest)
       suffix_sent
       suffix_received
       client.CS.cs_model)
  returns client_after_handshake_installs_received_decode_replay_slice client
  with _.
  (
    lemma_client_after_handshake_installs_received_decode_replay_slice_from_ordered_witnesses
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
      ce13
      ce14
      cf
      model4
      suffix_sent
      suffix_received
  )

let lemma_clean16_no_tail_valid_byte_traces_client_post_derive_received_decode_replay_slice
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
      (ensures client_post_derive_received_decode_replay_slice client)
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
  lemma_client_post_derive_received_decode_replay_slice_from_staged_milestone
    client
    server

let lemma_clean16_no_tail_valid_byte_traces_client_post_derive_ordered_received_decode_replay_slice
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
      (ensures client_post_derive_ordered_received_decode_replay_slice client)
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
  lemma_client_post_derive_ordered_received_decode_replay_slice_from_staged_milestone
    client
    server

let lemma_clean16_no_tail_valid_byte_traces_client_after_handshake_installs_received_decode_replay_slice
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
      (ensures client_after_handshake_installs_received_decode_replay_slice client)
=
  lemma_clean16_no_tail_valid_byte_traces_client_post_derive_ordered_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_client_after_handshake_installs_received_decode_replay_slice client

let lemma_server_encrypted_flight_staged_replay_fragment_from_normalized_replay_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w)
      (ensures
        exists r.
          server_encrypted_flight_staged_replay_fragment client server w r)
=
  assert (exists server_raw_sent server_raw_received client_raw_sent client_raw_received.
    normalized_replay_boundary_server_flight_inputs
      client
      server
      w
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received)
  by (
    Tac.norm
      [delta_only
        [`%PNB.paired_supported_normalized_replay_boundary_inputs;
         `%normalized_replay_boundary_server_flight_inputs]];
    Tac.smt ());
  eliminate exists
    (server_raw_sent:B.bytes)
    (server_raw_received:B.bytes)
    (client_raw_sent:B.bytes)
    (client_raw_received:B.bytes).
    normalized_replay_boundary_server_flight_inputs
      client
      server
      w
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
  returns
    exists r.
      server_encrypted_flight_staged_replay_fragment client server w r
  with _.
  (
    let server_rest =
      PWL.server_receive_client_finished_replay_events
        w.PCB.hcb_server_app_write_material
        w.PCB.hcb_received_msg4
        w.PCB.hcb_server_finished_rest in
    let client_rest =
      PWL.client_finished_replay_events
        w.PCB.hcb_verified_server_finished
        w.PCB.hcb_client_app_write_material
        w.PCB.hcb_client_app_read_material
        w.PCB.hcb_sent_msg4
        w.PCB.hcb_client_finished_rest in
    let r = {
      sfr_server_flight_rest = server_rest;
      sfr_client_flight_rest = client_rest;
      sfr_server_raw_sent = server_raw_sent;
      sfr_server_raw_received = server_raw_received;
      sfr_client_raw_sent = client_raw_sent;
      sfr_client_raw_received = client_raw_received;
      sfr_server_final = server.CS.cs_model;
      sfr_client_final = client.CS.cs_model;
    } in
    assert (server_encrypted_flight_staged_replay_fragment client server w r)
    by (
      Tac.norm
        [delta_only
          [`%PNB.paired_supported_normalized_replay_boundary_inputs;
           `%normalized_replay_boundary_server_flight_inputs;
           `%server_encrypted_flight_staged_replay_fragment;
           `%PWL.paired_protected_handshake_contiguous_replay_views;
           `%PWL.server_protected_handshake_contiguous_replay_events;
           `%PWL.client_protected_handshake_contiguous_replay_events;
           `%PWL.server_encrypted_flight_replay_events;
           `%PWL.client_receive_server_encrypted_flight_replay_events;
           `%PWL.server_receive_client_finished_replay_events;
           `%PWL.client_finished_replay_events]];
      Tac.smt ());
    introduce exists (r':server_flight_replay_witnesses).
      server_encrypted_flight_staged_replay_fragment client server w r'
    with r and ()
  )

let lemma_clean16_server_encrypted_flight_staged_replay_fragment_from_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        PNTSFS.clean16_server_encrypted_flight_staged_milestone
          client
          server /\
        clean16_server_encrypted_flight_semantic_replay_completion
          client
          server
          w)
      (ensures
        exists r.
          server_encrypted_flight_staged_replay_fragment client server w r)
=
  lemma_server_encrypted_flight_staged_replay_fragment_from_normalized_replay_boundary_inputs
    client
    server
    w

#pop-options
