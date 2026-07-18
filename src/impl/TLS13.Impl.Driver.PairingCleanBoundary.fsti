module TLS13.Impl.Driver.PairingCleanBoundary

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GFin  = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PR = TLS13.Impl.Driver.PairingProtectedReplay
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module R = TLS13.Record.Spec
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

noeq
type handshake_complete_boundary_witnesses = {
  hcb_client_ch: GCH.clientHello;
  hcb_server_ch: GCH.clientHello;
  hcb_client_sh: GSH.serverHello;
  hcb_server_sh: GSH.serverHello;
  hcb_client_ch_raw: B.bytes;
  hcb_server_ch_raw: B.bytes;
  hcb_client_sh_raw: B.bytes;
  hcb_server_sh_raw: B.bytes;
  hcb_start: CS.handshake_start;
  hcb_selection: CS.server_handshake_selection;
  hcb_server_shared: C.x25519_shared_secret;
  hcb_client_shared: C.x25519_shared_secret;
  hcb_server_model1: CS.connection_model;
  hcb_server_model2: CS.connection_model;
  hcb_server_model3: CS.connection_model;
  hcb_server_model4: CS.connection_model;
  hcb_server_model5: CS.connection_model;
  hcb_client_model1: CS.connection_model;
  hcb_client_model2: CS.connection_model;
  hcb_client_model3: CS.connection_model;
  hcb_client_model4: CS.connection_model;
  hcb_server_after_install: CS.connection_model;
  hcb_client_after_install: CS.connection_model;
  hcb_server_after0: CS.connection_model;
  hcb_client_after0: CS.connection_model;
  hcb_server_after1: CS.connection_model;
  hcb_client_after1: CS.connection_model;
  hcb_server_after_auth_skip: CS.connection_model;
  hcb_client_after_auth_skip: CS.connection_model;
  hcb_server_after2: CS.connection_model;
  hcb_client_after2: CS.connection_model;
  hcb_client_after_verify_skip: CS.connection_model;
  hcb_server_after3: CS.connection_model;
  hcb_client_after3: CS.connection_model;
  hcb_server_auth_skip: CS.local_event;
  hcb_client_auth_skip: CS.local_event;
  hcb_client_verify_skip: CS.local_event;
  hcb_server_material: CS.traffic_key_material;
  hcb_client_material: CS.traffic_key_material;
  hcb_sent_msg0: M.handshake_msg;
  hcb_received_msg0: M.handshake_msg;
  hcb_sent_msg1: M.handshake_msg;
  hcb_received_msg1: M.handshake_msg;
  hcb_sent_msg2: M.handshake_msg;
  hcb_received_msg2: M.handshake_msg;
  hcb_sent_msg3: M.handshake_msg;
  hcb_received_msg3: M.handshake_msg;
  hcb_verified_server_finished: GFin.finished;
  hcb_client_app_write_material: CS.traffic_key_material;
  hcb_client_app_read_material: CS.traffic_key_material;
  hcb_server_app_write_material: CS.traffic_key_material;
  hcb_sent_msg4: M.handshake_msg;
  hcb_received_msg4: M.handshake_msg;
  hcb_client_finished_rest: list CS.conn_event;
  hcb_server_finished_rest: list CS.conn_event;
  hcb_cf_client_after_verify: CS.connection_model;
  hcb_cf_client_after_app_write: CS.connection_model;
  hcb_cf_client_after_app_read: CS.connection_model;
  hcb_cf_server_after_app_write: CS.connection_model;
  hcb_cf_client_after_finished: CS.connection_model;
  hcb_cf_server_after_finished: CS.connection_model;
}

noextract
let paired_supported_handshake_complete_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:handshake_complete_boundary_witnesses)
  : prop =
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_suffix =
    PWL.server_protected_handshake_contiguous_replay_events
      w.hcb_server_material
      w.hcb_sent_msg0
      w.hcb_sent_msg1
      w.hcb_server_auth_skip
      w.hcb_sent_msg2
      w.hcb_sent_msg3
      w.hcb_server_app_write_material
      w.hcb_received_msg4
      w.hcb_server_finished_rest in
  let client_suffix =
    PWL.client_protected_handshake_contiguous_replay_events
      w.hcb_client_material
      w.hcb_received_msg0
      w.hcb_received_msg1
      w.hcb_client_auth_skip
      w.hcb_received_msg2
      w.hcb_client_verify_skip
      w.hcb_received_msg3
      w.hcb_verified_server_finished
      w.hcb_client_app_write_material
      w.hcb_client_app_read_material
      w.hcb_sent_msg4
      w.hcb_client_finished_rest in
  let server_prefix =
    PWSeg.server_cleartext_handshake_prefix_events
      w.hcb_client_ch
      w.hcb_selection
      w.hcb_server_shared
      w.hcb_server_sh in
  let client_prefix =
    PWSeg.client_cleartext_handshake_prefix_events
      w.hcb_start
      w.hcb_client_ch
      w.hcb_server_sh
      w.hcb_client_shared in
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some w.hcb_client_ch /\
  server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some w.hcb_server_ch /\
  client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    Some w.hcb_client_sh /\
  server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    Some w.hcb_server_sh /\
  w.hcb_server_ch == w.hcb_client_ch /\
  w.hcb_client_sh == w.hcb_server_sh /\
  WFL.supported_client_hello_wire_profile w.hcb_client_ch /\
  Seq.equal w.hcb_client_ch_raw w.hcb_server_ch_raw /\
  Seq.equal w.hcb_server_sh_raw w.hcb_client_sh_raw /\
  CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ClientHello w.hcb_client_ch))
    w.hcb_client_ch_raw /\
  CS.received_cleartext_tls_message_raw
    (M.TlsHandshake (M.ClientHello w.hcb_server_ch))
    w.hcb_server_ch_raw /\
  CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello w.hcb_server_sh))
    w.hcb_server_sh_raw /\
  CS.received_cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello w.hcb_client_sh))
    w.hcb_client_sh_raw /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  Seq.equal
    server.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received /\
  Seq.equal
    client.CS.cs_wire_log.CL.raw_sent
    server.CS.cs_wire_log.CL.raw_received /\
  server.CS.cs_event_log ==
    FStar.List.Tot.append server_prefix server_suffix /\
  client.CS.cs_event_log ==
    FStar.List.Tot.append client_prefix client_suffix /\
  TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent server /\
  TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent server /\
  TLS13.Spec.StateMachine.Replay.connection_state_sent_seal_replay_consistent client /\
  TLS13.Spec.StateMachine.Replay.connection_state_received_decode_replay_consistent client /\
  CS.step_model
    server_model0
    (CS.ConnLocalEvent CS.LocalStartServer) == Some w.hcb_server_model1 /\
  CS.step_model
    w.hcb_server_model1
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello w.hcb_client_ch);
    }) == Some w.hcb_server_model2 /\
  CS.step_model
    w.hcb_server_model2
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters w.hcb_selection)) ==
    Some w.hcb_server_model3 /\
  CS.step_model
    w.hcb_server_model3
    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret w.hcb_server_shared)) ==
    Some w.hcb_server_model4 /\
  CS.step_model
    w.hcb_server_model4
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello w.hcb_server_sh);
    }) == Some w.hcb_server_model5 /\
  CS.step_model
    client_model0
    (CS.ConnLocalEvent (CS.LocalStartHandshake w.hcb_start)) ==
    Some w.hcb_client_model1 /\
  CS.step_model
    w.hcb_client_model1
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello w.hcb_client_ch);
    }) == Some w.hcb_client_model2 /\
  CS.step_model
    w.hcb_client_model2
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello w.hcb_server_sh);
    }) == Some w.hcb_client_model3 /\
  CS.step_model
    w.hcb_client_model3
    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret w.hcb_client_shared)) ==
    Some w.hcb_client_model4 /\
  (match
    client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate,
    client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
    client.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
    client.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
    server.CS.cs_model.CS.model_handshake.CS.hs_client_finished
  with
  | Some client_ee, Some server_ee_msg,
    Some client_cert, Some server_cert_msg,
    Some client_cv, Some server_cv_msg,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    w.hcb_sent_msg0 == M.EncryptedExtensions server_ee_msg /\
    w.hcb_received_msg0 == M.EncryptedExtensions client_ee /\
    w.hcb_sent_msg1 == M.Certificate server_cert_msg /\
    w.hcb_received_msg1 == M.Certificate client_cert /\
    w.hcb_sent_msg2 == M.CertificateVerify server_cv_msg /\
    w.hcb_received_msg2 == M.CertificateVerify client_cv /\
    w.hcb_sent_msg3 == M.Finished server_sf /\
    w.hcb_received_msg3 == M.Finished client_sf /\
    w.hcb_sent_msg4 == M.Finished client_cf /\
    w.hcb_received_msg4 == M.Finished server_cf
  | _, _, _, _, _, _, _, _, _, _ ->
    False) /\
  (match
    w.hcb_server_model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
    w.hcb_client_model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
  with
  | Some server_secret, Some client_secret ->
    Seq.equal server_secret client_secret
  | _, _ ->
    False) /\
  Seq.equal
    w.hcb_server_model5.CS.model_handshake.CS.hs_transcript
    w.hcb_client_model4.CS.model_handshake.CS.hs_transcript /\
  PWL.local_event_does_not_install_record_keys w.hcb_server_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.hcb_client_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.hcb_client_verify_skip /\
  PWL.write_read_record_material_aligned
    w.hcb_client_model4
    w.hcb_server_model5 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_sent_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_received_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_sent_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_received_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_sent_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_received_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_sent_msg3 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_received_msg3 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_sent_msg4 /\
  PWL.protected_handshake_wire_round_trip_message w.hcb_received_msg4 /\
  CS.step_model
    w.hcb_server_model5
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.hcb_server_material;
        };
      })) == Some w.hcb_server_after_install /\
  CS.step_model
    w.hcb_client_model4
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.hcb_client_material;
      })) == Some w.hcb_client_after_install /\
  CS.step_model
    w.hcb_server_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.hcb_sent_msg0;
    }) == Some w.hcb_server_after0 /\
  CS.step_model
    w.hcb_client_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.hcb_received_msg0;
    }) == Some w.hcb_client_after0 /\
  w.hcb_server_after0.CS.model_record.CS.record_write ==
    R.next_seq w.hcb_server_after_install.CS.model_record.CS.record_write /\
  w.hcb_client_after0.CS.model_record.CS.record_read ==
    R.next_seq w.hcb_client_after_install.CS.model_record.CS.record_read /\
  CS.step_model
    w.hcb_server_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.hcb_sent_msg1;
    }) == Some w.hcb_server_after1 /\
  CS.step_model
    w.hcb_client_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.hcb_received_msg1;
    }) == Some w.hcb_client_after1 /\
  w.hcb_server_after1.CS.model_record.CS.record_write ==
    R.next_seq w.hcb_server_after0.CS.model_record.CS.record_write /\
  w.hcb_client_after1.CS.model_record.CS.record_read ==
    R.next_seq w.hcb_client_after0.CS.model_record.CS.record_read /\
  CS.step_model
    w.hcb_server_after1
    (CS.ConnLocalEvent w.hcb_server_auth_skip) ==
    Some w.hcb_server_after_auth_skip /\
  CS.step_model
    w.hcb_client_after1
    (CS.ConnLocalEvent w.hcb_client_auth_skip) ==
    Some w.hcb_client_after_auth_skip /\
  CS.step_model
    w.hcb_server_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.hcb_sent_msg2;
    }) == Some w.hcb_server_after2 /\
  CS.step_model
    w.hcb_client_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.hcb_received_msg2;
    }) == Some w.hcb_client_after2 /\
  w.hcb_server_after2.CS.model_record.CS.record_write ==
    R.next_seq w.hcb_server_after_auth_skip.CS.model_record.CS.record_write /\
  w.hcb_client_after2.CS.model_record.CS.record_read ==
    R.next_seq w.hcb_client_after_auth_skip.CS.model_record.CS.record_read /\
  CS.step_model
    w.hcb_client_after2
    (CS.ConnLocalEvent w.hcb_client_verify_skip) ==
    Some w.hcb_client_after_verify_skip /\
  CS.step_model
    w.hcb_server_after2
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.hcb_sent_msg3;
    }) == Some w.hcb_server_after3 /\
  CS.step_model
    w.hcb_client_after_verify_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.hcb_received_msg3;
    }) == Some w.hcb_client_after3 /\
  w.hcb_server_after3.CS.model_record.CS.record_write ==
    R.next_seq w.hcb_server_after2.CS.model_record.CS.record_write /\
  w.hcb_client_after3.CS.model_record.CS.record_read ==
    R.next_seq w.hcb_client_after_verify_skip.CS.model_record.CS.record_read /\
  CS.step_model
    w.hcb_client_after3
    (CS.ConnLocalEvent
      (CS.LocalVerifyFinished w.hcb_verified_server_finished)) ==
    Some w.hcb_cf_client_after_verify /\
  CS.step_model
    w.hcb_cf_client_after_verify
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = w.hcb_client_app_write_material;
      })) == Some w.hcb_cf_client_after_app_write /\
  CS.step_model
    w.hcb_cf_client_after_app_write
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.hcb_client_app_read_material;
      })) == Some w.hcb_cf_client_after_app_read /\
  CS.step_model
    w.hcb_server_after3
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.hcb_server_app_write_material;
        };
      })) == Some w.hcb_cf_server_after_app_write /\
  CS.step_model
    w.hcb_cf_client_after_app_read
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.hcb_sent_msg4;
    }) == Some w.hcb_cf_client_after_finished /\
  CS.step_model
    w.hcb_cf_server_after_app_write
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.hcb_received_msg4;
    }) == Some w.hcb_cf_server_after_finished

noextract
let paired_supported_handshake_complete_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists w.
    paired_supported_handshake_complete_boundary_inputs client server w

val lemma_client_server_application_record_material_agrees_from_clean_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_handshake_complete_boundary client server)
      (ensures
        TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
