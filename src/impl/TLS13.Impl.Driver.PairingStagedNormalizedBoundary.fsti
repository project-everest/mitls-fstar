module TLS13.Impl.Driver.PairingStagedNormalizedBoundary

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PR = TLS13.Impl.Driver.PairingProtectedReplay
module PWL = TLS13.ConnectionState.ProtectedWireBase
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

(**
  Staged-v2 variant of [PairingNormalizedBoundary].

  The older normalized boundary packages a single contiguous protected replay
  view and still includes the stale pre-install client-write/server-read record
  alignment.  This boundary instead exposes exactly the staged-v2 premises used
  by [PairingProtectedReplay]: one replay slice for the server encrypted flight,
  and a separate replay slice for ClientFinished after explicit client-handshake
  write and server-handshake read installs.
**)

noeq
type staged_replay_witnesses = {
  snb_server_flight_rest: list CS.conn_event;
  snb_client_flight_rest: list CS.conn_event;
  snb_server_raw_sent: B.bytes;
  snb_server_raw_received: B.bytes;
  snb_client_raw_sent: B.bytes;
  snb_client_raw_received: B.bytes;
  snb_server_final: CS.connection_model;
  snb_client_final: CS.connection_model;
  snb_client_finished_write_install_source: CS.connection_model;
  snb_client_finished_read_install_source: CS.connection_model;
  snb_client_finished_client_write_material: CS.traffic_key_material;
  snb_client_finished_server_read_material: CS.traffic_key_material;
  snb_client_finished_sender: CS.connection_model;
  snb_client_finished_receiver: CS.connection_model;
  snb_client_finished_raw_sent: B.bytes;
  snb_client_finished_raw_received: B.bytes;
  snb_server_finished_raw_sent: B.bytes;
  snb_server_finished_raw_received: B.bytes;
  snb_client_finished_final: CS.connection_model;
  snb_server_finished_final: CS.connection_model;
}

noextract
let paired_supported_normalized_staged_replay_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (s:staged_replay_witnesses)
  : prop =
  let client_ch = w.PCB.hcb_client_ch in
  let server_ch = w.PCB.hcb_server_ch in
  let client_sh = w.PCB.hcb_client_sh in
  let server_sh = w.PCB.hcb_server_sh in
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some client_ch /\
  server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some server_ch /\
  client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    Some client_sh /\
  server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    Some server_sh /\
  WFL.supported_client_hello_wire_profile client_ch /\
  Seq.equal w.PCB.hcb_client_ch_raw w.PCB.hcb_server_ch_raw /\
  Seq.equal w.PCB.hcb_server_sh_raw w.PCB.hcb_client_sh_raw /\
  CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ClientHello client_ch))
    w.PCB.hcb_client_ch_raw /\
  CS.received_cleartext_tls_message_raw
    (M.TlsHandshake (M.ClientHello server_ch))
    w.PCB.hcb_server_ch_raw /\
  CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello server_sh))
    w.PCB.hcb_server_sh_raw /\
  CS.received_cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello client_sh))
    w.PCB.hcb_client_sh_raw /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
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
    w.PCB.hcb_sent_msg0 == M.EncryptedExtensions server_ee_msg /\
    w.PCB.hcb_received_msg0 == M.EncryptedExtensions client_ee /\
    w.PCB.hcb_sent_msg1 == M.Certificate server_cert_msg /\
    w.PCB.hcb_received_msg1 == M.Certificate client_cert /\
    w.PCB.hcb_sent_msg2 == M.CertificateVerify server_cv_msg /\
    w.PCB.hcb_received_msg2 == M.CertificateVerify client_cv /\
    w.PCB.hcb_sent_msg3 == M.Finished server_sf /\
    w.PCB.hcb_received_msg3 == M.Finished client_sf /\
    w.PCB.hcb_sent_msg4 == M.Finished client_cf /\
    w.PCB.hcb_received_msg4 == M.Finished server_cf
  | _, _, _, _, _, _, _, _, _, _ ->
    False) /\
  (match
    w.PCB.hcb_server_model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
    w.PCB.hcb_client_model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
  with
  | Some server_secret, Some client_secret ->
    Seq.equal server_secret client_secret
  | _, _ ->
    False) /\
  Seq.equal
    w.PCB.hcb_server_model5.CS.model_handshake.CS.hs_transcript
    w.PCB.hcb_client_model4.CS.model_handshake.CS.hs_transcript /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_server_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_verify_skip /\
  Seq.equal s.snb_server_raw_sent s.snb_client_raw_received /\
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
    TLS13.Record.Spec.next_seq
      w.PCB.hcb_server_after_install.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after0.CS.model_record.CS.record_read ==
    TLS13.Record.Spec.next_seq
      w.PCB.hcb_client_after_install.CS.model_record.CS.record_read /\
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
    TLS13.Record.Spec.next_seq w.PCB.hcb_server_after0.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after1.CS.model_record.CS.record_read ==
    TLS13.Record.Spec.next_seq w.PCB.hcb_client_after0.CS.model_record.CS.record_read /\
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
    TLS13.Record.Spec.next_seq
      w.PCB.hcb_server_after_auth_skip.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after2.CS.model_record.CS.record_read ==
    TLS13.Record.Spec.next_seq
      w.PCB.hcb_client_after_auth_skip.CS.model_record.CS.record_read /\
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
    TLS13.Record.Spec.next_seq w.PCB.hcb_server_after2.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after3.CS.model_record.CS.record_read ==
    TLS13.Record.Spec.next_seq
      w.PCB.hcb_client_after_verify_skip.CS.model_record.CS.record_read /\
  TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
    w.PCB.hcb_server_model5
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_material;
        };
      }) :: CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg0;
      } :: CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg1;
      } :: CS.ConnLocalEvent w.PCB.hcb_server_auth_skip ::
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg2;
      } :: CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg3;
      } :: s.snb_server_flight_rest)
    s.snb_server_raw_sent
    s.snb_server_raw_received
    s.snb_server_final /\
  TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
    w.PCB.hcb_client_model4
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_material;
      }) :: CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg0;
      } :: CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg1;
      } :: CS.ConnLocalEvent w.PCB.hcb_client_auth_skip ::
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg2;
      } :: CS.ConnLocalEvent w.PCB.hcb_client_verify_skip ::
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg3;
      } :: s.snb_client_flight_rest)
    s.snb_client_raw_sent
    s.snb_client_raw_received
    s.snb_client_final /\
  TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees
    (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material s.snb_client_finished_client_write_material)
    (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material s.snb_client_finished_server_read_material) /\
  CS.step_model
    s.snb_client_finished_write_install_source
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = s.snb_client_finished_client_write_material;
      })) == Some s.snb_client_finished_sender /\
  CS.step_model
    s.snb_client_finished_read_install_source
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = s.snb_client_finished_server_read_material;
        };
      })) == Some s.snb_client_finished_receiver /\
  Seq.equal s.snb_client_finished_raw_sent s.snb_server_finished_raw_received /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg4 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg4 /\
  CS.step_model
    s.snb_client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished)) ==
    Some w.PCB.hcb_cf_client_after_verify /\
  CS.step_model
    w.PCB.hcb_cf_client_after_verify
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = w.PCB.hcb_client_app_write_material;
      })) == Some w.PCB.hcb_cf_client_after_app_write /\
  CS.step_model
    w.PCB.hcb_cf_client_after_app_write
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_app_read_material;
      })) == Some w.PCB.hcb_cf_client_after_app_read /\
  CS.step_model
    s.snb_client_finished_receiver
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_app_write_material;
        };
      })) == Some w.PCB.hcb_cf_server_after_app_write /\
  CS.step_model
    w.PCB.hcb_cf_client_after_app_read
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg4;
    }) == Some w.PCB.hcb_cf_client_after_finished /\
  CS.step_model
    w.PCB.hcb_cf_server_after_app_write
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg4;
    }) == Some w.PCB.hcb_cf_server_after_finished /\
  TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
    s.snb_client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished) ::
     CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficWrite;
         CS.install_material = w.PCB.hcb_client_app_write_material;
       }) ::
     CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficRead;
         CS.install_material = w.PCB.hcb_client_app_read_material;
       }) ::
     CS.ConnNetworkEvent {
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg4;
     } :: w.PCB.hcb_client_finished_rest)
    s.snb_client_finished_raw_sent
    s.snb_client_finished_raw_received
    s.snb_client_finished_final /\
  TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
    s.snb_client_finished_receiver
    (CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeysForRole {
         CS.install_role = CS.ServerEndpoint;
         CS.install_payload = {
           CS.install_epoch = CS.TrafficApplication;
           CS.install_direction = CS.TrafficWrite;
           CS.install_material = w.PCB.hcb_server_app_write_material;
         };
       }) ::
     CS.ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg4;
     } :: w.PCB.hcb_server_finished_rest)
    s.snb_server_finished_raw_sent
    s.snb_server_finished_raw_received
    s.snb_server_finished_final

noextract
let paired_supported_normalized_staged_replay_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists w s.
    paired_supported_normalized_staged_replay_boundary_inputs client server w s

(**
  Corrected projection-facing boundary.

  The staged-v2 boundary above is still useful for legacy callers that can
  provide its exact replay schedule, but its ClientFinished slice installs the
  client-handshake write key and server-handshake read key immediately before
  ClientFinished.  Those installs are not legal that late in the real clean16
  traces: both must happen before the server encrypted flight.  This boundary
  records the schedule-insensitive target used by the normalized pairing theorem:
  normalized cleartext/raw agreement plus already-derived protected projection
  witnesses.
**)
noeq
type normalized_projection_boundary_witnesses = {
  npb_client_ch: GCH.clientHello;
  npb_server_ch: GCH.clientHello;
  npb_client_sh: GSH.serverHello;
  npb_server_sh: GSH.serverHello;
  npb_client_ch_raw: B.bytes;
  npb_server_ch_raw: B.bytes;
  npb_client_sh_raw: B.bytes;
  npb_server_sh_raw: B.bytes;
}

noextract
let paired_supported_normalized_projection_boundary_cleartext_core_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:normalized_projection_boundary_witnesses)
  : prop =
  let client_ch = w.npb_client_ch in
  let server_ch = w.npb_server_ch in
  let client_sh = w.npb_client_sh in
  let server_sh = w.npb_server_sh in
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
   Some client_ch /\
  server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
   Some server_ch /\
  client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
   Some client_sh /\
  server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
   Some server_sh /\
  WFL.supported_client_hello_wire_profile client_ch /\
  Seq.equal w.npb_client_ch_raw w.npb_server_ch_raw /\
  Seq.equal w.npb_server_sh_raw w.npb_client_sh_raw /\
  CS.cleartext_tls_message_raw
   (M.TlsHandshake (M.ClientHello client_ch))
   w.npb_client_ch_raw /\
  CS.received_cleartext_tls_message_raw
   (M.TlsHandshake (M.ClientHello server_ch))
   w.npb_server_ch_raw /\
  CS.cleartext_tls_message_raw
   (M.TlsHandshake (M.ServerHello server_sh))
   w.npb_server_sh_raw /\
  CS.received_cleartext_tls_message_raw
   (M.TlsHandshake (M.ServerHello client_sh))
   w.npb_client_sh_raw /\
  WFL.paired_cleartext_hello_key_shares client server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
   client
   server

noextract
let paired_supported_normalized_projection_boundary_cleartext_core
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists w.
   paired_supported_normalized_projection_boundary_cleartext_core_inputs
     client
     server
     w

noextract
let paired_supported_normalized_projection_boundary_core_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:normalized_projection_boundary_witnesses)
  : prop =
  paired_supported_normalized_projection_boundary_cleartext_core_inputs
   client
   server
   w /\
  Pairing.paired_protected_handshake_event_projection_pair_witnesses
   client
   server

noextract
let paired_supported_normalized_projection_boundary_core
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists w.
   paired_supported_normalized_projection_boundary_core_inputs client server w

val lemma_client_server_application_record_material_agrees_from_normalized_projection_boundary_core
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
     (requires paired_supported_normalized_projection_boundary_core client server)
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

noextract
let paired_supported_normalized_projection_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : prop =
  let client_ch = w.PCB.hcb_client_ch in
  let server_ch = w.PCB.hcb_server_ch in
  let client_sh = w.PCB.hcb_client_sh in
  let server_sh = w.PCB.hcb_server_sh in
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some client_ch /\
  server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
    Some server_ch /\
  client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    Some client_sh /\
  server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
    Some server_sh /\
  WFL.supported_client_hello_wire_profile client_ch /\
  Seq.equal w.PCB.hcb_client_ch_raw w.PCB.hcb_server_ch_raw /\
  Seq.equal w.PCB.hcb_server_sh_raw w.PCB.hcb_client_sh_raw /\
  CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ClientHello client_ch))
    w.PCB.hcb_client_ch_raw /\
  CS.received_cleartext_tls_message_raw
    (M.TlsHandshake (M.ClientHello server_ch))
    w.PCB.hcb_server_ch_raw /\
  CS.cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello server_sh))
    w.PCB.hcb_server_sh_raw /\
  CS.received_cleartext_tls_message_raw
    (M.TlsHandshake (M.ServerHello client_sh))
    w.PCB.hcb_client_sh_raw /\
  WFL.paired_cleartext_hello_key_shares client server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  Pairing.paired_protected_handshake_event_projection_pair_witnesses
    client
    server

noextract
let paired_supported_normalized_projection_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists w.
    paired_supported_normalized_projection_boundary_inputs client server w

val lemma_client_server_application_record_material_agrees_from_normalized_projection_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_normalized_projection_boundary client server)
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

val lemma_client_server_application_record_material_agrees_from_normalized_staged_replay_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_normalized_staged_replay_boundary client server)
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
