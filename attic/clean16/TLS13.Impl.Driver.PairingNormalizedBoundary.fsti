module TLS13.Impl.Driver.PairingNormalizedBoundary

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PR = TLS13.Impl.Driver.PairingProtectedReplay
module PWL = TLS13.ConnectionState.ProtectedWireBase
module R = TLS13.Record.Spec
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

(**
  A parser-facing handshake-complete boundary.

  Unlike [PairingCleanBoundary.paired_supported_handshake_complete_boundary],
  this predicate never requires exact [GCH.clientHello] or [GSH.serverHello]
  record equality across endpoints.  The cleartext hellos are connected by raw
  bytes (which proves body-insensitive/wire-normalized hello agreement), and the
  protected flight is supplied as a replay view.  The replay view is what the
  lower protected-wire projection lemmas use to recover serialized-handshake
  equivalence for EncryptedExtensions/Certificate/CertificateVerify/Finished.
**)
noextract
let paired_supported_normalized_replay_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : prop =
  let client_ch = w.PCB.hcb_client_ch in
  let server_ch = w.PCB.hcb_server_ch in
  let client_sh = w.PCB.hcb_client_sh in
  let server_sh = w.PCB.hcb_server_sh in
  exists (server_raw_sent:B.bytes).
  exists (server_raw_received:B.bytes).
  exists (client_raw_sent:B.bytes).
  exists (client_raw_received:B.bytes).
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
    PWL.local_event_does_not_install_record_keys
      w.PCB.hcb_client_verify_skip /\
    PWL.write_read_record_material_aligned
      w.PCB.hcb_client_model4
      w.PCB.hcb_server_model5 /\
    Seq.equal server_raw_sent client_raw_received /\
    Seq.equal client_raw_sent server_raw_received /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg0 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg0 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg1 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg1 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg2 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg2 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg3 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg3 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg4 /\
    PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg4 /\
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
        CL.message_value =
          M.TlsHandshake w.PCB.hcb_received_msg0;
      }) == Some w.PCB.hcb_client_after0 /\
    w.PCB.hcb_server_after0.CS.model_record.CS.record_write ==
      R.next_seq
        w.PCB.hcb_server_after_install.CS.model_record.CS.record_write /\
    w.PCB.hcb_client_after0.CS.model_record.CS.record_read ==
      R.next_seq
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
        CL.message_value =
          M.TlsHandshake w.PCB.hcb_received_msg1;
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
        CL.message_value =
          M.TlsHandshake w.PCB.hcb_received_msg2;
      }) == Some w.PCB.hcb_client_after2 /\
    w.PCB.hcb_server_after2.CS.model_record.CS.record_write ==
      R.next_seq
        w.PCB.hcb_server_after_auth_skip.CS.model_record.CS.record_write /\
    w.PCB.hcb_client_after2.CS.model_record.CS.record_read ==
      R.next_seq
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
        CL.message_value =
          M.TlsHandshake w.PCB.hcb_received_msg3;
      }) == Some w.PCB.hcb_client_after3 /\
    w.PCB.hcb_server_after3.CS.model_record.CS.record_write ==
      R.next_seq w.PCB.hcb_server_after2.CS.model_record.CS.record_write /\
    w.PCB.hcb_client_after3.CS.model_record.CS.record_read ==
      R.next_seq
        w.PCB.hcb_client_after_verify_skip.CS.model_record.CS.record_read /\
    CS.step_model
      w.PCB.hcb_client_after3
      (CS.ConnLocalEvent
        (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished)) ==
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
      w.PCB.hcb_server_after3
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
        CL.message_value =
          M.TlsHandshake w.PCB.hcb_received_msg4;
      }) == Some w.PCB.hcb_cf_server_after_finished /\
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

noextract
let paired_supported_normalized_replay_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists w.
    paired_supported_normalized_replay_boundary_inputs client server w

val lemma_client_server_application_record_material_agrees_from_normalized_replay_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires paired_supported_normalized_replay_boundary client server)
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
