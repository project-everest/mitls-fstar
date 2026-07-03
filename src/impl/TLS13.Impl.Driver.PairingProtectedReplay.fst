module TLS13.Impl.Driver.PairingProtectedReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Pairing = TLS13.Impl.Driver.Pairing
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWS = TLS13.ConnectionState.ProtectedWireStaged
module R = TLS13.Record.Spec
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_contiguous_replay_views
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:M.client_hello)
  (server_ch:M.client_hello)
  (client_sh:M.server_hello)
  (server_sh:M.server_hello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  (server_flight_sender:CS.connection_model)
  (server_flight_receiver:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (verified_server_finished:M.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        WFL.supported_client_hello_wire_profile client_ch /\
        Seq.equal client_ch_raw server_ch_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        W.parse_supported_server_hello
          (W.serialize_handshake (M.ServerHello server_sh)) == Some server_sh /\
        W.parse_supported_server_hello
          (W.serialize_handshake (M.ServerHello client_sh)) == Some client_sh /\
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
          sent_msg0 == M.EncryptedExtensions server_ee_msg /\
          received_msg0 == M.EncryptedExtensions client_ee /\
          sent_msg1 == M.Certificate server_cert_msg /\
          received_msg1 == M.Certificate client_cert /\
          sent_msg2 == M.CertificateVerify server_cv_msg /\
          received_msg2 == M.CertificateVerify client_cv /\
          sent_msg3 == M.Finished server_sf /\
          received_msg3 == M.Finished client_sf /\
          sent_msg4 == M.Finished client_cf /\
          received_msg4 == M.Finished server_cf
        | _, _, _, _, _, _, _, _, _, _ ->
          False) /\
        (match
          server_flight_sender.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          server_flight_receiver.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server_flight_sender.CS.model_handshake.CS.hs_transcript
          server_flight_receiver.CS.model_handshake.CS.hs_transcript /\
        PWL.local_event_does_not_install_record_keys server_auth_skip /\
        PWL.local_event_does_not_install_record_keys client_auth_skip /\
        PWL.local_event_does_not_install_record_keys client_verify_skip /\
        PWL.write_read_record_material_aligned
          server_flight_receiver
          server_flight_sender /\
        Seq.equal server_raw_sent client_raw_received /\
        Seq.equal client_raw_sent server_raw_received /\
        PWL.protected_handshake_wire_round_trip_message sent_msg0 /\
        PWL.protected_handshake_wire_round_trip_message received_msg0 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg1 /\
        PWL.protected_handshake_wire_round_trip_message received_msg1 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg2 /\
        PWL.protected_handshake_wire_round_trip_message received_msg2 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg3 /\
        PWL.protected_handshake_wire_round_trip_message received_msg3 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg4 /\
        PWL.protected_handshake_wire_round_trip_message received_msg4 /\
        CS.step_model
          server_flight_sender
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after_install /\
        CS.step_model
          server_flight_receiver
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after_install /\
        CS.step_model
          server_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          client_after_install
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.CS.model_record.CS.record_write ==
          R.next_seq server_after_install.CS.model_record.CS.record_write /\
        client_after0.CS.model_record.CS.record_read ==
          R.next_seq client_after_install.CS.model_record.CS.record_read /\
        CS.step_model
          server_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        CS.step_model
          client_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        server_after1.CS.model_record.CS.record_write ==
          R.next_seq server_after0.CS.model_record.CS.record_write /\
        client_after1.CS.model_record.CS.record_read ==
          R.next_seq client_after0.CS.model_record.CS.record_read /\
        CS.step_model server_after1 (CS.ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        CS.step_model
          server_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_auth_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        server_after2.CS.model_record.CS.record_write ==
          R.next_seq server_after_auth_skip.CS.model_record.CS.record_write /\
        client_after2.CS.model_record.CS.record_read ==
          R.next_seq client_after_auth_skip.CS.model_record.CS.record_read /\
        CS.step_model client_after2 (CS.ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        CS.step_model
          server_after2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        CS.step_model
          client_after_verify_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        server_after3.CS.model_record.CS.record_write ==
          R.next_seq server_after2.CS.model_record.CS.record_write /\
        client_after3.CS.model_record.CS.record_read ==
          R.next_seq client_after_verify_skip.CS.model_record.CS.record_read /\
        CS.step_model
          client_after3
          (CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished)) ==
          Some cf_client_after_verify /\
        CS.step_model
          cf_client_after_verify
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_app_write_material;
            })) == Some cf_client_after_app_write /\
        CS.step_model
          cf_client_after_app_write
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_app_read_material;
            })) == Some cf_client_after_app_read /\
        CS.step_model
          server_after3
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            })) == Some cf_server_after_app_write /\
        CS.step_model
          cf_client_after_app_read
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg4;
          }) == Some cf_client_after_finished /\
        CS.step_model
          cf_server_after_app_write
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg4;
          }) == Some cf_server_after_finished /\
        PWL.paired_protected_handshake_contiguous_replay_views
          server_flight_sender
          server_flight_receiver
          server_material
          client_material
          sent_msg0
          received_msg0
          sent_msg1
          received_msg1
          server_auth_skip
          client_auth_skip
          sent_msg2
          received_msg2
          client_verify_skip
          sent_msg3
          received_msg3
          verified_server_finished
          client_app_write_material
          client_app_read_material
          server_app_write_material
          sent_msg4
          received_msg4
          client_finished_rest
          server_finished_rest
          server_raw_sent
          server_raw_received
          client_raw_sent
          client_raw_received
          server_final
          client_final)
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
  PWS.lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_replay_views
    client
    server
    server_flight_sender
    server_flight_receiver
    server_after_install
    client_after_install
    server_after0
    client_after0
    server_after1
    client_after1
    server_after_auth_skip
    client_after_auth_skip
    server_after2
    client_after2
    client_after_verify_skip
    server_after3
    client_after3
    server_auth_skip
    client_auth_skip
    client_verify_skip
    server_material
    client_material
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    sent_msg2
    received_msg2
    sent_msg3
    received_msg3
    verified_server_finished
    client_app_write_material
    client_app_read_material
    server_app_write_material
    sent_msg4
    received_msg4
    client_finished_rest
    server_finished_rest
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final
    cf_client_after_verify
    cf_client_after_app_write
    cf_client_after_app_read
    cf_server_after_app_write
    cf_client_after_finished
    cf_server_after_finished;
  Pairing.lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projection_witnesses
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw
