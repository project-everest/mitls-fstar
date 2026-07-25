module TLS13.Impl.Driver.PairingProtectedReplay

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
module PWCS = TLS13.ConnectionState.ProtectedWireConcreteSegmentation
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module PWS = TLS13.ConnectionState.ProtectedWireStaged
module R = TLS13.Record.Spec
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_contiguous_replay_views
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
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
  (verified_server_finished:GFin.finished)
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
        TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
          (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
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

let lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_staged_replays_v2
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
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
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  (client_finished_write_install_source:CS.connection_model)
  (client_finished_read_install_source:CS.connection_model)
  (client_finished_client_write_material:CS.traffic_key_material)
  (client_finished_server_read_material:CS.traffic_key_material)
  (client_finished_sender:CS.connection_model)
  (client_finished_receiver:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (client_finished_raw_sent:B.bytes)
  (client_finished_raw_received:B.bytes)
  (server_finished_raw_sent:B.bytes)
  (server_finished_raw_received:B.bytes)
  (client_finished_final:CS.connection_model)
  (server_finished_final:CS.connection_model)
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
        Seq.equal server_raw_sent client_raw_received /\
        PWL.protected_handshake_wire_round_trip_message sent_msg0 /\
        PWL.protected_handshake_wire_round_trip_message received_msg0 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg1 /\
        PWL.protected_handshake_wire_round_trip_message received_msg1 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg2 /\
        PWL.protected_handshake_wire_round_trip_message received_msg2 /\
        PWL.protected_handshake_wire_round_trip_message sent_msg3 /\
        PWL.protected_handshake_wire_round_trip_message received_msg3 /\
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          server_flight_sender
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: CS.ConnLocalEvent server_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
          server_flight_receiver
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: CS.ConnLocalEvent client_auth_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: CS.ConnLocalEvent client_verify_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg3;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material client_finished_client_write_material)
          (TLS13.Spec.StateMachine.KeyMaterial.record_material_of_traffic_material client_finished_server_read_material) /\
        CS.step_model
          client_finished_write_install_source
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_finished_client_write_material;
            })) == Some client_finished_sender /\
        CS.step_model
          client_finished_read_install_source
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = client_finished_server_read_material;
              };
            })) == Some client_finished_receiver /\
        Seq.equal client_finished_raw_sent server_finished_raw_received /\
        PWL.protected_handshake_wire_round_trip_message sent_msg4 /\
        PWL.protected_handshake_wire_round_trip_message received_msg4 /\
        CS.step_model
          client_finished_sender
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
          client_finished_receiver
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          client_finished_sender
          (CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished) ::
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
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake sent_msg4;
           } :: client_finished_rest)
          client_finished_raw_sent
          client_finished_raw_received
          client_finished_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
          client_finished_receiver
          (CS.ConnLocalEvent
             (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = {
                 CS.install_epoch = CS.TrafficApplication;
                 CS.install_direction = CS.TrafficWrite;
                 CS.install_material = server_app_write_material;
               };
             }) ::
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake received_msg4;
           } :: server_finished_rest)
          server_finished_raw_sent
          server_finished_raw_received
          server_finished_final)
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
=
  PWS.lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays_v2
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
    server_rest
    client_rest
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final
    client_finished_write_install_source
    client_finished_read_install_source
    client_finished_client_write_material
    client_finished_server_read_material
    client_finished_sender
    client_finished_receiver
    cf_client_after_verify
    cf_client_after_app_write
    cf_client_after_app_read
    cf_server_after_app_write
    cf_client_after_finished
    cf_server_after_finished
    verified_server_finished
    client_app_write_material
    client_app_read_material
    server_app_write_material
    sent_msg4
    received_msg4
    client_finished_rest
    server_finished_rest
    client_finished_raw_sent
    client_finished_raw_received
    server_finished_raw_sent
    server_finished_raw_received
    client_finished_final
    server_finished_final;
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

let lemma_client_server_application_record_material_agrees_from_cleartext_prefix_full_replays
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  (server_model0:CS.connection_model)
  (client_model0:CS.connection_model)
  (start:CS.handshake_start)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (server_model1:CS.connection_model)
  (server_model2:CS.connection_model)
  (server_model3:CS.connection_model)
  (server_model4:CS.connection_model)
  (server_model5:CS.connection_model)
  (client_model1:CS.connection_model)
  (client_model2:CS.connection_model)
  (client_model3:CS.connection_model)
  (client_model4:CS.connection_model)
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
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  : Lemma
      (requires (
        let server_suffix =
          PWL.server_protected_handshake_contiguous_replay_events
            server_material
            sent_msg0
            sent_msg1
            server_auth_skip
            sent_msg2
            sent_msg3
            server_app_write_material
            received_msg4
            server_finished_rest in
        let client_suffix =
          PWL.client_protected_handshake_contiguous_replay_events
            client_material
            received_msg0
            received_msg1
            client_auth_skip
            received_msg2
            client_verify_skip
            received_msg3
            verified_server_finished
            client_app_write_material
            client_app_read_material
            sent_msg4
            client_finished_rest in
        let server_prefix =
          PWSeg.server_cleartext_handshake_prefix_events
            client_ch
            selection
            server_shared
            server_sh in
        let client_prefix =
          PWSeg.client_cleartext_handshake_prefix_events
            start
            client_ch
            server_sh
            client_shared in
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        server_ch == client_ch /\
        client_sh == server_sh /\
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
        Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server /\
        CS.step_model
          server_model0
          (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1 /\
        CS.step_model
          server_model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          }) == Some server_model2 /\
        CS.step_model
          server_model2
          (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
          Some server_model3 /\
        CS.step_model
          server_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
          Some server_model4 /\
        CS.step_model
          server_model4
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
          }) == Some server_model5 /\
        CS.step_model
          client_model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
          Some client_model1 /\
        CS.step_model
          client_model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          }) == Some client_model2 /\
        CS.step_model
          client_model2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
          }) == Some client_model3 /\
        CS.step_model
          client_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
          Some client_model4 /\
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
          server_model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client_model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server_model5.CS.model_handshake.CS.hs_transcript
          client_model4.CS.model_handshake.CS.hs_transcript /\
        PWL.local_event_does_not_install_record_keys server_auth_skip /\
        PWL.local_event_does_not_install_record_keys client_auth_skip /\
        PWL.local_event_does_not_install_record_keys client_verify_skip /\
        PWL.write_read_record_material_aligned client_model4 server_model5 /\
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
          server_model5
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
          client_model4
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
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received /\
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          server_model0
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
          server_model0
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          client_model0
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
          client_model0
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final))
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
=
  PWCS.lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays_known_start
    server_model0
    client_model0
    start
    client_ch
    selection
    server_shared
    client_shared
    server_sh
    server_model1
    server_model2
    server_model3
    server_model4
    server_model5
    client_model1
    client_model2
    client_model3
    client_model4
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
    server_full_sent
    server_full_received
    client_full_sent
    client_full_received
    server_final
    client_final;
  eliminate exists
    (server_raw_sent:B.bytes)
    (server_raw_received:B.bytes)
    (client_raw_sent:B.bytes)
    (client_raw_received:B.bytes).
    Seq.equal server_raw_sent client_raw_received /\
    Seq.equal client_raw_sent server_raw_received /\
    PWL.paired_protected_handshake_contiguous_replay_views
      server_model5
      client_model4
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
      client_final
  returns
    TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
    TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
      (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
      (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  ( lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_contiguous_replay_views
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
      server_model5
      client_model4
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
      cf_server_after_finished )

let lemma_client_server_application_record_material_agrees_from_handshake_complete_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  (start:CS.handshake_start)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (client_shared:C.x25519_shared_secret)
  (server_model1:CS.connection_model)
  (server_model2:CS.connection_model)
  (server_model3:CS.connection_model)
  (server_model4:CS.connection_model)
  (server_model5:CS.connection_model)
  (client_model1:CS.connection_model)
  (client_model2:CS.connection_model)
  (client_model3:CS.connection_model)
  (client_model4:CS.connection_model)
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
  (verified_server_finished:GFin.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  : Lemma
      (requires (
        let server_model0 =
          CS.initial_model server.CS.cs_model.CS.model_config in
        let client_model0 =
          CS.initial_model client.CS.cs_model.CS.model_config in
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        server_ch == client_ch /\
        client_sh == server_sh /\
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
        Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server /\
        paired_handshake_complete_boundary_state_logs
          client
          server
          start
          client_ch
          selection
          server_shared
          client_shared
          server_sh
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
          received_msg4 /\
        CS.step_model
          server_model0
          (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1 /\
        CS.step_model
          server_model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          }) == Some server_model2 /\
        CS.step_model
          server_model2
          (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
          Some server_model3 /\
        CS.step_model
          server_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
          Some server_model4 /\
        CS.step_model
          server_model4
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
          }) == Some server_model5 /\
        CS.step_model
          client_model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
          Some client_model1 /\
        CS.step_model
          client_model1
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          }) == Some client_model2 /\
        CS.step_model
          client_model2
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
          }) == Some client_model3 /\
        CS.step_model
          client_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
          Some client_model4 /\
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
          server_model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client_model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server_model5.CS.model_handshake.CS.hs_transcript
          client_model4.CS.model_handshake.CS.hs_transcript /\
        PWL.local_event_does_not_install_record_keys server_auth_skip /\
        PWL.local_event_does_not_install_record_keys client_auth_skip /\
        PWL.local_event_does_not_install_record_keys client_verify_skip /\
        PWL.write_read_record_material_aligned client_model4 server_model5 /\
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
          server_model5
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
          client_model4
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
          }) == Some cf_server_after_finished))
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
=
  PWCS.lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_state_logs_known_start
    server
    client
    start
    client_ch
    selection
    server_shared
    client_shared
    server_sh
    server_model1
    server_model2
    server_model3
    server_model4
    server_model5
    client_model1
    client_model2
    client_model3
    client_model4
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
    []
    [];
  eliminate exists
    (server_raw_sent:B.bytes)
    (server_raw_received:B.bytes)
    (client_raw_sent:B.bytes)
    (client_raw_received:B.bytes).
    Seq.equal server_raw_sent client_raw_received /\
    Seq.equal client_raw_sent server_raw_received /\
    PWL.paired_protected_handshake_contiguous_replay_views
      server_model5
      client_model4
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
      []
      []
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
      server.CS.cs_model
      client.CS.cs_model
  returns
    TLS13.Spec.StateMachine.KeyMaterial.supported_profile_client_server_key_material_agrees client server /\
    TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
      (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ClientTraffic)
      client
      server /\
    TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees
      (TLS13.Spec.StateMachine.KeyIdentifiers.traffic_id CS.TrafficApplication CS.ServerTraffic)
      client
      server
  with _.
  ( lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_contiguous_replay_views
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
      server_model5
      client_model4
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
      []
      []
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
      server.CS.cs_model
      client.CS.cs_model
      cf_client_after_verify
      cf_client_after_app_write
      cf_client_after_app_read
      cf_server_after_app_write
      cf_client_after_finished
      cf_server_after_finished )
