module TLS13.ConnectionState.ProtectedWireStaged

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
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
  (client_finished_sender:CS.connection_model)
  (client_finished_receiver:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  (verified_server_finished:M.finished)
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
        (match
          client_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished
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
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        protected_handshake_wire_round_trip_message sent_msg3 /\
        protected_handshake_wire_round_trip_message received_msg3 /\
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
        CS.conn_events_sent_seal_replay
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
        CS.conn_events_received_decode_replay
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
        write_read_record_material_aligned
          client_finished_sender
          client_finished_receiver /\
        Seq.equal client_finished_raw_sent server_finished_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg4 /\
        protected_handshake_wire_round_trip_message received_msg4 /\
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
        CS.conn_events_sent_seal_replay
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
        CS.conn_events_received_decode_replay
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
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client_state
            server_state
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)

// v2: derive the ClientFinished write/read record alignment from explicit
// handshake write/read installs, instead of requiring that alignment as an
// input.  The server encrypted flight side already uses explicit server-write
// and client-read handshake installs, so this wrapper has no pre-install
// protected-record alignment requirement.  The remaining ClientFinished-side
// non-replay side condition is only that the explicit client-write and
// server-read handshake install materials agree at the record key/IV level.
val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays_v2
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
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
  (verified_server_finished:M.finished)
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
        (match
          client_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished
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
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        protected_handshake_wire_round_trip_message sent_msg3 /\
        protected_handshake_wire_round_trip_message received_msg3 /\
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
        CS.conn_events_sent_seal_replay
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
        CS.conn_events_received_decode_replay
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
        CS.record_key_iv_material_agrees
          (CS.record_material_of_traffic_material client_finished_client_write_material)
          (CS.record_material_of_traffic_material client_finished_server_read_material) /\
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
        protected_handshake_wire_round_trip_message sent_msg4 /\
        protected_handshake_wire_round_trip_message received_msg4 /\
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
        CS.conn_events_sent_seal_replay
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
        CS.conn_events_received_decode_replay
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
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client_state
            server_state
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)

// v3: derive the protected projection witnesses from replay slices that start
// after both server-flight handshake traffic directions have already been
// installed.  This is the schedule-insensitive shape needed by the clean16
// proof: the two handshake installs are legal only before the encrypted server
// flight, but their local ordering is not part of the protected wire evidence.
val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_installed_server_flight_replays
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  (server_flight_sender:CS.connection_model)
  (server_flight_receiver:CS.connection_model)
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
  (client_finished_sender:CS.connection_model)
  (client_finished_receiver:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  (verified_server_finished:M.finished)
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
        (match
          client_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished
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
        write_read_record_material_aligned
          server_flight_sender
          server_flight_receiver /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        protected_handshake_wire_round_trip_message sent_msg3 /\
        protected_handshake_wire_round_trip_message received_msg3 /\
        CS.step_model
          server_flight_sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        CS.step_model
          server_flight_receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.CS.model_record.CS.record_write ==
          R.next_seq server_flight_sender.CS.model_record.CS.record_write /\
        client_after0.CS.model_record.CS.record_read ==
          R.next_seq server_flight_receiver.CS.model_record.CS.record_read /\
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
        CS.conn_events_sent_seal_replay
          server_flight_sender
          (CS.ConnNetworkEvent {
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
        CS.conn_events_received_decode_replay
          server_flight_receiver
          (CS.ConnNetworkEvent {
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
        write_read_record_material_aligned
          client_finished_sender
          client_finished_receiver /\
        Seq.equal client_finished_raw_sent server_finished_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg4 /\
        protected_handshake_wire_round_trip_message received_msg4 /\
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
        CS.conn_events_sent_seal_replay
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
        CS.conn_events_received_decode_replay
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
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client_state
            server_state
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)

val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_staged_replays
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
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
        (match
          client_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished
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
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        write_read_record_material_aligned
          server_flight_receiver
          server_flight_sender /\
        Seq.equal server_raw_sent client_raw_received /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        protected_handshake_wire_round_trip_message sent_msg3 /\
        protected_handshake_wire_round_trip_message received_msg3 /\
        protected_handshake_wire_round_trip_message sent_msg4 /\
        protected_handshake_wire_round_trip_message received_msg4 /\
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
        CS.conn_events_sent_seal_replay
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
            } ::
            server_receive_client_finished_replay_events
              server_app_write_material
              received_msg4
              server_finished_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
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
            } ::
            client_finished_replay_events
              verified_server_finished
              client_app_write_material
              client_app_read_material
              sent_msg4
              client_finished_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        CS.conn_events_sent_seal_replay
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
            } ::
            client_finished_replay_events
              verified_server_finished
              client_app_write_material
              client_app_read_material
              sent_msg4
              client_finished_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        CS.conn_events_received_decode_replay
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
            } ::
            server_receive_client_finished_replay_events
              server_app_write_material
              received_msg4
              server_finished_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client_state
            server_state
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)

val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_replay_views
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
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
        (match
          client_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
          client_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
          server_state.CS.cs_model.CS.model_handshake.CS.hs_client_finished
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
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        write_read_record_material_aligned
          server_flight_receiver
          server_flight_sender /\
        Seq.equal server_raw_sent client_raw_received /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        protected_handshake_wire_round_trip_message sent_msg3 /\
        protected_handshake_wire_round_trip_message received_msg3 /\
        protected_handshake_wire_round_trip_message sent_msg4 /\
        protected_handshake_wire_round_trip_message received_msg4 /\
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
        paired_protected_handshake_contiguous_replay_views
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
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client_state
            server_state
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)
