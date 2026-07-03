module TLS13.ConnectionState.ProtectedWireStaged

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module WU = TLS13.Wire.Spec.Reveal.Util

open TLS13.Spec.ConnectionState
open TLS13.ConnectionState.ProtectedWireBase
open TLS13.ConnectionState.ProtectedWireProjection
open TLS13.ConnectionState.ProtectedWireServerFlight
open TLS13.ConnectionState.ProtectedWireClientFinished

#push-options "--split_queries always --z3rlimit 10"
let lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays
  (client_state:connection_state)
  (server_state:connection_state)
  (server_flight_sender:connection_model)
  (server_flight_receiver:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (server_rest:list conn_event)
  (client_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  (client_finished_sender:connection_model)
  (client_finished_receiver:connection_model)
  (cf_client_after_verify:connection_model)
  (cf_client_after_app_write:connection_model)
  (cf_client_after_app_read:connection_model)
  (cf_server_after_app_write:connection_model)
  (cf_client_after_finished:connection_model)
  (cf_server_after_finished:connection_model)
  (verified_server_finished:M.finished)
  (client_app_write_material:traffic_key_material)
  (client_app_read_material:traffic_key_material)
  (server_app_write_material:traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list conn_event)
  (server_finished_rest:list conn_event)
  (client_finished_raw_sent:B.bytes)
  (client_finished_raw_received:B.bytes)
  (server_finished_raw_sent:B.bytes)
  (server_finished_raw_received:B.bytes)
  (client_finished_final:connection_model)
  (server_finished_final:connection_model)
  : Lemma
      (requires
        (match
          client_state.cs_model.model_handshake.hs_encrypted_extensions,
          server_state.cs_model.model_handshake.hs_encrypted_extensions,
          client_state.cs_model.model_handshake.hs_certificate,
          server_state.cs_model.model_handshake.hs_certificate,
          client_state.cs_model.model_handshake.hs_certificate_verify,
          server_state.cs_model.model_handshake.hs_certificate_verify,
          client_state.cs_model.model_handshake.hs_server_finished,
          server_state.cs_model.model_handshake.hs_server_finished,
          client_state.cs_model.model_handshake.hs_client_finished,
          server_state.cs_model.model_handshake.hs_client_finished
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
          server_flight_sender.model_handshake.hs_keys.ks_handshake_secret,
          server_flight_receiver.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server_flight_sender.model_handshake.hs_transcript
          server_flight_receiver.model_handshake.hs_transcript /\
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
        step_model
          server_flight_sender
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            })) == Some server_after_install /\
        step_model
          server_flight_receiver
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after_install /\
        step_model
          server_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some server_after0 /\
        step_model
          client_after_install
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some client_after0 /\
        server_after0.model_record.record_write ==
          R.next_seq server_after_install.model_record.record_write /\
        client_after0.model_record.record_read ==
          R.next_seq client_after_install.model_record.record_read /\
        step_model
          server_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some server_after1 /\
        step_model
          client_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some client_after1 /\
        server_after1.model_record.record_write ==
          R.next_seq server_after0.model_record.record_write /\
        client_after1.model_record.record_read ==
          R.next_seq client_after0.model_record.record_read /\
        step_model server_after1 (ConnLocalEvent server_auth_skip) ==
          Some server_after_auth_skip /\
        step_model client_after1 (ConnLocalEvent client_auth_skip) ==
          Some client_after_auth_skip /\
        step_model
          server_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        step_model
          client_after_auth_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        server_after2.model_record.record_write ==
          R.next_seq server_after_auth_skip.model_record.record_write /\
        client_after2.model_record.record_read ==
          R.next_seq client_after_auth_skip.model_record.record_read /\
        step_model client_after2 (ConnLocalEvent client_verify_skip) ==
          Some client_after_verify_skip /\
        step_model
          server_after2
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg3;
          }) == Some server_after3 /\
        step_model
          client_after_verify_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg3;
          }) == Some client_after3 /\
        server_after3.model_record.record_write ==
          R.next_seq server_after2.model_record.record_write /\
        client_after3.model_record.record_read ==
          R.next_seq client_after_verify_skip.model_record.record_read /\
        conn_events_sent_seal_replay
          server_flight_sender
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg1;
            } :: ConnLocalEvent server_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg3;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        conn_events_received_decode_replay
          server_flight_receiver
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            }) :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg0;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg1;
            } :: ConnLocalEvent client_auth_skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: ConnLocalEvent client_verify_skip :: ConnNetworkEvent {
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
        step_model
          client_finished_sender
          (ConnLocalEvent (LocalVerifyFinished verified_server_finished)) ==
          Some cf_client_after_verify /\
        step_model
          cf_client_after_verify
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficApplication;
              install_direction = TrafficWrite;
              install_material = client_app_write_material;
            })) == Some cf_client_after_app_write /\
        step_model
          cf_client_after_app_write
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficApplication;
              install_direction = TrafficRead;
              install_material = client_app_read_material;
            })) == Some cf_client_after_app_read /\
        step_model
          client_finished_receiver
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficApplication;
                install_direction = TrafficWrite;
                install_material = server_app_write_material;
              };
            })) == Some cf_server_after_app_write /\
        step_model
          cf_client_after_app_read
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg4;
          }) == Some cf_client_after_finished /\
        step_model
          cf_server_after_app_write
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg4;
          }) == Some cf_server_after_finished /\
        conn_events_sent_seal_replay
          client_finished_sender
          (ConnLocalEvent (LocalVerifyFinished verified_server_finished) ::
           ConnLocalEvent
             (LocalInstallTrafficKeys {
               install_epoch = TrafficApplication;
               install_direction = TrafficWrite;
               install_material = client_app_write_material;
             }) ::
           ConnLocalEvent
             (LocalInstallTrafficKeys {
               install_epoch = TrafficApplication;
               install_direction = TrafficRead;
               install_material = client_app_read_material;
             }) ::
           ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake sent_msg4;
           } :: client_finished_rest)
          client_finished_raw_sent
          client_finished_raw_received
          client_finished_final /\
        conn_events_received_decode_replay
          client_finished_receiver
          (ConnLocalEvent
             (LocalInstallTrafficKeysForRole {
               install_role = ServerEndpoint;
               install_payload = {
                 install_epoch = TrafficApplication;
                 install_direction = TrafficWrite;
                 install_material = server_app_write_material;
               };
             }) ::
           ConnNetworkEvent {
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
=
  lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_server_encrypted_flight_with_tails
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
    client_final;
  eliminate exists
    (pair0:protected_message_replay)
    (pair1:protected_message_replay)
    (pair2:protected_message_replay)
    (pair3:protected_message_replay)
    (server_tail_sent:B.bytes)
    (server_tail_received:B.bytes)
    (client_tail_sent:B.bytes)
    (client_tail_received:B.bytes).
    pair0.pm_sender == server_after_install /\
    pair0.pm_receiver == client_after_install /\
    protected_handshake_event_projection_pair
      pair0
      sent_msg0
      received_msg0 /\
    pair1.pm_sender == server_after0 /\
    pair1.pm_receiver == client_after0 /\
    protected_handshake_event_projection_pair
      pair1
      sent_msg1
      received_msg1 /\
    pair2.pm_sender == server_after_auth_skip /\
    pair2.pm_receiver == client_after_auth_skip /\
    protected_handshake_event_projection_pair
      pair2
      sent_msg2
      received_msg2 /\
    pair3.pm_sender == server_after2 /\
    pair3.pm_receiver == client_after_verify_skip /\
    protected_handshake_event_projection_pair
      pair3
      sent_msg3
      received_msg3 /\
    write_read_record_material_aligned server_after3 client_after3 /\
    Seq.equal server_tail_sent client_tail_received /\
    conn_events_sent_seal_replay
      server_after3
      server_rest
      server_tail_sent
      server_tail_received
      server_final /\
    conn_events_received_decode_replay
      client_after3
      client_rest
      client_tail_sent
      client_tail_received
      client_final
  returns
    exists server_ee server_cert server_cv server_finished client_finished.
      paired_protected_handshake_event_projection_pairs
        client_state
        server_state
        server_ee
        server_cert
        server_cv
        server_finished
        client_finished
  with _.
  ( lemma_protected_handshake_event_projection_pair_after_client_finished_local_skips_with_tails
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
    eliminate exists
      (pair4:protected_message_replay)
      (cf_client_tail_sent:B.bytes)
      (cf_client_tail_received:B.bytes)
      (cf_server_tail_sent:B.bytes)
      (cf_server_tail_received:B.bytes).
      pair4.pm_sender == cf_client_after_app_read /\
      pair4.pm_receiver == cf_server_after_app_write /\
      protected_handshake_event_projection_pair
        pair4
        sent_msg4
        received_msg4 /\
      Seq.equal cf_client_tail_sent cf_server_tail_received /\
      conn_events_sent_seal_replay
        cf_client_after_finished
        client_finished_rest
        cf_client_tail_sent
        cf_client_tail_received
        client_finished_final /\
      conn_events_received_decode_replay
        cf_server_after_finished
        server_finished_rest
        cf_server_tail_sent
        cf_server_tail_received
        server_finished_final
    returns
      exists server_ee server_cert server_cv server_finished client_finished.
        paired_protected_handshake_event_projection_pairs
          client_state
          server_state
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished
    with _.
    ( let client_hs = client_state.cs_model.model_handshake in
      let server_hs = server_state.cs_model.model_handshake in
      match
        client_hs.hs_encrypted_extensions,
        server_hs.hs_encrypted_extensions,
        client_hs.hs_certificate,
        server_hs.hs_certificate,
        client_hs.hs_certificate_verify,
        server_hs.hs_certificate_verify,
        client_hs.hs_server_finished,
        server_hs.hs_server_finished,
        client_hs.hs_client_finished,
        server_hs.hs_client_finished
      with
      | Some client_ee, Some server_ee_msg,
        Some client_cert, Some server_cert_msg,
        Some client_cv, Some server_cv_msg,
        Some client_sf, Some server_sf,
        Some client_cf, Some server_cf ->
        assert (sent_msg0 == M.EncryptedExtensions server_ee_msg);
        assert (received_msg0 == M.EncryptedExtensions client_ee);
        assert (sent_msg1 == M.Certificate server_cert_msg);
        assert (received_msg1 == M.Certificate client_cert);
        assert (sent_msg2 == M.CertificateVerify server_cv_msg);
        assert (received_msg2 == M.CertificateVerify client_cv);
        assert (sent_msg3 == M.Finished server_sf);
        assert (received_msg3 == M.Finished client_sf);
        assert (sent_msg4 == M.Finished client_cf);
        assert (received_msg4 == M.Finished server_cf);
        lemma_paired_protected_handshake_event_projection_pair_witnesses_intro_from_messages
          client_state
          server_state
          pair0
          pair1
          pair2
          pair3
          pair4
          sent_msg0
          received_msg0
          sent_msg1
          received_msg1
          sent_msg2
          received_msg2
          sent_msg3
          received_msg3
          sent_msg4
          received_msg4
      | _, _, _, _, _, _, _, _, _, _ ->
        assert False ) )

let lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_staged_replays
  (client_state:connection_state)
  (server_state:connection_state)
  (server_flight_sender:connection_model)
  (server_flight_receiver:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (verified_server_finished:M.finished)
  (client_app_write_material:traffic_key_material)
  (client_app_read_material:traffic_key_material)
  (server_app_write_material:traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list conn_event)
  (server_finished_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  (cf_client_after_verify:connection_model)
  (cf_client_after_app_write:connection_model)
  (cf_client_after_app_read:connection_model)
  (cf_server_after_app_write:connection_model)
  (cf_client_after_finished:connection_model)
  (cf_server_after_finished:connection_model)
=
  let client_finished_events =
    client_finished_replay_events
      verified_server_finished
      client_app_write_material
      client_app_read_material
      sent_msg4
      client_finished_rest in
  let server_finished_events =
    server_receive_client_finished_replay_events
      server_app_write_material
      received_msg4
      server_finished_rest in
  lemma_server_encrypted_flight_produces_client_finished_replay_inputs_with_tails
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
    server_finished_events
    client_finished_events
    server_raw_sent
    server_raw_received
    client_raw_sent
    client_raw_received
    server_final
    client_final;
  eliminate exists
    (client_tail_sent:B.bytes)
    (client_tail_received:B.bytes)
    (server_tail_sent:B.bytes)
    (server_tail_received:B.bytes).
    write_read_record_material_aligned client_after3 server_after3 /\
    Seq.equal client_tail_sent server_tail_received /\
    conn_events_sent_seal_replay
      client_after3
      client_finished_events
      client_tail_sent
      client_tail_received
      client_final /\
    conn_events_received_decode_replay
      server_after3
      server_finished_events
      server_tail_sent
      server_tail_received
      server_final
  returns
    exists server_ee server_cert server_cv server_finished client_finished.
      paired_protected_handshake_event_projection_pairs
        client_state
        server_state
        server_ee
        server_cert
        server_cv
        server_finished
        client_finished
  with _.
  ( lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays
      client_state
      server_state
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
      server_finished_events
      client_finished_events
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
      server_final
      client_final
      client_after3
      server_after3
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
      client_tail_sent
      client_tail_received
      server_tail_sent
      server_tail_received
      client_final
      server_final )
let lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_replay_views
  (client_state:connection_state)
  (server_state:connection_state)
  (server_flight_sender:connection_model)
  (server_flight_receiver:connection_model)
  (server_after_install:connection_model)
  (client_after_install:connection_model)
  (server_after0:connection_model)
  (client_after0:connection_model)
  (server_after1:connection_model)
  (client_after1:connection_model)
  (server_after_auth_skip:connection_model)
  (client_after_auth_skip:connection_model)
  (server_after2:connection_model)
  (client_after2:connection_model)
  (client_after_verify_skip:connection_model)
  (server_after3:connection_model)
  (client_after3:connection_model)
  (server_auth_skip:local_event)
  (client_auth_skip:local_event)
  (client_verify_skip:local_event)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (verified_server_finished:M.finished)
  (client_app_write_material:traffic_key_material)
  (client_app_read_material:traffic_key_material)
  (server_app_write_material:traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  (client_finished_rest:list conn_event)
  (server_finished_rest:list conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  (cf_client_after_verify:connection_model)
  (cf_client_after_app_write:connection_model)
  (cf_client_after_app_read:connection_model)
  (cf_server_after_app_write:connection_model)
  (cf_client_after_finished:connection_model)
  (cf_server_after_finished:connection_model)
=
  assert (
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
      client_final);
  assert (
    conn_events_sent_seal_replay
      server_flight_sender
      (server_protected_handshake_contiguous_replay_events
        server_material
        sent_msg0
        sent_msg1
        server_auth_skip
        sent_msg2
        sent_msg3
        server_app_write_material
        received_msg4
        server_finished_rest)
      server_raw_sent
      server_raw_received
      server_final);
  assert (
    conn_events_received_decode_replay
      server_flight_receiver
      (client_protected_handshake_contiguous_replay_events
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
        client_finished_rest)
      client_raw_sent
      client_raw_received
      client_final);
  assert (
    conn_events_sent_seal_replay
      server_flight_receiver
      (client_protected_handshake_contiguous_replay_events
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
        client_finished_rest)
      client_raw_sent
      client_raw_received
      client_final);
  assert (
    conn_events_received_decode_replay
      server_flight_sender
      (server_protected_handshake_contiguous_replay_events
        server_material
        sent_msg0
        sent_msg1
        server_auth_skip
        sent_msg2
        sent_msg3
        server_app_write_material
        received_msg4
        server_finished_rest)
      server_raw_sent
      server_raw_received
      server_final);
  lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_staged_replays
    client_state
    server_state
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
    cf_server_after_finished

#pop-options
