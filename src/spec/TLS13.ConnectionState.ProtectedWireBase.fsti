module TLS13.ConnectionState.ProtectedWireBase

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

type protected_message_replay = {
  pm_sender: CS.connection_model;
  pm_receiver: CS.connection_model;
  pm_raw_sent: B.bytes;
  pm_raw_received: B.bytes;
}

noextract
let write_read_record_material_aligned
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  : prop =
  sender.CS.model_record.CS.record_write.R.seq ==
    receiver.CS.model_record.CS.record_read.R.seq /\
  (match
    CS.record_direction_material sender.CS.model_record.CS.record_write,
    CS.record_direction_material receiver.CS.model_record.CS.record_read
  with
  | Some sender_write, Some receiver_read ->
    CS.record_key_iv_material_agrees sender_write receiver_read
  | _, _ ->
    False)

noextract
let local_event_does_not_install_record_keys
  (ev:CS.local_event)
  : prop =
  match ev with
  | CS.LocalInstallTrafficKeys _
  | CS.LocalInstallTrafficKeysForRole _ ->
    False
  | _ ->
    True

noextract
let local_event_preserves_record_write
  (ev:CS.local_event)
  : prop =
  match ev with
  | CS.LocalInstallTrafficKeys install ->
    install.CS.install_direction == CS.TrafficRead \/
    (install.CS.install_epoch == CS.TrafficApplication /\
     install.CS.install_direction == CS.TrafficWrite)
  | CS.LocalInstallTrafficKeysForRole role_install ->
    let install = role_install.CS.install_payload in
    install.CS.install_direction == CS.TrafficRead \/
    (role_install.CS.install_role <> CS.ServerEndpoint /\
     install.CS.install_epoch == CS.TrafficApplication /\
     install.CS.install_direction == CS.TrafficWrite)
  | _ ->
    True

noextract
let local_event_preserves_record_read
  (ev:CS.local_event)
  : prop =
  match ev with
  | CS.LocalInstallTrafficKeys install ->
    install.CS.install_direction == CS.TrafficWrite
  | CS.LocalInstallTrafficKeysForRole role_install ->
    role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | _ ->
    True

noextract
let client_finished_replay_events
  (verified_server_finished:M.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (rest:list CS.conn_event)
  : list CS.conn_event =
  CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished) ::
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
    CL.message_value = M.TlsHandshake sent_msg;
  } :: rest

noextract
let server_receive_client_finished_replay_events
  (server_app_write_material:CS.traffic_key_material)
  (received_msg:M.handshake_msg)
  (rest:list CS.conn_event)
  : list CS.conn_event =
  CS.ConnLocalEvent
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
    CL.message_value = M.TlsHandshake received_msg;
  } :: rest

noextract
let server_encrypted_flight_replay_events
  (server_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (server_auth_skip:CS.local_event)
  (sent_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (rest:list CS.conn_event)
  : list CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = server_material;
      };
    }) ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg0;
  } ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg1;
  } ::
  CS.ConnLocalEvent server_auth_skip ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg2;
  } ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg3;
  } ::
  rest

noextract
let client_receive_server_encrypted_flight_replay_events
  (client_material:CS.traffic_key_material)
  (received_msg0:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (client_auth_skip:CS.local_event)
  (received_msg2:M.handshake_msg)
  (client_verify_skip:CS.local_event)
  (received_msg3:M.handshake_msg)
  (rest:list CS.conn_event)
  : list CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = client_material;
    }) ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg0;
  } ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg1;
  } ::
  CS.ConnLocalEvent client_auth_skip ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg2;
  } ::
  CS.ConnLocalEvent client_verify_skip ::
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg3;
  } ::
  rest

noextract
let server_protected_handshake_contiguous_replay_events
  (server_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (server_auth_skip:CS.local_event)
  (sent_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (server_app_write_material:CS.traffic_key_material)
  (received_msg4:M.handshake_msg)
  (rest:list CS.conn_event)
  : list CS.conn_event =
  server_encrypted_flight_replay_events
    server_material
    sent_msg0
    sent_msg1
    server_auth_skip
    sent_msg2
    sent_msg3
    (server_receive_client_finished_replay_events
      server_app_write_material
      received_msg4
      rest)

noextract
let client_protected_handshake_contiguous_replay_events
  (client_material:CS.traffic_key_material)
  (received_msg0:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (client_auth_skip:CS.local_event)
  (received_msg2:M.handshake_msg)
  (client_verify_skip:CS.local_event)
  (received_msg3:M.handshake_msg)
  (verified_server_finished:M.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (sent_msg4:M.handshake_msg)
  (rest:list CS.conn_event)
  : list CS.conn_event =
  client_receive_server_encrypted_flight_replay_events
    client_material
    received_msg0
    received_msg1
    client_auth_skip
    received_msg2
    client_verify_skip
    received_msg3
    (client_finished_replay_events
      verified_server_finished
      client_app_write_material
      client_app_read_material
      sent_msg4
      rest)

noextract
let paired_protected_handshake_contiguous_replay_views
  (server_flight_sender:CS.connection_model)
  (server_flight_receiver:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (client_verify_skip:CS.local_event)
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
  : prop =
  let server_events =
    server_protected_handshake_contiguous_replay_events
      server_material
      sent_msg0
      sent_msg1
      server_auth_skip
      sent_msg2
      sent_msg3
      server_app_write_material
      received_msg4
      server_finished_rest in
  let client_events =
    client_protected_handshake_contiguous_replay_events
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
  CS.conn_events_sent_seal_replay
    server_flight_sender
    server_events
    server_raw_sent
    server_raw_received
    server_final /\
  CS.conn_events_received_decode_replay
    server_flight_receiver
    client_events
    client_raw_sent
    client_raw_received
    client_final /\
  CS.conn_events_sent_seal_replay
    server_flight_receiver
    client_events
    client_raw_sent
    client_raw_received
    client_final /\
  CS.conn_events_received_decode_replay
    server_flight_sender
    server_events
    server_raw_sent
    server_raw_received
    server_final


noextract
let protected_handshake_wire_round_trip_message (msg:M.handshake_msg) : prop =
  match msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ -> True
  | _ -> False

noextract
let protected_handshake_head_steps_advance_write_read
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  : prop =
  let sent_ev = CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  match CS.step_model sender sent_ev, CS.step_model receiver received_ev with
  | Some sender_after, Some receiver_after ->
    sender_after.CS.model_record.CS.record_write ==
      R.next_seq sender.CS.model_record.CS.record_write /\
    receiver_after.CS.model_record.CS.record_read ==
      R.next_seq receiver.CS.model_record.CS.record_read
  | _, _ ->
    False


noextract
let protected_handshake_event_projection_pair
  (pair:protected_message_replay)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  : prop =
  pair.pm_sender.CS.model_record.CS.record_write.R.seq ==
    pair.pm_receiver.CS.model_record.CS.record_read.R.seq /\
  (match
    CS.record_direction_material pair.pm_sender.CS.model_record.CS.record_write,
    CS.record_direction_material pair.pm_receiver.CS.model_record.CS.record_read
  with
  | Some sender_write, Some receiver_read ->
    CS.record_key_iv_material_agrees sender_write receiver_read
  | _, _ ->
    False) /\
  Seq.equal pair.pm_raw_sent pair.pm_raw_received /\
  protected_handshake_wire_round_trip_message sent_msg /\
  protected_handshake_wire_round_trip_message received_msg /\
  CS.sent_event_seal_projection
    pair.pm_sender
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake sent_msg;
    })
    pair.pm_raw_sent /\
  CS.received_event_decode_projection
    pair.pm_receiver
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake received_msg;
    })
    pair.pm_raw_received

noextract
let paired_protected_handshake_event_projection_pairs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_encrypted_extensions,
    server_hs.CS.hs_encrypted_extensions,
    client_hs.CS.hs_certificate,
    server_hs.CS.hs_certificate,
    client_hs.CS.hs_certificate_verify,
    server_hs.CS.hs_certificate_verify,
    client_hs.CS.hs_server_finished,
    server_hs.CS.hs_server_finished,
    client_hs.CS.hs_client_finished,
    server_hs.CS.hs_client_finished
  with
  | Some client_ee, Some server_ee_msg,
    Some client_cert, Some server_cert_msg,
    Some client_cv, Some server_cv_msg,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    protected_handshake_event_projection_pair
      server_ee
      (M.EncryptedExtensions server_ee_msg)
      (M.EncryptedExtensions client_ee) /\
    protected_handshake_event_projection_pair
      server_cert
      (M.Certificate server_cert_msg)
      (M.Certificate client_cert) /\
    protected_handshake_event_projection_pair
      server_cv
      (M.CertificateVerify server_cv_msg)
      (M.CertificateVerify client_cv) /\
    protected_handshake_event_projection_pair
      server_finished
      (M.Finished server_sf)
      (M.Finished client_sf) /\
    protected_handshake_event_projection_pair
      client_finished
      (M.Finished client_cf)
      (M.Finished server_cf)
  | _, _, _, _, _, _, _, _, _, _ ->
    False
