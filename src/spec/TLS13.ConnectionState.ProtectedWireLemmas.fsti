module TLS13.ConnectionState.ProtectedWireLemmas

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

val lemma_client_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:CS.traffic_epoch)
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        client.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          server.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
        CS.peer_record_material_agrees
          (CS.traffic_id epoch CS.ClientTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          client.CS.cs_model
          server.CS.cs_model)

val lemma_server_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:CS.traffic_epoch)
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        server.CS.cs_model.CS.model_record.CS.record_write.R.seq ==
          client.CS.cs_model.CS.model_record.CS.record_read.R.seq /\
        CS.peer_record_material_agrees
          (CS.traffic_id epoch CS.ServerTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          server.CS.cs_model
          client.CS.cs_model)

val lemma_append_heads_equal_same_len:
  #a:eqtype ->
  left:Seq.seq a ->
  left_tail:Seq.seq a ->
  right:Seq.seq a ->
  right_tail:Seq.seq a ->
  Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left right)

val lemma_append_tails_equal_same_len:
  #a:eqtype ->
  left:Seq.seq a ->
  left_tail:Seq.seq a ->
  right:Seq.seq a ->
  right_tail:Seq.seq a ->
  Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left_tail right_tail)

val lemma_raw_delta_heads_equal_same_len:
  sender_delta:B.bytes ->
  sender_tail:B.bytes ->
  receiver_delta:B.bytes ->
  receiver_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal
        (B.append sender_delta sender_tail)
        (B.append receiver_delta receiver_tail) /\
      B.length sender_delta == B.length receiver_delta)
    (ensures Seq.equal sender_delta receiver_delta)

val lemma_equal_streams_skip_empty_left:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  left_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail))
    (ensures Seq.equal left_tail right_stream)

val lemma_equal_streams_skip_empty_right:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  right_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_stream right_tail)

val lemma_equal_streams_skip_empty_both:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  left_tail:B.bytes ->
  right_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail) /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_tail right_tail)

val lemma_equal_stream_record_head_lengths:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  left_head:B.bytes ->
  left_tail:B.bytes ->
  right_head:B.bytes ->
  right_tail:B.bytes ->
  left_ct:T.content_type ->
  left_fragment:M.sealed_record ->
  right_ct:T.content_type ->
  right_fragment:M.sealed_record ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append left_head left_tail) /\
      Seq.equal right_stream (B.append right_head right_tail) /\
      W.parse_record_wire left_head ==
        Some (left_ct, left_fragment, B.length left_head) /\
      W.parse_record_wire right_head ==
        Some (right_ct, right_fragment, B.length right_head))
    (ensures B.length left_head == B.length right_head)

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

val lemma_protected_handshake_wire_equal_from_sent_seal_peer
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        CS.sent_single_protected_message_seal
          sender
          (M.TlsHandshake sent_msg)
          raw /\
        CS.received_single_protected_message_decode
          receiver
          (M.TlsHandshake received_msg)
          raw /\
        protected_handshake_wire_round_trip_message received_msg)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))

val lemma_protected_handshake_wire_equal_from_event_projections_peer
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal raw_sent raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          raw_sent /\
        CS.received_event_decode_projection
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          raw_received)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))

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

val lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : Lemma
      (requires
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)
      (ensures WFL.paired_protected_handshake_wire_equivalent client server)

val lemma_paired_protected_handshake_event_projection_pairs_intro
  (client:CS.connection_state)
  (server:CS.connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : Lemma
      (requires
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
          False))
      (ensures
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)

val lemma_paired_protected_handshake_event_projection_pairs_intro_from_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  : Lemma
      (requires
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
        protected_handshake_event_projection_pair
          server_ee
          sent_msg0
          received_msg0 /\
        protected_handshake_event_projection_pair
          server_cert
          sent_msg1
          received_msg1 /\
        protected_handshake_event_projection_pair
          server_cv
          sent_msg2
          received_msg2 /\
        protected_handshake_event_projection_pair
          server_finished
          sent_msg3
          received_msg3 /\
        protected_handshake_event_projection_pair
          client_finished
          sent_msg4
          received_msg4)
      (ensures
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)

val lemma_paired_protected_handshake_event_projection_pair_witnesses_intro_from_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  : Lemma
      (requires
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
        protected_handshake_event_projection_pair
          server_ee
          sent_msg0
          received_msg0 /\
        protected_handshake_event_projection_pair
          server_cert
          sent_msg1
          received_msg1 /\
        protected_handshake_event_projection_pair
          server_cv
          sent_msg2
          received_msg2 /\
        protected_handshake_event_projection_pair
          server_finished
          sent_msg3
          received_msg3 /\
        protected_handshake_event_projection_pair
          client_finished
          sent_msg4
          received_msg4)
      (ensures
        exists server_ee' server_cert' server_cv' server_finished' client_finished'.
          paired_protected_handshake_event_projection_pairs
            client
            server
            server_ee'
            server_cert'
            server_cv'
            server_finished'
            client_finished')

val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_pair_outputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  : Lemma
      (requires
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
        (exists server_ee server_cert server_cv server_finished.
          protected_handshake_event_projection_pair
            server_ee
            sent_msg0
            received_msg0 /\
          protected_handshake_event_projection_pair
            server_cert
            sent_msg1
            received_msg1 /\
          protected_handshake_event_projection_pair
            server_cv
            sent_msg2
            received_msg2 /\
          protected_handshake_event_projection_pair
            server_finished
            sent_msg3
            received_msg3) /\
        (exists client_finished.
          protected_handshake_event_projection_pair
            client_finished
            sent_msg4
            received_msg4))
      (ensures
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client
            server
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)

val lemma_conn_events_sent_seal_replay_head
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          CS.legal_event model ev /\
          CS.step_model model ev == Some model1 /\
          CS.event_raw_delta_legal model ev delta_sent delta_received /\
          CS.sent_event_nonempty_seal_projection model ev delta_sent /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          CS.conn_events_sent_seal_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)

val lemma_conn_events_received_decode_replay_head
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          CS.legal_event model ev /\
          CS.step_model model ev == Some model1 /\
          CS.event_raw_delta_legal model ev delta_sent delta_received /\
          CS.received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          CS.conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)

val lemma_step_received_network_event_preserves_record_write
  (model:CS.connection_model)
  (msg:M.tls_message)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_write ==
          model.CS.model_record.CS.record_write)

val lemma_step_sent_network_event_preserves_record_read
  (model:CS.connection_model)
  (msg:M.tls_message)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_read ==
          model.CS.model_record.CS.record_read)

val lemma_step_received_network_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (msg:M.tls_message)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)

val lemma_step_sent_network_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (msg:M.tls_message)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)

val lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
  (sender:CS.connection_model)
  (sender_msg:M.tls_message)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_msg:M.tls_message)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_msg;
          }) == Some sender_after /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver_after)

val lemma_step_non_install_local_event_preserves_record_layer
  (model:CS.connection_model)
  (ev:CS.local_event)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        CS.step_model
          model
          (CS.ConnLocalEvent ev) == Some model_after)
      (ensures model_after.CS.model_record == model.CS.model_record)

val lemma_step_local_event_preserves_record_write
  (model:CS.connection_model)
  (ev:CS.local_event)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_write ev /\
        CS.step_model
          model
          (CS.ConnLocalEvent ev) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_write ==
          model.CS.model_record.CS.record_write)

val lemma_step_local_event_preserves_record_read
  (model:CS.connection_model)
  (ev:CS.local_event)
  (model_after:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_read ev /\
        CS.step_model
          model
          (CS.ConnLocalEvent ev) == Some model_after)
      (ensures
        model_after.CS.model_record.CS.record_read ==
          model.CS.model_record.CS.record_read)

val lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (ev:CS.local_event)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        CS.step_model
          sender
          (CS.ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)

val lemma_step_sender_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (ev:CS.local_event)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_write ev /\
        CS.step_model
          sender
          (CS.ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)

val lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (ev:CS.local_event)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        CS.step_model
          receiver
          (CS.ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)

val lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (ev:CS.local_event)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        local_event_preserves_record_read ev /\
        CS.step_model
          receiver
          (CS.ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)

val lemma_next_seq_models_preserve_write_read_record_material_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver_after:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        sender_after.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read)
      (ensures write_read_record_material_aligned sender_after receiver_after)

val lemma_server_handshake_write_client_handshake_read_install_aligned
  (server:CS.connection_model)
  (client:CS.connection_model)
  (material:CS.traffic_key_material)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              };
            })) == Some server_after /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)

val lemma_server_handshake_write_client_handshake_read_install_materials_aligned
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  : Lemma
      (requires
        CS.record_key_iv_material_agrees
          (CS.record_material_of_traffic_material server_material)
          (CS.record_material_of_traffic_material client_material) /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)

val lemma_server_handshake_install_materials_agree_from_key_schedule
  (server_hs:CS.handshake_state)
  (client_hs:CS.handshake_state)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  : Lemma
      (requires
        (match
          server_hs.CS.hs_keys.CS.ks_handshake_secret,
          client_hs.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal server_hs.CS.hs_transcript client_hs.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          } /\
        CS.traffic_install_matches_key_schedule
          client_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_material;
          })
      (ensures
        CS.record_key_iv_material_agrees
          (CS.record_material_of_traffic_material server_material)
          (CS.record_material_of_traffic_material client_material))

val lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          } /\
        CS.traffic_install_matches_key_schedule
          client.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_material;
          } /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)

val lemma_client_handshake_write_server_handshake_read_install_aligned
  (client:CS.connection_model)
  (server:CS.connection_model)
  (material:CS.traffic_key_material)
  (client_after:CS.connection_model)
  (server_after:CS.connection_model)
  : Lemma
      (requires
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = material;
            })) == Some client_after /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)

val lemma_client_handshake_write_server_handshake_read_install_materials_aligned
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  (client_after:CS.connection_model)
  (server_after:CS.connection_model)
  : Lemma
      (requires
        CS.record_key_iv_material_agrees
          (CS.record_material_of_traffic_material client_material)
          (CS.record_material_of_traffic_material server_material) /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_material;
            })) == Some client_after /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)

val lemma_client_handshake_install_materials_agree_from_key_schedule
  (client_hs:CS.handshake_state)
  (server_hs:CS.handshake_state)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  : Lemma
      (requires
        (match
          client_hs.CS.hs_keys.CS.ks_handshake_secret,
          server_hs.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal client_hs.CS.hs_transcript server_hs.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule
          client_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_material;
          } /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server_hs
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_material;
          })
      (ensures
        CS.record_key_iv_material_agrees
          (CS.record_material_of_traffic_material client_material)
          (CS.record_material_of_traffic_material server_material))

val lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  (client_after:CS.connection_model)
  (server_after:CS.connection_model)
  : Lemma
      (requires
        (match
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal
          client.CS.model_handshake.CS.hs_transcript
          server.CS.model_handshake.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule
          client.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_material;
          } /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint
          server.CS.model_handshake
          {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_material;
          } /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_material;
            })) == Some client_after /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)

val lemma_sent_replay_skip_empty_head_preserves_peer_stream
  (sender:CS.connection_model)
  (ev:CS.conn_event)
  (sender_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        CS.conn_events_sent_seal_replay
          sender
          (ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        (match ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists sender1 sender_tail_sent sender_tail_received.
          CS.legal_event sender ev /\
          CS.step_model sender ev == Some sender1 /\
          Seq.equal sender_tail_sent receiver_raw_received /\
          CS.conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final)

val lemma_received_replay_skip_empty_head_preserves_peer_stream
  (sender_raw_sent:B.bytes)
  (receiver:CS.connection_model)
  (ev:CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        CS.conn_events_received_decode_replay
          receiver
          (ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists receiver1 receiver_tail_sent receiver_tail_received.
          CS.legal_event receiver ev /\
          CS.step_model receiver ev == Some receiver1 /\
          Seq.equal sender_raw_sent receiver_tail_received /\
          CS.conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_sent_replay_skip_zero_received_head_preserves_peer_stream
  (receiver_raw_sent:B.bytes)
  (sender:CS.connection_model)
  (ev:CS.conn_event)
  (sender_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal receiver_raw_sent sender_raw_received /\
        CS.conn_events_sent_seal_replay
          sender
          (ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        (match ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists sender1 sender_tail_sent sender_tail_received.
          CS.legal_event sender ev /\
          CS.step_model sender ev == Some sender1 /\
          Seq.equal receiver_raw_sent sender_tail_received /\
          CS.conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final)

val lemma_received_replay_skip_zero_sent_head_preserves_peer_stream
  (receiver:CS.connection_model)
  (ev:CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal receiver_raw_sent sender_raw_received /\
        CS.conn_events_received_decode_replay
          receiver
          (ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists receiver1 receiver_tail_sent receiver_tail_received.
          CS.legal_event receiver ev /\
          CS.step_model receiver ev == Some receiver1 /\
          Seq.equal receiver_tail_sent sender_raw_received /\
          CS.conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_ev:CS.conn_event)
  (receiver_ev:CS.conn_event)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal receiver_raw_sent sender_raw_received /\
        CS.conn_events_sent_seal_replay
          sender
          (sender_ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (receiver_ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match sender_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        (match receiver_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists sender1 receiver1
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.legal_event sender sender_ev /\
          CS.step_model sender sender_ev == Some sender1 /\
          CS.legal_event receiver receiver_ev /\
          CS.step_model receiver receiver_ev == Some receiver1 /\
          Seq.equal receiver_tail_sent sender_tail_received /\
          CS.conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_ev:CS.conn_event)
  (receiver_ev:CS.conn_event)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        CS.conn_events_sent_seal_replay
          sender
          (sender_ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (receiver_ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match sender_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists sender1 receiver1
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.legal_event sender sender_ev /\
          CS.step_model sender sender_ev == Some sender1 /\
          CS.legal_event receiver receiver_ev /\
          CS.step_model receiver receiver_ev == Some receiver1 /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_sent_event_nonempty_seal_projection_protected
  (model:CS.connection_model)
  (msg:M.tls_message)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Sent msg == false /\
        CS.protected_record_count CL.Sent msg == 1 /\
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent
          delta_received /\
        CS.sent_event_nonempty_seal_projection
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)
      (ensures
        CS.sent_event_seal_projection
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)

val lemma_received_event_nonempty_decode_projection_protected
  (model:CS.connection_model)
  (msg:M.tls_message)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Received msg == false /\
        CS.protected_record_count CL.Received msg == 1 /\
        CS.event_raw_delta_legal
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_sent
          delta_received /\
        CS.received_event_nonempty_decode_projection
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)
      (ensures
        CS.received_event_decode_projection
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)

val lemma_protected_handshake_event_projection_pair_from_aligned_heads
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_stream:B.bytes)
  (receiver_stream:B.bytes)
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        B.length sender_delta == B.length receiver_delta /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        CS.received_event_decode_projection
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          receiver_delta)
      (ensures
        protected_handshake_event_projection_pair
          {
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta;
            pm_raw_received = receiver_delta;
          }
          sent_msg
          received_msg)

val lemma_protected_handshake_event_projection_pair_from_equal_stream_heads
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_stream:B.bytes)
  (receiver_stream:B.bytes)
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        CS.received_event_decode_projection
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          receiver_delta)
      (ensures
        protected_handshake_event_projection_pair
          {
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta;
            pm_raw_received = receiver_delta;
          }
          sent_msg
          received_msg)

val lemma_protected_handshake_event_tails_equal_from_equal_stream_heads
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_stream:B.bytes)
  (receiver_stream:B.bytes)
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        CS.received_event_decode_projection
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          receiver_delta)
      (ensures Seq.equal sender_tail receiver_tail)

val lemma_protected_handshake_event_projection_pair_from_head_replays
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after receiver_after pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after /\
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
          Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after /\
        sender_after.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after)

val lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after /\
        sender_after.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after /\
          Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
          Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pairs_from_two_head_replays_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after0:CS.connection_model)
  (receiver_after0:CS.connection_model)
  (sender_after1:CS.connection_model)
  (receiver_after1:CS.connection_model)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some sender_after0 /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some receiver_after0 /\
        sender_after0.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after0.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read /\
        CS.step_model
          sender_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some sender_after1 /\
        CS.step_model
          receiver_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some receiver_after1 /\
        sender_after1.CS.model_record.CS.record_write ==
          R.next_seq sender_after0.CS.model_record.CS.record_write /\
        receiver_after1.CS.model_record.CS.record_read ==
          R.next_seq receiver_after0.CS.model_record.CS.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair0 pair1 sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair0.pm_sender == sender /\
          pair0.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair0
            sent_msg0
            received_msg0 /\
          pair1.pm_sender == sender_after0 /\
          pair1.pm_receiver == receiver_after0 /\
          protected_handshake_event_projection_pair
            pair1
            sent_msg1
            received_msg1 /\
          write_read_record_material_aligned sender_after0 receiver_after0 /\
          write_read_record_material_aligned sender_after1 receiver_after1 /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model sender skip_ev == Some sender_after /\
        (match skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        sender_after.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender_after.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model sender skip_ev == Some sender_after /\
        (match skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        write_read_record_material_aligned sender_after receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            sender_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after_head:CS.connection_model)
  (receiver_after_head:CS.connection_model)
  (skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model sender skip_ev == Some sender_after /\
        CS.step_model
          sender_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.CS.model_record.CS.record_write ==
          R.next_seq sender_after.CS.model_record.CS.record_write /\
        receiver_after_head.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read /\
        (match skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        write_read_record_material_aligned sender_after receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after_head receiver_after_head /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model receiver skip_ev == Some receiver_after /\
        (match skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver_after.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver_after.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model receiver skip_ev == Some receiver_after /\
        (match skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sender_after_head:CS.connection_model)
  (receiver_after_head:CS.connection_model)
  (skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model receiver skip_ev == Some receiver_after /\
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        CS.step_model
          receiver_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after_head.CS.model_record.CS.record_read ==
          R.next_seq receiver_after.CS.model_record.CS.record_read /\
        (match skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after_head receiver_after_head /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sender_skip_ev:CS.conn_event)
  (receiver_skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model sender sender_skip_ev == Some sender_after /\
        CS.step_model receiver receiver_skip_ev == Some receiver_after /\
        (match sender_skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        sender_after.CS.model_record.CS.record_write.R.seq ==
          receiver_after.CS.model_record.CS.record_read.R.seq /\
        (match
          CS.record_direction_material sender_after.CS.model_record.CS.record_write,
          CS.record_direction_material receiver_after.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_tails
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sender_skip_ev:CS.conn_event)
  (receiver_skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model sender sender_skip_ev == Some sender_after /\
        CS.step_model receiver receiver_skip_ev == Some receiver_after /\
        (match sender_skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender_after receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            sender_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sender_after_head:CS.connection_model)
  (receiver_after_head:CS.connection_model)
  (sender_skip_ev:CS.conn_event)
  (receiver_skip_ev:CS.conn_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        CS.step_model sender sender_skip_ev == Some sender_after /\
        CS.step_model receiver receiver_skip_ev == Some receiver_after /\
        CS.step_model
          sender_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        CS.step_model
          receiver_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.CS.model_record.CS.record_write ==
          R.next_seq sender_after.CS.model_record.CS.record_write /\
        receiver_after_head.CS.model_record.CS.record_read ==
          R.next_seq receiver_after.CS.model_record.CS.record_read /\
        (match sender_skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | CS.ConnLocalEvent _ -> True
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender_after receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after_head receiver_after_head /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pairs_from_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after0:CS.connection_model)
  (receiver_after0:CS.connection_model)
  (sender_after1:CS.connection_model)
  (receiver_after1:CS.connection_model)
  (sender_after_skip:CS.connection_model)
  (receiver_after_skip:CS.connection_model)
  (sender_after2:CS.connection_model)
  (receiver_after2:CS.connection_model)
  (sender_skip:CS.local_event)
  (receiver_skip:CS.local_event)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        local_event_does_not_install_record_keys sender_skip /\
        local_event_does_not_install_record_keys receiver_skip /\
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some sender_after0 /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some receiver_after0 /\
        sender_after0.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after0.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read /\
        CS.step_model
          sender_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some sender_after1 /\
        CS.step_model
          receiver_after0
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some receiver_after1 /\
        sender_after1.CS.model_record.CS.record_write ==
          R.next_seq sender_after0.CS.model_record.CS.record_write /\
        receiver_after1.CS.model_record.CS.record_read ==
          R.next_seq receiver_after0.CS.model_record.CS.record_read /\
        CS.step_model
          sender_after1
          (CS.ConnLocalEvent sender_skip) == Some sender_after_skip /\
        CS.step_model
          receiver_after1
          (CS.ConnLocalEvent receiver_skip) == Some receiver_after_skip /\
        CS.step_model
          sender_after_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some sender_after2 /\
        CS.step_model
          receiver_after_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some receiver_after2 /\
        sender_after2.CS.model_record.CS.record_write ==
          R.next_seq sender_after_skip.CS.model_record.CS.record_write /\
        receiver_after2.CS.model_record.CS.record_read ==
          R.next_seq receiver_after_skip.CS.model_record.CS.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          } :: CS.ConnLocalEvent sender_skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          } :: CS.ConnLocalEvent receiver_skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair0 pair1 pair2 sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair0.pm_sender == sender /\
          pair0.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair0
            sent_msg0
            received_msg0 /\
          pair1.pm_sender == sender_after0 /\
          pair1.pm_receiver == receiver_after0 /\
          protected_handshake_event_projection_pair
            pair1
            sent_msg1
            received_msg1 /\
          pair2.pm_sender == sender_after_skip /\
          pair2.pm_receiver == receiver_after_skip /\
          protected_handshake_event_projection_pair
            pair2
            sent_msg2
            received_msg2 /\
          write_read_record_material_aligned sender_after1 receiver_after1 /\
          write_read_record_material_aligned sender_after2 receiver_after2 /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after2
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after2
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          server
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
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists server_after client_after server_after_head client_after_head pair
          server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          CS.step_model
            server
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = server_material;
                };
              })) == Some server_after /\
          CS.step_model
            client
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = client_material;
              })) == Some client_after /\
          CS.step_model
            server_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some server_after_head /\
          CS.step_model
            client_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some client_after_head /\
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal server_tail_sent client_tail_received /\
          CS.conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_next_alignment_and_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after:CS.connection_model)
  (client_after:CS.connection_model)
  (server_after_head:CS.connection_model)
  (client_after_head:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_material;
              };
            })) == Some server_after /\
        CS.step_model
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            })) == Some client_after /\
        CS.step_model
          server_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some server_after_head /\
        CS.step_model
          client_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some client_after_head /\
        server_after_head.CS.model_record.CS.record_write ==
          R.next_seq server_after.CS.model_record.CS.record_write /\
        client_after_head.CS.model_record.CS.record_read ==
          R.next_seq client_after.CS.model_record.CS.record_read /\
        CS.conn_events_sent_seal_replay
          server
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
              CL.message_value = M.TlsHandshake sent_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists pair server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          pair.pm_sender == server_after /\
          pair.pm_receiver == client_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned server_after_head client_after_head /\
          Seq.equal server_tail_sent client_tail_received /\
          CS.conn_events_sent_seal_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_and_next_head_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        CS.step_model
          server
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
          client
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
        CS.conn_events_sent_seal_replay
          server
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
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
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
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists pair0 pair1 server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
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
          write_read_record_material_aligned server_after1 client_after1 /\
          Seq.equal server_tail_sent client_tail_received /\
          CS.conn_events_sent_seal_replay
            server_after1
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after1
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
  (server_after_install:CS.connection_model)
  (client_after_install:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_skip:CS.connection_model)
  (client_after_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (server_skip:CS.local_event)
  (client_skip:CS.local_event)
  (server_material:CS.traffic_key_material)
  (client_material:CS.traffic_key_material)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
        local_event_does_not_install_record_keys server_skip /\
        local_event_does_not_install_record_keys client_skip /\
        Seq.equal server_raw_sent client_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        CS.step_model
          server
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
          client
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
        CS.step_model server_after1 (CS.ConnLocalEvent server_skip) ==
          Some server_after_skip /\
        CS.step_model client_after1 (CS.ConnLocalEvent client_skip) ==
          Some client_after_skip /\
        CS.step_model
          server_after_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some server_after2 /\
        CS.step_model
          client_after_skip
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some client_after2 /\
        server_after2.CS.model_record.CS.record_write ==
          R.next_seq server_after_skip.CS.model_record.CS.record_write /\
        client_after2.CS.model_record.CS.record_read ==
          R.next_seq client_after_skip.CS.model_record.CS.record_read /\
        CS.conn_events_sent_seal_replay
          server
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
            } :: CS.ConnLocalEvent server_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg2;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final /\
        CS.conn_events_received_decode_replay
          client
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
            } :: CS.ConnLocalEvent client_skip :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg2;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final)
      (ensures
        exists pair0 pair1 pair2 server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
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
          pair2.pm_sender == server_after_skip /\
          pair2.pm_receiver == client_after_skip /\
          protected_handshake_event_projection_pair
            pair2
            sent_msg2
            received_msg2 /\
          write_read_record_material_aligned server_after2 client_after2 /\
          Seq.equal server_tail_sent client_tail_received /\
          CS.conn_events_sent_seal_replay
            server_after2
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after2
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_server_encrypted_flight_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
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
  : Lemma
      (requires
        (match
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.CS.model_handshake.CS.hs_transcript
          client.CS.model_handshake.CS.hs_transcript /\
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
          server
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
          client
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
          server
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
          client
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
          client_final)
      (ensures
        exists pair0 pair1 pair2 pair3 server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
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
          CS.conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_server_encrypted_flight_preserves_client_to_server_stream_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
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
  : Lemma
      (requires
        Seq.equal client_raw_sent server_raw_received /\
        CS.step_model
          server
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
          client
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
        CS.conn_events_sent_seal_replay
          server
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
          client
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
          client_final)
      (ensures
        exists server_tail_sent server_tail_received
          client_tail_sent client_tail_received.
          Seq.equal client_tail_sent server_tail_received /\
          CS.conn_events_sent_seal_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final /\
          CS.conn_events_received_decode_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final)

val lemma_server_encrypted_flight_preserves_client_to_server_replay_tails_with_tails
  (server:CS.connection_model)
  (client:CS.connection_model)
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
  : Lemma
      (requires
        Seq.equal client_raw_sent server_raw_received /\
        CS.step_model
          server
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
          client
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
        CS.conn_events_sent_seal_replay
          client
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
        CS.conn_events_received_decode_replay
          server
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
          server_final)
      (ensures
        exists client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
          Seq.equal client_tail_sent server_tail_received /\
          CS.conn_events_sent_seal_replay
            client_after3
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after3
            server_rest
            server_tail_sent
            server_tail_received
            server_final)

val lemma_server_encrypted_flight_preserves_client_write_server_read_alignment
  (server:CS.connection_model)
  (client:CS.connection_model)
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
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        local_event_does_not_install_record_keys server_auth_skip /\
        local_event_does_not_install_record_keys client_auth_skip /\
        local_event_does_not_install_record_keys client_verify_skip /\
        CS.step_model
          server
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
          client
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
          }) == Some client_after3)
      (ensures write_read_record_material_aligned client_after3 server_after3)

val lemma_protected_handshake_event_projection_pair_after_client_write_server_read_install_heads_with_tails
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_material:CS.traffic_key_material)
  (server_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_rest:list CS.conn_event)
  (server_rest:list CS.conn_event)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_final:CS.connection_model)
  (server_final:CS.connection_model)
  : Lemma
      (requires
        (match
          client.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          server.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal
          client.CS.model_handshake.CS.hs_transcript
          server.CS.model_handshake.CS.hs_transcript /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          client
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_material;
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        CS.conn_events_received_decode_replay
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_material;
              };
            }) :: CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists client_after server_after client_after_head server_after_head pair
          client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
          CS.step_model
            client
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = client_material;
              })) == Some client_after /\
          CS.step_model
            server
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_material;
                };
              })) == Some server_after /\
          CS.step_model
            client_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some client_after_head /\
          CS.step_model
            server_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some server_after_head /\
          pair.pm_sender == client_after /\
          pair.pm_receiver == server_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal client_tail_sent server_tail_received /\
          CS.conn_events_sent_seal_replay
            client_after_head
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after_head
            server_rest
            server_tail_sent
            server_tail_received
            server_final)

val lemma_protected_handshake_event_projection_pair_after_client_finished_local_skips_with_tails
  (client:CS.connection_model)
  (server:CS.connection_model)
  (client_after_verify:CS.connection_model)
  (client_after_app_write:CS.connection_model)
  (client_after_app_read:CS.connection_model)
  (server_after_app_write:CS.connection_model)
  (client_after_finished:CS.connection_model)
  (server_after_finished:CS.connection_model)
  (verified_server_finished:M.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (client_rest:list CS.conn_event)
  (server_rest:list CS.conn_event)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_final:CS.connection_model)
  (server_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned client server /\
        Seq.equal client_raw_sent server_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.step_model
          client
          (CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished)) ==
          Some client_after_verify /\
        CS.step_model
          client_after_verify
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = client_app_write_material;
            })) == Some client_after_app_write /\
        CS.step_model
          client_after_app_write
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeys {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = client_app_read_material;
            })) == Some client_after_app_read /\
        CS.step_model
          server
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            })) == Some server_after_app_write /\
        CS.step_model
          client_after_app_read
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some client_after_finished /\
        CS.step_model
          server_after_app_write
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some server_after_finished /\
        CS.conn_events_sent_seal_replay
          client
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
             CL.message_value = M.TlsHandshake sent_msg;
           } :: client_rest)
          client_raw_sent
          client_raw_received
          client_final /\
        CS.conn_events_received_decode_replay
          server
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
             CL.message_value = M.TlsHandshake received_msg;
           } :: server_rest)
          server_raw_sent
          server_raw_received
          server_final)
      (ensures
        exists pair client_tail_sent client_tail_received
          server_tail_sent server_tail_received.
          pair.pm_sender == client_after_app_read /\
          pair.pm_receiver == server_after_app_write /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal client_tail_sent server_tail_received /\
          CS.conn_events_sent_seal_replay
            client_after_finished
            client_rest
            client_tail_sent
            client_tail_received
            client_final /\
          CS.conn_events_received_decode_replay
            server_after_finished
            server_rest
            server_tail_sent
            server_tail_received
            server_final)

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

val lemma_protected_handshake_event_projection_pair_after_sender_received_network_head
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after pair.
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = skip_msg;
            }) == Some sender_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_sender_received_network_head_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = skip_msg;
            }) == Some sender_after /\
          CS.step_model
            sender_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after pair.
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = skip_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = skip_msg;
            }) == Some receiver_after /\
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_opposite_network_heads
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_skip_msg:M.tls_message)
  (receiver_skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after receiver_after pair.
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = sender_skip_msg;
            }) == Some sender_after /\
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = receiver_skip_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_opposite_network_heads_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_skip_msg:M.tls_message)
  (receiver_skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_skip_msg;
          } :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after receiver_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = sender_skip_msg;
            }) == Some sender_after /\
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = receiver_skip_msg;
            }) == Some receiver_after /\
          CS.step_model
            sender_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip:CS.local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnLocalEvent skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after pair.
          CS.step_model sender (CS.ConnLocalEvent skip) == Some sender_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip:CS.local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnLocalEvent skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model sender (CS.ConnLocalEvent skip) == Some sender_after /\
          CS.step_model
            sender_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (sender_after:CS.connection_model)
  (receiver:CS.connection_model)
  (sender_after_head:CS.connection_model)
  (receiver_after_head:CS.connection_model)
  (skip:CS.local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        CS.step_model sender (CS.ConnLocalEvent skip) == Some sender_after /\
        CS.step_model
          sender_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        CS.step_model
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.CS.model_record.CS.record_write ==
          R.next_seq sender_after.CS.model_record.CS.record_write /\
        receiver_after_head.CS.model_record.CS.record_read ==
          R.next_seq receiver.CS.model_record.CS.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnLocalEvent skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after_head receiver_after_head /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip:CS.local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnLocalEvent skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after pair.
          CS.step_model receiver (CS.ConnLocalEvent skip) == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)

val lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head_with_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (skip:CS.local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnLocalEvent skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          CS.step_model receiver (CS.ConnLocalEvent skip) == Some receiver_after /\
          CS.step_model
            sender
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          CS.step_model
            receiver_after
            (CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            }) == Some receiver_after_head /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)

val lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head_with_next_alignment_and_tails
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (receiver_after:CS.connection_model)
  (sender_after_head:CS.connection_model)
  (receiver_after_head:CS.connection_model)
  (skip:CS.local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list CS.conn_event)
  (receiver_rest:list CS.conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:CS.connection_model)
  (receiver_final:CS.connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        CS.step_model receiver (CS.ConnLocalEvent skip) == Some receiver_after /\
        CS.step_model
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        CS.step_model
          receiver_after
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.CS.model_record.CS.record_write ==
          R.next_seq sender.CS.model_record.CS.record_write /\
        receiver_after_head.CS.model_record.CS.record_read ==
          R.next_seq receiver_after.CS.model_record.CS.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        CS.conn_events_received_decode_replay
          receiver
          (CS.ConnLocalEvent skip :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists pair sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after_head receiver_after_head /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          CS.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          CS.conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
