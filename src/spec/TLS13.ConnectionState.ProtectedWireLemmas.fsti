module TLS13.ConnectionState.ProtectedWireLemmas

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

type protected_message_replay = {
  pm_sender: CS.connection_model;
  pm_receiver: CS.connection_model;
  pm_raw_sent: B.bytes;
  pm_raw_received: B.bytes;
}

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

noextract
let protected_handshake_wire_round_trip_message (msg:M.handshake_msg) : prop =
  match msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ -> True
  | _ -> False

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
