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
