module TLS13.ConnectionState.ProtectedWireHead

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (sender_ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (sender_ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)
      (ensures
        TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
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
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection
          model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)
      (ensures
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
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
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        B.length sender_delta == B.length receiver_delta /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
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
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
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
        TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
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
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender_after.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver_after.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender_after.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver_after.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
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
        TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
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
          TLS13.Spec.StateMachine.Replay.conn_events_sent_seal_replay
            sender_after2
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          TLS13.Spec.StateMachine.Replay.conn_events_received_decode_replay
            receiver_after2
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
