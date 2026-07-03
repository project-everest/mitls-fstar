module TLS13.ConnectionState.ProtectedWireSkipWrappers

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
