module TLS13.ConnectionState.ProtectedWireSkipWrappers

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
open TLS13.ConnectionState.ProtectedWireRecordAlignment
open TLS13.ConnectionState.ProtectedWireHead

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_after_sender_received_network_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after pair.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = skip_msg;
            }) == Some sender_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists sender_after' pair.
      step_model sender skip_ev == Some sender_after' /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_received_network_event_preserves_write_read_record_material_alignment
      sender
      skip_msg
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_from_head_replays
      sender_after
      receiver
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_tail_sent
      sender_tail_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists sender_after' pair.
        step_model sender skip_ev == Some sender_after' /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (pair':protected_message_replay).
        step_model sender skip_ev == Some sender_after' /\
        pair'.pm_sender == sender_after' /\
        pair'.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair'
          sent_msg
          received_msg
      with sender_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_sender_received_network_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
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
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = skip_msg;
            }) == Some sender_after /\
          step_model
            sender_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver
            (ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender skip_ev == Some sender_after' /\
      step_model sender_after' sent_ev == Some sender_after_head /\
      step_model receiver received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_received_network_event_preserves_write_read_record_material_alignment
      sender
      skip_msg
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
      sender
      sender_after
      receiver
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender_after sent_ev == Some sender_after_head0 /\
      step_model receiver received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender_after /\
      pair0.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists receiver_after pair.
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = skip_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  returns
    exists receiver_after' pair.
      step_model receiver skip_ev == Some receiver_after' /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_sent_network_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip_msg
      receiver_after;
    lemma_protected_handshake_event_projection_pair_from_head_replays
      sender
      receiver_after
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_tail_sent
      receiver_tail_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists receiver_after' pair.
        step_model receiver skip_ev == Some receiver_after' /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (pair':protected_message_replay).
        step_model receiver skip_ev == Some receiver_after' /\
        pair'.pm_sender == sender /\
        pair'.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair'
          sent_msg
          received_msg
      with receiver_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = skip_msg;
          } :: ConnNetworkEvent {
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
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = skip_msg;
            }) == Some receiver_after /\
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver_after
            (ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received0 /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  returns
    exists receiver_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model receiver skip_ev == Some receiver_after' /\
      step_model sender sent_ev == Some sender_after_head /\
      step_model receiver_after' received_ev == Some receiver_after_head /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_sent_network_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip_msg
      receiver_after;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
      sender
      receiver
      receiver_after
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender sent_ev == Some sender_after_head0 /\
      step_model receiver_after received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender /\
      pair0.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists receiver_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        receiver_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_opposite_network_heads
  (sender:connection_model)
  (receiver:connection_model)
  (sender_skip_msg:M.tls_message)
  (receiver_skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_skip_msg;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          } :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        exists sender_after receiver_after pair.
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = sender_skip_msg;
            }) == Some sender_after /\
          step_model
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = receiver_skip_msg;
            }) == Some receiver_after /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
  let sender_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = sender_skip_msg;
  } in
  let receiver_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = receiver_skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists sender_after' receiver_after pair.
      step_model sender sender_skip_ev == Some sender_after' /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_after:connection_model)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_received_decode_replay
        receiver_after
        (received_ev :: receiver_rest)
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after' receiver_after' pair.
        step_model sender sender_skip_ev == Some sender_after' /\
        step_model receiver receiver_skip_ev == Some receiver_after' /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
    with _.
    ( lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
        sender
        sender_skip_msg
        sender_after
        receiver
        receiver_skip_msg
        receiver_after;
      lemma_protected_handshake_event_projection_pair_from_head_replays
        sender_after
        receiver_after
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
        sender_final
        receiver_final;
      eliminate exists (pair:protected_message_replay).
        pair.pm_sender == sender_after /\
        pair.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
      returns
        exists sender_after' receiver_after' pair.
          step_model sender sender_skip_ev == Some sender_after' /\
          step_model receiver receiver_skip_ev == Some receiver_after' /\
          pair.pm_sender == sender_after' /\
          pair.pm_receiver == receiver_after' /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
      with _.
      ( introduce exists
          (sender_after':connection_model)
          (receiver_after':connection_model)
          (pair':protected_message_replay).
          step_model sender sender_skip_ev == Some sender_after' /\
          step_model receiver receiver_skip_ev == Some receiver_after' /\
          pair'.pm_sender == sender_after' /\
          pair'.pm_receiver == receiver_after' /\
          protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg
        with sender_after receiver_after pair
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_opposite_network_heads_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (sender_skip_msg:M.tls_message)
  (receiver_skip_msg:M.tls_message)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = sender_skip_msg;
            } :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: sender_rest)
            sender_raw_sent
            sender_raw_received
            sender_final /\
        conn_events_received_decode_replay
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = receiver_skip_msg;
            } :: ConnNetworkEvent {
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
            step_model
              sender
              (ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = sender_skip_msg;
              }) == Some sender_after /\
            step_model
              receiver
              (ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = receiver_skip_msg;
              }) == Some receiver_after /\
            step_model
              sender_after
              (ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake sent_msg;
              }) == Some sender_after_head /\
            step_model
              receiver_after
              (ConnNetworkEvent {
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
            conn_events_sent_seal_replay
              sender_after_head
              sender_rest
              sender_tail_sent
              sender_tail_received
              sender_final /\
            conn_events_received_decode_replay
              receiver_after_head
              receiver_rest
              receiver_tail_sent
              receiver_tail_received
              receiver_final)
=
  let sender_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = sender_skip_msg;
  } in
  let receiver_skip_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = receiver_skip_msg;
  } in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after' receiver_after sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender sender_skip_ev == Some sender_after' /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      step_model sender_after' sent_ev == Some sender_after_head /\
      step_model receiver_after received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent0
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_after:connection_model)
      (receiver_tail_sent0:B.bytes)
      (receiver_tail_received0:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver_after /\
      Seq.equal sender_tail_sent0 receiver_tail_received0 /\
      conn_events_received_decode_replay
        receiver_after
        (received_ev :: receiver_rest)
        receiver_tail_sent0
        receiver_tail_received0
        receiver_final
    returns
      exists sender_after' receiver_after' sender_after_head receiver_after_head pair
        sender_tail_sent sender_tail_received
        receiver_tail_sent receiver_tail_received.
        step_model sender sender_skip_ev == Some sender_after' /\
        step_model receiver receiver_skip_ev == Some receiver_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
        conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
    with _.
    ( lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
        sender
        sender_skip_msg
        sender_after
        receiver
        receiver_skip_msg
        receiver_after;
      lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_tails
        sender
        sender_after
        receiver
        receiver_after
        sender_skip_ev
        receiver_skip_ev
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_raw_sent
        sender_raw_received
        receiver_raw_sent
        receiver_raw_received
        sender_final
        receiver_final;
      eliminate exists
        (sender_after_head0:connection_model)
        (receiver_after_head0:connection_model)
        (pair0:protected_message_replay)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes)
        (receiver_tail_sent:B.bytes)
        (receiver_tail_received:B.bytes).
        step_model sender_after sent_ev == Some sender_after_head0 /\
        step_model receiver_after received_ev == Some receiver_after_head0 /\
        pair0.pm_sender == sender_after /\
        pair0.pm_receiver == receiver_after /\
        protected_handshake_event_projection_pair
            pair0
            sent_msg
            received_msg /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
            sender_after_head0
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
        conn_events_received_decode_replay
            receiver_after_head0
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
      returns
        exists sender_after' receiver_after' sender_after_head receiver_after_head pair
            sender_tail_sent' sender_tail_received'
            receiver_tail_sent' receiver_tail_received'.
            step_model sender sender_skip_ev == Some sender_after' /\
            step_model receiver receiver_skip_ev == Some receiver_after' /\
            step_model sender_after' sent_ev == Some sender_after_head /\
            step_model receiver_after' received_ev == Some receiver_after_head /\
            pair.pm_sender == sender_after' /\
            pair.pm_receiver == receiver_after' /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after_head
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after_head
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
      with _.
      ( introduce exists
            (sender_after':connection_model)
            (receiver_after':connection_model)
            (sender_after_head:connection_model)
            (receiver_after_head:connection_model)
            (pair:protected_message_replay)
            (sender_tail_sent':B.bytes)
            (sender_tail_received':B.bytes)
            (receiver_tail_sent':B.bytes)
            (receiver_tail_received':B.bytes).
            step_model sender sender_skip_ev == Some sender_after' /\
            step_model receiver receiver_skip_ev == Some receiver_after' /\
            step_model sender_after' sent_ev == Some sender_after_head /\
            step_model receiver_after' received_ev == Some receiver_after_head /\
            pair.pm_sender == sender_after' /\
            pair.pm_receiver == receiver_after' /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after_head
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after_head
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
        with
            sender_after
            receiver_after
            sender_after_head0
            receiver_after_head0
            pair0
            sender_tail_sent
            sender_tail_received
            receiver_tail_sent
            receiver_tail_received
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
            sender
            (ConnLocalEvent skip :: ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: sender_rest)
            sender_raw_sent
            sender_raw_received
            sender_final /\
        conn_events_received_decode_replay
            receiver
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: receiver_rest)
            receiver_raw_sent
            receiver_raw_received
            receiver_final)
      (ensures
        exists sender_after pair.
            step_model sender (ConnLocalEvent skip) == Some sender_after /\
            pair.pm_sender == sender_after /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg)
=
  let skip_ev = ConnLocalEvent skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  returns
    exists sender_after' pair.
      step_model sender skip_ev == Some sender_after' /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      skip
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head
      sender
      sender_after
      receiver
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists sender_after' pair.
        step_model sender skip_ev == Some sender_after' /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (pair':protected_message_replay).
        step_model sender skip_ev == Some sender_after' /\
        pair'.pm_sender == sender_after' /\
        pair'.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg
      with sender_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnLocalEvent skip :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
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
          step_model sender (ConnLocalEvent skip) == Some sender_after /\
          step_model
            sender_after
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver
            (ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnLocalEvent skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    skip_ev
    (sent_ev :: sender_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender_after:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender_after /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender_after
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  returns
    exists sender_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model sender skip_ev == Some sender_after' /\
      step_model sender_after' sent_ev == Some sender_after_head /\
      step_model receiver received_ev == Some receiver_after_head /\
      pair.pm_sender == sender_after' /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      skip
      sender_after
      receiver;
    lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
      sender
      sender_after
      receiver
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender_after sent_ev == Some sender_after_head0 /\
      step_model receiver received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender_after /\
      pair0.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists sender_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (sender_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender skip_ev == Some sender_after' /\
        step_model sender_after' sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after' /\
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_sender_non_install_local_head_with_next_alignment_and_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (sender_after_head:connection_model)
  (receiver_after_head:connection_model)
  (skip:local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        step_model sender (ConnLocalEvent skip) == Some sender_after /\
        step_model
          sender_after
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.model_record.record_write ==
          R.next_seq sender_after.model_record.record_write /\
        receiver_after_head.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnLocalEvent skip :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
    sender
    skip
    sender_after
    receiver;
  lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_next_alignment_and_tails
    sender
    sender_after
    receiver
    sender_after_head
    receiver_after_head
    (ConnLocalEvent skip)
    sent_msg
    received_msg
    sender_rest
    receiver_rest
    sender_raw_sent
    sender_raw_received
    receiver_raw_sent
    receiver_raw_received
    sender_final
    receiver_final

let lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            } :: sender_rest)
            sender_raw_sent
            sender_raw_received
            sender_final /\
        conn_events_received_decode_replay
            receiver
            (ConnLocalEvent skip :: ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake received_msg;
            } :: receiver_rest)
            receiver_raw_sent
            receiver_raw_received
            receiver_final)
      (ensures
        exists receiver_after pair.
            step_model receiver (ConnLocalEvent skip) == Some receiver_after /\
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver_after /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg)
=
  let skip_ev = ConnLocalEvent skip in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  returns
    exists receiver_after' pair.
      step_model receiver skip_ev == Some receiver_after' /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
  with _.
  ( lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip
      receiver_after;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head
      sender
      receiver
      receiver_after
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists (pair:protected_message_replay).
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg
    returns
      exists receiver_after' pair.
        step_model receiver skip_ev == Some receiver_after' /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (pair':protected_message_replay).
        step_model receiver skip_ev == Some receiver_after' /\
        pair'.pm_sender == sender /\
        pair'.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg
      with receiver_after pair
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (skip:local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnLocalEvent skip :: ConnNetworkEvent {
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
          step_model receiver (ConnLocalEvent skip) == Some receiver_after /\
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after_head /\
          step_model
            receiver_after
            (ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let skip_ev = ConnLocalEvent skip in
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_received_replay_skip_empty_head_preserves_peer_stream
    sender_raw_sent
    receiver
    skip_ev
    (received_ev :: receiver_rest)
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver_after:connection_model)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver_after /\
    Seq.equal sender_raw_sent receiver_tail_received0 /\
    conn_events_received_decode_replay
      receiver_after
      (received_ev :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  returns
    exists receiver_after' sender_after_head receiver_after_head pair
      sender_tail_sent sender_tail_received
      receiver_tail_sent receiver_tail_received.
      step_model receiver skip_ev == Some receiver_after' /\
      step_model sender sent_ev == Some sender_after_head /\
      step_model receiver_after' received_ev == Some receiver_after_head /\
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after' /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
  with _.
  ( lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      sender
      receiver
      skip
      receiver_after;
    lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
      sender
      receiver
      receiver_after
      skip_ev
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_raw_sent
      receiver_raw_received
      sender_final
      receiver_final;
    eliminate exists
      (sender_after_head0:connection_model)
      (receiver_after_head0:connection_model)
      (pair0:protected_message_replay)
      (sender_tail_sent:B.bytes)
      (sender_tail_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      step_model sender sent_ev == Some sender_after_head0 /\
      step_model receiver_after received_ev == Some receiver_after_head0 /\
      pair0.pm_sender == sender /\
      pair0.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair0
        sent_msg
        received_msg /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_sent_seal_replay
        sender_after_head0
        sender_rest
        sender_tail_sent
        sender_tail_received
        sender_final /\
      conn_events_received_decode_replay
        receiver_after_head0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    returns
      exists receiver_after' sender_after_head receiver_after_head pair
        sender_tail_sent' sender_tail_received'
        receiver_tail_sent' receiver_tail_received'.
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
    with _.
    ( introduce exists
        (receiver_after':connection_model)
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model receiver skip_ev == Some receiver_after' /\
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after' received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after' /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender_after_head
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_after_head
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        receiver_after
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_receiver_non_install_local_head_with_next_alignment_and_tails
  (sender:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_after_head:connection_model)
  (receiver_after_head:connection_model)
  (skip:local_event)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (sender_rest:list conn_event)
  (receiver_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys skip /\
        write_read_record_material_aligned sender receiver /\
        step_model receiver (ConnLocalEvent skip) == Some receiver_after /\
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after_head /\
        step_model
          receiver_after
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after_head /\
        sender_after_head.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after_head.model_record.record_read ==
          R.next_seq receiver_after.model_record.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnLocalEvent skip :: ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after_head
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after_head
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
    sender
    receiver
    skip
    receiver_after;
  lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_next_alignment_and_tails
    sender
    receiver
    receiver_after
    sender_after_head
    receiver_after_head
    (ConnLocalEvent skip)
    sent_msg
    received_msg
    sender_rest
    receiver_rest
    sender_raw_sent
    sender_raw_received
    receiver_raw_sent
    receiver_raw_received
    sender_final
    receiver_final
#pop-options
