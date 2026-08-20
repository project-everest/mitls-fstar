module TLS13.ConnectionState.ProtectedWireHead

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
module PWP = TLS13.ConnectionState.ProtectedWireProjection

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay
open TLS13.ConnectionState.ProtectedWireBase
open TLS13.ConnectionState.ProtectedWireStream
open TLS13.ConnectionState.ProtectedWireReplay
open TLS13.ConnectionState.ProtectedWireRecordAlignment

let lemma_sent_replay_skip_empty_head_preserves_peer_stream
  (sender:connection_model)
  (ev:conn_event)
  (sender_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        conn_events_sent_seal_replay
          sender
          (ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        (match ev with
         | ConnLocalEvent _ -> True
           | ConnProtectedHandshake _ -> True
           | ConnCleartextHandshake _ -> True
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists sender1 sender_tail_sent sender_tail_received.
          legal_event sender ev /\
          step_model sender ev == Some sender1 /\
          Seq.equal sender_tail_sent receiver_raw_received /\
          conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final)
=
  lemma_conn_events_sent_seal_replay_head
    sender
    ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event sender ev /\
    step_model sender ev == Some sender1 /\
    event_raw_delta_legal sender ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection sender ev delta_sent /\
    Seq.equal sender_raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal sender_raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay
      sender1
      sender_rest
      tail_sent
      tail_received
      sender_final
  with
  ( match ev with
    | ConnLocalEvent _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnProtectedHandshake _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnCleartextHandshake _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnNetworkEvent msg ->
      assert (msg.CL.message_direction == CL.Received);
      assert (Seq.equal delta_sent B.empty);
    lemma_equal_streams_skip_empty_left
      sender_raw_sent
      receiver_raw_received
      tail_sent;
    introduce exists
      (sender1':connection_model)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes).
      legal_event sender ev /\
      step_model sender ev == Some sender1' /\
      Seq.equal sender_tail_sent' receiver_raw_received /\
      conn_events_sent_seal_replay
        sender1'
        sender_rest
        sender_tail_sent'
        sender_tail_received'
        sender_final
    with sender1 tail_sent tail_received
    and () )

let lemma_received_replay_skip_empty_head_preserves_peer_stream
  (sender_raw_sent:B.bytes)
  (receiver:connection_model)
  (ev:conn_event)
  (receiver_rest:list conn_event)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (receiver_final:connection_model)
  : Lemma
      (requires
        Seq.equal sender_raw_sent receiver_raw_received /\
        conn_events_received_decode_replay
          receiver
          (ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match ev with
         | ConnLocalEvent _ -> True
           | ConnProtectedHandshake step -> not step.protected_handshake_head
           | ConnCleartextHandshake _ -> False
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists receiver1 receiver_tail_sent receiver_tail_received.
          legal_event receiver ev /\
          step_model receiver ev == Some receiver1 /\
          Seq.equal sender_raw_sent receiver_tail_received /\
          conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_conn_events_received_decode_replay_head
    receiver
    ev
    receiver_rest
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event receiver ev /\
    step_model receiver ev == Some receiver1 /\
    event_raw_delta_legal receiver ev delta_sent delta_received /\
    received_event_nonempty_decode_projection receiver ev delta_received /\
    Seq.equal receiver_raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal receiver_raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      receiver1
      receiver_rest
      tail_sent
      tail_received
      receiver_final
  with
  ( match ev with
    | ConnLocalEvent _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnProtectedHandshake _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnCleartextHandshake _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnNetworkEvent msg ->
      assert (msg.CL.message_direction == CL.Sent);
      assert (Seq.equal delta_received B.empty);
    lemma_equal_streams_skip_empty_right
      sender_raw_sent
      receiver_raw_received
      tail_received;
    introduce exists
      (receiver1':connection_model)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      legal_event receiver ev /\
      step_model receiver ev == Some receiver1' /\
      Seq.equal sender_raw_sent receiver_tail_received' /\
      conn_events_received_decode_replay
        receiver1'
        receiver_rest
        receiver_tail_sent'
        receiver_tail_received'
        receiver_final
    with receiver1 tail_sent tail_received
    and () )

let lemma_sent_replay_skip_zero_received_head_preserves_peer_stream
  (receiver_raw_sent:B.bytes)
  (sender:connection_model)
  (ev:conn_event)
  (sender_rest:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (sender_final:connection_model)
  : Lemma
      (requires
        Seq.equal receiver_raw_sent sender_raw_received /\
        conn_events_sent_seal_replay
          sender
          (ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        (match ev with
         | ConnLocalEvent _ -> True
           | ConnProtectedHandshake step -> not step.protected_handshake_head
           | ConnCleartextHandshake _ -> False
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists sender1 sender_tail_sent sender_tail_received.
          legal_event sender ev /\
          step_model sender ev == Some sender1 /\
          Seq.equal receiver_raw_sent sender_tail_received /\
          conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final)
=
  lemma_conn_events_sent_seal_replay_head
    sender
    ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event sender ev /\
    step_model sender ev == Some sender1 /\
    event_raw_delta_legal sender ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection sender ev delta_sent /\
    Seq.equal sender_raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal sender_raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay
      sender1
      sender_rest
      tail_sent
      tail_received
      sender_final
  with
  ( match ev with
    | ConnLocalEvent _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnProtectedHandshake _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnCleartextHandshake _ ->
      assert (Seq.equal delta_received B.empty)
    | ConnNetworkEvent msg ->
      assert (msg.CL.message_direction == CL.Sent);
      assert (Seq.equal delta_received B.empty);
    lemma_equal_streams_skip_empty_right
      receiver_raw_sent
      sender_raw_received
      tail_received;
    introduce exists
      (sender1':connection_model)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes).
      legal_event sender ev /\
      step_model sender ev == Some sender1' /\
      Seq.equal receiver_raw_sent sender_tail_received' /\
      conn_events_sent_seal_replay
        sender1'
        sender_rest
        sender_tail_sent'
        sender_tail_received'
        sender_final
    with sender1 tail_sent tail_received
    and () )

let lemma_received_replay_skip_zero_sent_head_preserves_peer_stream
  (receiver:connection_model)
  (ev:conn_event)
  (receiver_rest:list conn_event)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_final:connection_model)
  : Lemma
      (requires
        Seq.equal receiver_raw_sent sender_raw_received /\
        conn_events_received_decode_replay
          receiver
          (ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match ev with
         | ConnLocalEvent _ -> True
           | ConnProtectedHandshake _ -> True
           | ConnCleartextHandshake _ -> True
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists receiver1 receiver_tail_sent receiver_tail_received.
          legal_event receiver ev /\
          step_model receiver ev == Some receiver1 /\
          Seq.equal receiver_tail_sent sender_raw_received /\
          conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_conn_events_received_decode_replay_head
    receiver
    ev
    receiver_rest
    receiver_raw_sent
    receiver_raw_received
    receiver_final;
  eliminate exists
    (receiver1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event receiver ev /\
    step_model receiver ev == Some receiver1 /\
    event_raw_delta_legal receiver ev delta_sent delta_received /\
    received_event_nonempty_decode_projection receiver ev delta_received /\
    Seq.equal receiver_raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal receiver_raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      receiver1
      receiver_rest
      tail_sent
      tail_received
      receiver_final
  with
  ( match ev with
    | ConnLocalEvent _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnProtectedHandshake _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnCleartextHandshake _ ->
      assert (Seq.equal delta_sent B.empty)
    | ConnNetworkEvent msg ->
      assert (msg.CL.message_direction == CL.Received);
      assert (Seq.equal delta_sent B.empty);
    lemma_equal_streams_skip_empty_left
      receiver_raw_sent
      sender_raw_received
      tail_sent;
    introduce exists
      (receiver1':connection_model)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      legal_event receiver ev /\
      step_model receiver ev == Some receiver1' /\
      Seq.equal receiver_tail_sent' sender_raw_received /\
      conn_events_received_decode_replay
        receiver1'
        receiver_rest
        receiver_tail_sent'
        receiver_tail_received'
        receiver_final
    with receiver1 tail_sent tail_received
    and () )

let lemma_sent_received_replays_skip_zero_opposite_heads_preserve_peer_stream
  (sender:connection_model)
  (receiver:connection_model)
  (sender_ev:conn_event)
  (receiver_ev:conn_event)
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
        Seq.equal receiver_raw_sent sender_raw_received /\
        conn_events_sent_seal_replay
          sender
          (sender_ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match sender_ev with
         | ConnLocalEvent _ -> True
           | ConnProtectedHandshake step -> not step.protected_handshake_head
           | ConnCleartextHandshake _ -> False
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
          (match receiver_ev with
           | ConnLocalEvent _ -> True
           | ConnProtectedHandshake _ -> True
           | ConnCleartextHandshake _ -> True
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received))
      (ensures
        exists sender1 receiver1
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          legal_event sender sender_ev /\
          step_model sender sender_ev == Some sender1 /\
          legal_event receiver receiver_ev /\
          step_model receiver receiver_ev == Some receiver1 /\
          Seq.equal receiver_tail_sent sender_tail_received /\
          conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_sent_replay_skip_zero_received_head_preserves_peer_stream
    receiver_raw_sent
    sender
    sender_ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_ev /\
    step_model sender sender_ev == Some sender1 /\
    Seq.equal receiver_raw_sent sender_tail_received /\
    conn_events_sent_seal_replay
      sender1
      sender_rest
      sender_tail_sent
      sender_tail_received
      sender_final
  with
  ( lemma_received_replay_skip_zero_sent_head_preserves_peer_stream
      receiver
      receiver_ev
      receiver_rest
      receiver_raw_sent
      receiver_raw_received
      sender_tail_received
      receiver_final;
    eliminate exists
      (receiver1:connection_model)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_ev /\
      step_model receiver receiver_ev == Some receiver1 /\
      Seq.equal receiver_tail_sent sender_tail_received /\
      conn_events_received_decode_replay
        receiver1
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    with
    ( introduce exists
        (sender1':connection_model)
        (receiver1':connection_model)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        legal_event sender sender_ev /\
        step_model sender sender_ev == Some sender1' /\
        legal_event receiver receiver_ev /\
        step_model receiver receiver_ev == Some receiver1' /\
        Seq.equal receiver_tail_sent' sender_tail_received' /\
        conn_events_sent_seal_replay
          sender1'
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver1'
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender1
        receiver1
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
  (sender:connection_model)
  (receiver:connection_model)
  (sender_ev:conn_event)
  (receiver_ev:conn_event)
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
        Seq.equal sender_raw_sent receiver_raw_received /\
        conn_events_sent_seal_replay
          sender
          (sender_ev :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_ev :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        (match sender_ev with
         | ConnLocalEvent _ -> True
           | ConnProtectedHandshake _ -> True
           | ConnCleartextHandshake _ -> True
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
          (match receiver_ev with
           | ConnLocalEvent _ -> True
           | ConnProtectedHandshake step -> not step.protected_handshake_head
           | ConnCleartextHandshake _ -> False
           | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent))
      (ensures
        exists sender1 receiver1
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
          legal_event sender sender_ev /\
          step_model sender sender_ev == Some sender1 /\
          legal_event receiver receiver_ev /\
          step_model receiver receiver_ev == Some receiver1 /\
          Seq.equal sender_tail_sent receiver_tail_received /\
          conn_events_sent_seal_replay
            sender1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  lemma_sent_replay_skip_empty_head_preserves_peer_stream
    sender
    sender_ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    receiver_raw_received
    sender_final;
  eliminate exists
    (sender1:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_ev /\
    step_model sender sender_ev == Some sender1 /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      sender_rest
      sender_tail_sent
      sender_tail_received
      sender_final
  with
  ( lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent
      receiver
      receiver_ev
      receiver_rest
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver1:connection_model)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_ev /\
      step_model receiver receiver_ev == Some receiver1 /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_received_decode_replay
        receiver1
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    with
    ( introduce exists
        (sender1':connection_model)
        (receiver1':connection_model)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        legal_event sender sender_ev /\
        step_model sender sender_ev == Some sender1' /\
        legal_event receiver receiver_ev /\
        step_model receiver receiver_ev == Some receiver1' /\
        Seq.equal sender_tail_sent' receiver_tail_received' /\
        conn_events_sent_seal_replay
          sender1'
          sender_rest
          sender_tail_sent'
          sender_tail_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver1'
          receiver_rest
          receiver_tail_sent'
          receiver_tail_received'
          receiver_final
      with
        sender1
        receiver1
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

#push-options "--z3rlimit 10"
let lemma_sent_event_nonempty_seal_projection_protected
  (model:connection_model)
  (msg:M.tls_message)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        network_message_is_cleartext CL.Sent msg == false /\
        protected_record_count CL.Sent msg == 1 /\
        event_raw_delta_legal
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent
          delta_received /\
        sent_event_nonempty_seal_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)
      (ensures
        sent_event_seal_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          })
          delta_sent)
=
  if B.length delta_sent == 0 then
    begin
      assert (raw_records_exactly delta_sent T.Application_data 1);
      CSL.lemma_raw_records_exactly_one_parse_record delta_sent T.Application_data;
      eliminate exists (fragment:B.bytes).
        W.parse_record delta_sent ==
          Some (T.Application_data, fragment, B.length delta_sent)
      with
      ( W.lemma_parse_record_implies_parse_record_wire delta_sent;
        W.lemma_parse_record_wire_some_consumed_positive
          delta_sent
          T.Application_data
          fragment
          (B.length delta_sent);
        assert False )
    end
  else
    assert (sent_event_seal_projection
      model
      (ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = msg;
      })
      delta_sent)

#restart-solver
let lemma_received_event_nonempty_decode_projection_protected
  (model:connection_model)
  (msg:M.tls_message)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  : Lemma
      (requires
        network_message_is_cleartext CL.Received msg == false /\
        protected_record_count CL.Received msg == 1 /\
        event_raw_delta_legal
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_sent
          delta_received /\
        received_event_nonempty_decode_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)
      (ensures
        received_event_decode_projection
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          })
          delta_received)
=
  if B.length delta_received == 0 then
    begin
      assert (raw_records_exactly delta_received T.Application_data 1);
      CSL.lemma_raw_records_exactly_one_parse_record delta_received T.Application_data;
      eliminate exists (fragment:B.bytes).
        W.parse_record delta_received ==
          Some (T.Application_data, fragment, B.length delta_received)
      with
      ( W.lemma_parse_record_implies_parse_record_wire delta_received;
        W.lemma_parse_record_wire_some_consumed_positive
          delta_received
          T.Application_data
          fragment
          (B.length delta_received);
        assert False )
    end
  else
    assert (received_event_decode_projection
      model
      (ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = msg;
      })
      delta_received)
#pop-options

#push-options "--z3rlimit 20"
let lemma_single_message_sender_normalizes_received_handshake_head
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (receiver_head:conn_event)
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
        protected_handshake_buffer_empty receiver /\
        protected_handshake_wire_round_trip_message sent_msg /\
        (match receiver_head with
         | ConnNetworkEvent directed ->
           directed.CL.message_direction == CL.Received /\
           directed.CL.message_value == M.TlsHandshake received_msg
         | ConnProtectedHandshake step ->
           (* A BUFFERING step delivers no message -- it sets a record's
              plaintext aside so that a handshake message spanning several
              records can be reassembled -- and its
              [protected_handshake_message] field is inert.  Pinning that
              inert field to [received_msg] would be meaningless, so a
              caller reasoning about a step that DELIVERS [received_msg]
              must say the step is not a buffering one. *)
           step.protected_handshake_buffering == false /\
           step.protected_handshake_message == received_msg
         (* A cleartext buffering step delivers no message either. *)
         | ConnCleartextHandshake _ ->
           False
         | ConnLocalEvent _ ->
           False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
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
          (receiver_head :: receiver_rest)
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
      (ensures
        received_handshake_head_normal_form received_msg receiver_head /\
        normalized_received_handshake_replay
          receiver
          received_msg
          receiver_rest
          receiver_raw_sent
          receiver_raw_received
          receiver_final)
=
  let sender_head = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  lemma_conn_events_sent_seal_replay_head
    sender
    sender_head
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender_model1:connection_model)
    (sender_delta_sent:B.bytes)
    (sender_delta_received:B.bytes)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_head /\
    step_model sender sender_head == Some sender_model1 /\
    event_raw_delta_legal
      sender
      sender_head
      sender_delta_sent
      sender_delta_received /\
    sent_event_nonempty_seal_projection
      sender
      sender_head
      sender_delta_sent /\
    Seq.equal
      sender_raw_sent
      (B.append sender_delta_sent sender_tail_sent) /\
    Seq.equal
      sender_raw_received
      (B.append sender_delta_received sender_tail_received) /\
    conn_events_sent_seal_replay
      sender_model1
      sender_rest
      sender_tail_sent
      sender_tail_received
      sender_final
  with
  ( lemma_conn_events_received_decode_replay_head
      receiver
      receiver_head
      receiver_rest
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_model1:connection_model)
      (receiver_delta_sent:B.bytes)
      (receiver_delta_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_head /\
      step_model receiver receiver_head == Some receiver_model1 /\
      event_raw_delta_legal
        receiver
        receiver_head
        receiver_delta_sent
        receiver_delta_received /\
      received_event_nonempty_decode_projection
        receiver
        receiver_head
        receiver_delta_received /\
      Seq.equal
        receiver_raw_sent
        (B.append receiver_delta_sent receiver_tail_sent) /\
      Seq.equal
        receiver_raw_received
        (B.append receiver_delta_received receiver_tail_received) /\
      conn_events_received_decode_replay
        receiver_model1
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    with
    ( match receiver_head with
      | ConnNetworkEvent directed ->
        assert (directed == {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake received_msg;
        });
        assert (receiver_head == ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake received_msg;
        })
      | ConnLocalEvent _ ->
        assert False
      | ConnProtectedHandshake step ->
        if step.protected_handshake_head
        then
          begin
            lemma_sent_event_nonempty_seal_projection_protected
              sender
              (M.TlsHandshake sent_msg)
              sender_delta_sent
              sender_delta_received;
            assert (sent_event_seal_projection
              sender
              sender_head
              sender_delta_sent);
            assert (sent_single_protected_message_seal
              sender
              (M.TlsHandshake sent_msg)
              sender_delta_sent);
            CSL.lemma_raw_records_exactly_one_parse_record
              receiver_delta_received
              T.Application_data;
            assert (B.length receiver_delta_received > 0);
            assert (received_event_decode_projection
              receiver
              receiver_head
              receiver_delta_received);
            eliminate exists (sender_outer:M.sealed_record).
              W.parse_record sender_delta_sent ==
                Some
                  (T.Application_data,
                   sender_outer,
                   B.length sender_delta_sent) /\
              R.seal
                sender.model_record.record_write
                (record_header_aad sender_delta_sent)
                {
                  R.content_type = T.Application_data;
                  R.fragment =
                    sent_tls_inner_plaintext_fragment
                      (M.TlsHandshake sent_msg);
                } ==
                Some
                  (sender_outer,
                   R.next_seq sender.model_record.record_write)
            with
            ( W.lemma_parse_record_implies_parse_record_wire sender_delta_sent;
              eliminate exists
                (receiver_outer:B.bytes)
                (opened:B.bytes)
                (plaintext:M.plaintext).
                W.parse_record_wire receiver_delta_received ==
                  Some
                    (T.Application_data,
                     receiver_outer,
                     B.length receiver_delta_received) /\
                received_record_opened
                  receiver
                  receiver_delta_received
                  receiver_outer
                  opened /\
                W.parse_plaintext opened == Some plaintext /\
                plaintext.M.content_type == T.Handshake /\
                Seq.equal
                  plaintext.M.fragment
                  step.protected_handshake_fragment /\
                step.protected_handshake_offset <=
                  B.length step.protected_handshake_fragment /\
                W.parse_handshake
                  (Seq.slice
                    step.protected_handshake_fragment
                    step.protected_handshake_offset
                    (B.length step.protected_handshake_fragment)) ==
                  Some
                    (step.protected_handshake_message,
                     step.protected_handshake_consumed)
              with
              ( lemma_equal_stream_record_head_lengths
                  sender_raw_sent
                  receiver_raw_received
                  sender_delta_sent
                  sender_tail_sent
                  receiver_delta_received
                  receiver_tail_received
                  T.Application_data
                  sender_outer
                  T.Application_data
                  receiver_outer;
                lemma_append_heads_equal_same_len
                  sender_delta_sent
                  sender_tail_sent
                  receiver_delta_received
                  receiver_tail_received;
                assert (Seq.equal
                  sender_delta_sent
                  receiver_delta_received);
                Seq.lemma_eq_elim
                  sender_delta_sent
                  receiver_delta_received;
                PWP.lemma_single_protected_message_seal_saturates_protected_head
                  sender
                  receiver
                  sent_msg
                  step
                  receiver_delta_received;
                assert (single_message_head_step_shape step);
                lemma_single_message_head_step_replay_normalizes
                  receiver
                  step
                  receiver_rest
                  receiver_raw_sent
                  receiver_raw_received
                  receiver_final ) )
          end
        else
          begin
            assert (Seq.equal
              step.protected_handshake_fragment
              receiver.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes);
            assert (step.protected_handshake_offset ==
              receiver.model_handshake.hs_buffers.hb_encrypted_server_handshake_parsed);
            Seq.lemma_eq_elim
              receiver.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes
              B.empty;
            assert (Seq.equal
              step.protected_handshake_fragment
              B.empty);
            Seq.lemma_eq_elim
              step.protected_handshake_fragment
              B.empty;
            assert False
          end ) )
#pop-options

#push-options "--z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_aligned_heads
  (sender:connection_model)
  (receiver:connection_model)
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
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        B.length sender_delta == B.length receiver_delta /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
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
=
  Seq.lemma_eq_elim sender_stream receiver_stream;
  Seq.lemma_eq_elim sender_stream (B.append sender_delta sender_tail);
  assert (Seq.equal
    (B.append sender_delta sender_tail)
    (B.append receiver_delta receiver_tail));
  lemma_raw_delta_heads_equal_same_len
    sender_delta
    sender_tail
    receiver_delta
    receiver_tail;
  assert (Seq.equal sender_delta receiver_delta)
#pop-options

#push-options "--z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_equal_stream_heads
  (sender:connection_model)
  (receiver:connection_model)
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
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_stream receiver_stream /\
        Seq.equal sender_stream (B.append sender_delta sender_tail) /\
        Seq.equal receiver_stream (B.append receiver_delta receiver_tail) /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
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
=
  match sent_msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ ->
    match received_msg with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ ->
      assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
      assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
      assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
      assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
      assert (sent_single_protected_message_seal
        sender
        (M.TlsHandshake sent_msg)
        sender_delta);
      assert (received_single_protected_message_decode
        receiver
        (M.TlsHandshake received_msg)
        receiver_delta);
      eliminate exists (sender_ciphertext:B.bytes).
        W.parse_record sender_delta ==
          Some (T.Application_data, sender_ciphertext, B.length sender_delta) /\
        R.seal
          sender.model_record.record_write
          (record_header_aad sender_delta)
          {
            R.content_type = T.Application_data;
            R.fragment = sent_tls_inner_plaintext_fragment (M.TlsHandshake sent_msg);
          } ==
          Some (sender_ciphertext, R.next_seq sender.model_record.record_write)
      with
      ( W.lemma_parse_record_implies_parse_record_wire sender_delta;
        assert (W.parse_record_wire sender_delta ==
          Some (T.Application_data, sender_ciphertext, B.length sender_delta));
        eliminate exists
          (receiver_fragment:B.bytes)
          (opened:B.bytes)
          (plaintext:M.plaintext).
          W.parse_record_wire receiver_delta ==
            Some (T.Application_data, receiver_fragment, B.length receiver_delta) /\
          received_record_opened receiver receiver_delta receiver_fragment opened /\
          W.parse_plaintext opened == Some plaintext /\
          W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
            Some (M.TlsHandshake received_msg)
        with
        ( lemma_equal_stream_record_head_lengths
            sender_stream
            receiver_stream
            sender_delta
            sender_tail
            receiver_delta
            receiver_tail
            T.Application_data
            sender_ciphertext
            T.Application_data
            receiver_fragment;
          assert (B.length sender_delta == B.length receiver_delta);
          lemma_protected_handshake_event_projection_pair_from_aligned_heads
            sender
            receiver
            sent_msg
            received_msg
            sender_stream
            receiver_stream
            sender_delta
            sender_tail
            receiver_delta
            receiver_tail ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
let lemma_protected_handshake_event_tails_equal_from_equal_stream_heads
  (sender:connection_model)
  (receiver:connection_model)
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
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          sender_delta /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          receiver_delta)
      (ensures Seq.equal sender_tail receiver_tail)
=
  match sent_msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ ->
    match received_msg with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ ->
      assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
      assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
      assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
      assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
      assert (sent_single_protected_message_seal
        sender
        (M.TlsHandshake sent_msg)
        sender_delta);
      assert (received_single_protected_message_decode
        receiver
        (M.TlsHandshake received_msg)
        receiver_delta);
      eliminate exists (sender_ciphertext:M.sealed_record).
        W.parse_record sender_delta ==
          Some (T.Application_data, sender_ciphertext, B.length sender_delta) /\
        R.seal
          sender.model_record.record_write
          (record_header_aad sender_delta)
          {
            R.content_type = T.Application_data;
            R.fragment = sent_tls_inner_plaintext_fragment (M.TlsHandshake sent_msg);
          } ==
          Some (sender_ciphertext, R.next_seq sender.model_record.record_write)
      with
      ( W.lemma_parse_record_implies_parse_record_wire sender_delta;
        assert (W.parse_record_wire sender_delta ==
          Some (T.Application_data, sender_ciphertext, B.length sender_delta));
        eliminate exists
          (receiver_fragment:M.sealed_record)
          (opened:B.bytes)
          (plaintext:M.plaintext).
          W.parse_record_wire receiver_delta ==
            Some (T.Application_data, receiver_fragment, B.length receiver_delta) /\
          received_record_opened receiver receiver_delta receiver_fragment opened /\
          W.parse_plaintext opened == Some plaintext /\
          W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
            Some (M.TlsHandshake received_msg)
        with
        ( lemma_equal_stream_record_head_lengths
            sender_stream
            receiver_stream
            sender_delta
            sender_tail
            receiver_delta
            receiver_tail
            T.Application_data
            sender_ciphertext
            T.Application_data
            receiver_fragment;
          assert (B.length sender_delta == B.length receiver_delta);
          Seq.lemma_eq_elim sender_stream receiver_stream;
          Seq.lemma_eq_elim sender_stream (B.append sender_delta sender_tail);
          assert (Seq.equal
            (B.append sender_delta sender_tail)
            (B.append receiver_delta receiver_tail));
          lemma_append_tails_equal_same_len
            sender_delta
            sender_tail
            receiver_delta
            receiver_tail ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_head_replays
  (sender:connection_model)
  (receiver:connection_model)
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
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
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
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  match sent_msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ ->
    match received_msg with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ ->
      lemma_conn_events_sent_seal_replay_head
        sender
        sent_ev
        sender_rest
        sender_raw_sent
        sender_raw_received
        sender_final;
      eliminate exists
        (sender_model1:connection_model)
        (sender_delta_sent:B.bytes)
        (sender_delta_received:B.bytes)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes).
        legal_event sender sent_ev /\
        step_model sender sent_ev == Some sender_model1 /\
        event_raw_delta_legal sender sent_ev sender_delta_sent sender_delta_received /\
        sent_event_nonempty_seal_projection sender sent_ev sender_delta_sent /\
        Seq.equal sender_raw_sent (B.append sender_delta_sent sender_tail_sent) /\
        Seq.equal sender_raw_received (B.append sender_delta_received sender_tail_received) /\
        conn_events_sent_seal_replay
          sender_model1
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final
      with
      ( lemma_conn_events_received_decode_replay_head
          receiver
          received_ev
          receiver_rest
          receiver_raw_sent
          receiver_raw_received
          receiver_final;
        eliminate exists
          (receiver_model1:connection_model)
          (receiver_delta_sent:B.bytes)
          (receiver_delta_received:B.bytes)
          (receiver_tail_sent:B.bytes)
          (receiver_tail_received:B.bytes).
          legal_event receiver received_ev /\
          step_model receiver received_ev == Some receiver_model1 /\
          event_raw_delta_legal receiver received_ev receiver_delta_sent receiver_delta_received /\
          received_event_nonempty_decode_projection receiver received_ev receiver_delta_received /\
          Seq.equal receiver_raw_sent (B.append receiver_delta_sent receiver_tail_sent) /\
          Seq.equal receiver_raw_received (B.append receiver_delta_received receiver_tail_received) /\
          conn_events_received_decode_replay
            receiver_model1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
        with
        ( assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
          assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
          assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
          assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
          lemma_sent_event_nonempty_seal_projection_protected
            sender
            (M.TlsHandshake sent_msg)
            sender_delta_sent
            sender_delta_received;
          lemma_received_event_nonempty_decode_projection_protected
            receiver
            (M.TlsHandshake received_msg)
            receiver_delta_sent
            receiver_delta_received;
          lemma_protected_handshake_event_projection_pair_from_equal_stream_heads
            sender
            receiver
            sent_msg
            received_msg
            sender_raw_sent
            receiver_raw_received
            sender_delta_sent
            sender_tail_sent
            receiver_delta_received
            receiver_tail_received;
          introduce exists (pair:protected_message_replay).
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg
          with ({
            pm_sender = sender;
            pm_receiver = receiver;
            pm_raw_sent = sender_delta_sent;
            pm_raw_received = receiver_delta_received;
          })
          and () ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
#restart-solver
let lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
  (sender:connection_model)
  (receiver:connection_model)
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
          step_model
            sender
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake sent_msg;
            }) == Some sender_after /\
          step_model
            receiver
            (ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  match sent_msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ ->
    match received_msg with
    | M.EncryptedExtensions _
    | M.Certificate _
    | M.CertificateVerify _
    | M.Finished _ ->
      lemma_conn_events_sent_seal_replay_head
        sender
        sent_ev
        sender_rest
        sender_raw_sent
        sender_raw_received
        sender_final;
      eliminate exists
        (sender_model1:connection_model)
        (sender_delta_sent:B.bytes)
        (sender_delta_received:B.bytes)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes).
        legal_event sender sent_ev /\
        step_model sender sent_ev == Some sender_model1 /\
        event_raw_delta_legal sender sent_ev sender_delta_sent sender_delta_received /\
        sent_event_nonempty_seal_projection sender sent_ev sender_delta_sent /\
        Seq.equal sender_raw_sent (B.append sender_delta_sent sender_tail_sent) /\
        Seq.equal sender_raw_received (B.append sender_delta_received sender_tail_received) /\
        conn_events_sent_seal_replay
          sender_model1
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final
      with
      ( lemma_conn_events_received_decode_replay_head
          receiver
          received_ev
          receiver_rest
          receiver_raw_sent
          receiver_raw_received
          receiver_final;
        eliminate exists
          (receiver_model1:connection_model)
          (receiver_delta_sent:B.bytes)
          (receiver_delta_received:B.bytes)
          (receiver_tail_sent:B.bytes)
          (receiver_tail_received:B.bytes).
          legal_event receiver received_ev /\
          step_model receiver received_ev == Some receiver_model1 /\
          event_raw_delta_legal receiver received_ev receiver_delta_sent receiver_delta_received /\
          received_event_nonempty_decode_projection receiver received_ev receiver_delta_received /\
          Seq.equal receiver_raw_sent (B.append receiver_delta_sent receiver_tail_sent) /\
          Seq.equal receiver_raw_received (B.append receiver_delta_received receiver_tail_received) /\
          conn_events_received_decode_replay
            receiver_model1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final
        with
        ( assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
          assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
          assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
          assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
          lemma_sent_event_nonempty_seal_projection_protected
            sender
            (M.TlsHandshake sent_msg)
            sender_delta_sent
            sender_delta_received;
          lemma_received_event_nonempty_decode_projection_protected
            receiver
            (M.TlsHandshake received_msg)
            receiver_delta_sent
            receiver_delta_received;
          lemma_protected_handshake_event_projection_pair_from_equal_stream_heads
            sender
            receiver
            sent_msg
            received_msg
            sender_raw_sent
            receiver_raw_received
            sender_delta_sent
            sender_tail_sent
            receiver_delta_received
            receiver_tail_received;
          lemma_protected_handshake_event_tails_equal_from_equal_stream_heads
            sender
            receiver
            sent_msg
            received_msg
            sender_raw_sent
            receiver_raw_received
            sender_delta_sent
            sender_tail_sent
            receiver_delta_received
            receiver_tail_received;
          introduce exists
            (sender_after:connection_model)
            (receiver_after:connection_model)
            (pair:protected_message_replay)
            (sender_tail_sent':B.bytes)
            (sender_tail_received':B.bytes)
            (receiver_tail_sent':B.bytes)
            (receiver_tail_received':B.bytes).
            step_model sender sent_ev == Some sender_after /\
            step_model receiver received_ev == Some receiver_after /\
            pair.pm_sender == sender /\
            pair.pm_receiver == receiver /\
            protected_handshake_event_projection_pair
              pair
              sent_msg
              received_msg /\
            Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent') /\
            Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received') /\
            Seq.equal sender_tail_sent' receiver_tail_received' /\
            conn_events_sent_seal_replay
              sender_after
              sender_rest
              sender_tail_sent'
              sender_tail_received'
              sender_final /\
            conn_events_received_decode_replay
              receiver_after
              receiver_rest
              receiver_tail_sent'
              receiver_tail_received'
              receiver_final
          with
            sender_model1
            receiver_model1
            ({
              pm_sender = sender;
              pm_receiver = receiver;
              pm_raw_sent = sender_delta_sent;
              pm_raw_received = receiver_delta_received;
            })
            sender_tail_sent
            sender_tail_received
            receiver_tail_sent
            receiver_tail_received
          and () ) )
    | _ ->
      assert False
  | _ ->
    assert False
#pop-options

#push-options "--z3rlimit 10"
let lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after:connection_model)
  (receiver_after:connection_model)
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
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after /\
        sender_after.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
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
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_conn_events_sent_seal_replay_head
    sender
    sent_ev
    sender_rest
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender_after0:connection_model)
    (sender_delta_sent:B.bytes)
    (sender_delta_received:B.bytes)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sent_ev /\
    step_model sender sent_ev == Some sender_after0 /\
    event_raw_delta_legal sender sent_ev sender_delta_sent sender_delta_received /\
    sent_event_nonempty_seal_projection sender sent_ev sender_delta_sent /\
    Seq.equal sender_raw_sent (B.append sender_delta_sent sender_tail_sent) /\
    Seq.equal sender_raw_received (B.append sender_delta_received sender_tail_received) /\
    conn_events_sent_seal_replay
      sender_after0
      sender_rest
      sender_tail_sent
      sender_tail_received
      sender_final
  with
  ( lemma_conn_events_received_decode_replay_head
      receiver
      received_ev
      receiver_rest
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_after0:connection_model)
      (receiver_delta_sent:B.bytes)
      (receiver_delta_received:B.bytes)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver received_ev /\
      step_model receiver received_ev == Some receiver_after0 /\
      event_raw_delta_legal receiver received_ev receiver_delta_sent receiver_delta_received /\
      received_event_nonempty_decode_projection receiver received_ev receiver_delta_received /\
      Seq.equal receiver_raw_sent (B.append receiver_delta_sent receiver_tail_sent) /\
      Seq.equal receiver_raw_received (B.append receiver_delta_received receiver_tail_received) /\
      conn_events_received_decode_replay
        receiver_after0
        receiver_rest
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    with
    ( assert (sender_after0 == sender_after);
      assert (receiver_after0 == receiver_after);
      assert (sender_after.model_record.record_write ==
        R.next_seq sender.model_record.record_write);
      assert (receiver_after.model_record.record_read ==
        R.next_seq receiver.model_record.record_read);
      lemma_next_seq_models_preserve_write_read_record_material_alignment
        sender
        receiver
        sender_after
        receiver_after;
      lemma_protected_handshake_event_projection_pair_from_head_replays
        sender
        receiver
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
        pair.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair
          sent_msg
          received_msg
      with
      ( introduce exists
          (pair':protected_message_replay).
          pair'.pm_sender == sender /\
          pair'.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair'
            sent_msg
            received_msg /\
          write_read_record_material_aligned sender_after receiver_after
        with pair
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment_and_tails
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after:connection_model)
  (receiver_after:connection_model)
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
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          }) == Some sender_after /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          }) == Some receiver_after /\
        sender_after.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
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
          conn_events_sent_seal_replay
            sender_after
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
  lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
    sender
    receiver
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
    (sender_after0:connection_model)
    (receiver_after0:connection_model)
    (pair:protected_message_replay)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    step_model sender sent_ev == Some sender_after0 /\
    step_model receiver received_ev == Some receiver_after0 /\
    pair.pm_sender == sender /\
    pair.pm_receiver == receiver /\
    protected_handshake_event_projection_pair
      pair
      sent_msg
      received_msg /\
    Seq.equal sender_raw_sent (B.append pair.pm_raw_sent sender_tail_sent) /\
    Seq.equal receiver_raw_received (B.append pair.pm_raw_received receiver_tail_received) /\
    Seq.equal sender_tail_sent receiver_tail_received /\
    conn_events_sent_seal_replay
      sender_after0
      sender_rest
      sender_tail_sent
      sender_tail_received
      sender_final /\
    conn_events_received_decode_replay
      receiver_after0
      receiver_rest
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  with
  ( assert (sender_after0 == sender_after);
    assert (receiver_after0 == receiver_after);
    lemma_next_seq_models_preserve_write_read_record_material_alignment
      sender
      receiver
      sender_after
      receiver_after;
    introduce exists
      (pair':protected_message_replay)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      pair'.pm_sender == sender /\
      pair'.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair'
        sent_msg
        received_msg /\
      write_read_record_material_aligned sender_after receiver_after /\
      Seq.equal sender_raw_sent (B.append pair'.pm_raw_sent sender_tail_sent') /\
      Seq.equal receiver_raw_received (B.append pair'.pm_raw_received receiver_tail_received') /\
      Seq.equal sender_tail_sent' receiver_tail_received' /\
      conn_events_sent_seal_replay
        sender_after
        sender_rest
        sender_tail_sent'
        sender_tail_received'
        sender_final /\
      conn_events_received_decode_replay
        receiver_after
        receiver_rest
        receiver_tail_sent'
        receiver_tail_received'
        receiver_final
    with pair sender_tail_sent sender_tail_received receiver_tail_sent receiver_tail_received
    and () )

let lemma_protected_handshake_event_projection_pairs_from_two_head_replays_with_next_alignment_and_tails
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after0:connection_model)
  (receiver_after0:connection_model)
  (sender_after1:connection_model)
  (receiver_after1:connection_model)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
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
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some sender_after0 /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some receiver_after0 /\
        sender_after0.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after0.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
        step_model
          sender_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some sender_after1 /\
        step_model
          receiver_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some receiver_after1 /\
        sender_after1.model_record.record_write ==
          R.next_seq sender_after0.model_record.record_write /\
        receiver_after1.model_record.record_read ==
          R.next_seq receiver_after0.model_record.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          } :: ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after1
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after1
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sent_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg1;
  } in
  let received_ev1 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg1;
  } in
  lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment_and_tails
    sender
    receiver
    sender_after0
    receiver_after0
    sent_msg0
    received_msg0
    (sent_ev1 :: sender_rest)
    (received_ev1 :: receiver_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_sent
    receiver_raw_received
    sender_final
    receiver_final;
  eliminate exists
    (pair0:protected_message_replay)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    pair0.pm_sender == sender /\
    pair0.pm_receiver == receiver /\
    protected_handshake_event_projection_pair
      pair0
      sent_msg0
      received_msg0 /\
    write_read_record_material_aligned sender_after0 receiver_after0 /\
    Seq.equal sender_raw_sent (B.append pair0.pm_raw_sent sender_tail_sent0) /\
    Seq.equal receiver_raw_received (B.append pair0.pm_raw_received receiver_tail_received0) /\
    Seq.equal sender_tail_sent0 receiver_tail_received0 /\
    conn_events_sent_seal_replay
      sender_after0
      (sent_ev1 :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final /\
    conn_events_received_decode_replay
      receiver_after0
      (received_ev1 :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  with
  ( lemma_protected_handshake_event_projection_pair_from_head_replays_with_next_alignment_and_tails
      sender_after0
      receiver_after0
      sender_after1
      receiver_after1
      sent_msg1
      received_msg1
      sender_rest
      receiver_rest
      sender_tail_sent0
      sender_tail_received0
      receiver_tail_sent0
      receiver_tail_received0
      sender_final
      receiver_final;
    eliminate exists
      (pair1:protected_message_replay)
      (sender_tail_sent1:B.bytes)
      (sender_tail_received1:B.bytes)
      (receiver_tail_sent1:B.bytes)
      (receiver_tail_received1:B.bytes).
      pair1.pm_sender == sender_after0 /\
      pair1.pm_receiver == receiver_after0 /\
      protected_handshake_event_projection_pair
        pair1
        sent_msg1
        received_msg1 /\
      write_read_record_material_aligned sender_after1 receiver_after1 /\
      Seq.equal sender_tail_sent0 (B.append pair1.pm_raw_sent sender_tail_sent1) /\
      Seq.equal receiver_tail_received0 (B.append pair1.pm_raw_received receiver_tail_received1) /\
      Seq.equal sender_tail_sent1 receiver_tail_received1 /\
      conn_events_sent_seal_replay
        sender_after1
        sender_rest
        sender_tail_sent1
        sender_tail_received1
        sender_final /\
      conn_events_received_decode_replay
        receiver_after1
        receiver_rest
        receiver_tail_sent1
        receiver_tail_received1
        receiver_final
    with
    ( introduce exists
        (pair0':protected_message_replay)
        (pair1':protected_message_replay)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes)
        (receiver_tail_sent:B.bytes)
        (receiver_tail_received:B.bytes).
        pair0'.pm_sender == sender /\
        pair0'.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair0'
          sent_msg0
          received_msg0 /\
        pair1'.pm_sender == sender_after0 /\
        pair1'.pm_receiver == receiver_after0 /\
        protected_handshake_event_projection_pair
          pair1'
          sent_msg1
          received_msg1 /\
        write_read_record_material_aligned sender_after0 receiver_after0 /\
        write_read_record_material_aligned sender_after1 receiver_after1 /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
          sender_after1
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_after1
          receiver_rest
          receiver_tail_sent
          receiver_tail_received
          receiver_final
      with
        pair0
        pair1
        sender_tail_sent1
        sender_tail_received1
        receiver_tail_sent1
        receiver_tail_received1
      and () ) )

#restart-solver
let lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (skip_ev:conn_event)
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
        step_model sender skip_ev == Some sender_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake _ -> True
         | ConnCleartextHandshake _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        sender_after.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender_after.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (skip_ev :: ConnNetworkEvent {
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
        exists pair.
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver /\
          protected_handshake_event_projection_pair
            pair
            sent_msg
            received_msg)
=
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
    (sender1:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  with
  ( assert (sender1 == sender_after);
    assert (
      conn_events_sent_seal_replay
        sender_after
        (sent_ev :: sender_rest)
        sender_tail_sent
        sender_tail_received
        sender_final);
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
      receiver_final )

let lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (skip_ev:conn_event)
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
        step_model sender skip_ev == Some sender_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake _ -> True
         | ConnCleartextHandshake _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        write_read_record_material_aligned sender_after receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (skip_ev :: ConnNetworkEvent {
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
        exists sender_after_head receiver_after_head pair
          sender_tail_sent sender_tail_received
          receiver_tail_sent receiver_tail_received.
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
    (sender1:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender skip_ev /\
    step_model sender skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  with
  ( assert (sender1 == sender_after);
    lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
      sender_after
      receiver
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_tail_sent0
      sender_tail_received0
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
      Seq.equal sender_tail_sent0 (B.append pair0.pm_raw_sent sender_tail_sent) /\
      Seq.equal receiver_raw_received (B.append pair0.pm_raw_received receiver_tail_received) /\
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
    with
    ( introduce exists
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender_after sent_ev == Some sender_after_head /\
        step_model receiver received_ev == Some receiver_after_head /\
        pair.pm_sender == sender_after /\
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
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

let lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head_with_next_alignment_and_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (sender_after_head:connection_model)
  (receiver_after_head:connection_model)
  (skip_ev:conn_event)
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
        step_model sender skip_ev == Some sender_after /\
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
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake _ -> True
         | ConnCleartextHandshake _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        write_read_record_material_aligned sender_after receiver /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (skip_ev :: ConnNetworkEvent {
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
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
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
  with
  ( assert (sender_after_head0 == sender_after_head);
    assert (receiver_after_head0 == receiver_after_head);
    lemma_next_seq_models_preserve_write_read_record_material_alignment
      sender_after
      receiver
      sender_after_head
      receiver_after_head;
    introduce exists
      (pair:protected_message_replay)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      write_read_record_material_aligned sender_after_head receiver_after_head /\
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
      pair0
      sender_tail_sent
      sender_tail_received
      receiver_tail_sent
      receiver_tail_received
    and () )

let lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head
  (sender:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (skip_ev:conn_event)
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
        step_model receiver skip_ev == Some receiver_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake step -> not step.protected_handshake_head
         | ConnCleartextHandshake _ -> False
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        sender.model_record.record_write.R.seq ==
          receiver_after.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver_after.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
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
          (skip_ev :: ConnNetworkEvent {
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
=
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
    (receiver1:connection_model)
    (receiver_tail_sent:B.bytes)
    (receiver_tail_received:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver1 /\
    Seq.equal sender_raw_sent receiver_tail_received /\
    conn_events_received_decode_replay
      receiver1
      (received_ev :: receiver_rest)
      receiver_tail_sent
      receiver_tail_received
      receiver_final
  with
  ( assert (receiver1 == receiver_after);
    assert (
      conn_events_received_decode_replay
        receiver_after
        (received_ev :: receiver_rest)
        receiver_tail_sent
        receiver_tail_received
        receiver_final);
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
      receiver_final )

let lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_tails
  (sender:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (skip_ev:conn_event)
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
        step_model receiver skip_ev == Some receiver_after /\
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake step -> not step.protected_handshake_head
         | ConnCleartextHandshake _ -> False
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender receiver_after /\
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
          (skip_ev :: ConnNetworkEvent {
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
    (receiver1:connection_model)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
    legal_event receiver skip_ev /\
    step_model receiver skip_ev == Some receiver1 /\
    Seq.equal sender_raw_sent receiver_tail_received0 /\
    conn_events_received_decode_replay
      receiver1
      (received_ev :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  with
  ( assert (receiver1 == receiver_after);
    lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
      sender
      receiver_after
      sent_msg
      received_msg
      sender_rest
      receiver_rest
      sender_raw_sent
      sender_raw_received
      receiver_tail_sent0
      receiver_tail_received0
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
      Seq.equal sender_raw_sent (B.append pair0.pm_raw_sent sender_tail_sent) /\
      Seq.equal receiver_tail_received0 (B.append pair0.pm_raw_received receiver_tail_received) /\
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
    with
    ( introduce exists
        (sender_after_head:connection_model)
        (receiver_after_head:connection_model)
        (pair:protected_message_replay)
        (sender_tail_sent':B.bytes)
        (sender_tail_received':B.bytes)
        (receiver_tail_sent':B.bytes)
        (receiver_tail_received':B.bytes).
        step_model sender sent_ev == Some sender_after_head /\
        step_model receiver_after received_ev == Some receiver_after_head /\
        pair.pm_sender == sender /\
        pair.pm_receiver == receiver_after /\
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
        sender_after_head0
        receiver_after_head0
        pair0
        sender_tail_sent
        sender_tail_received
        receiver_tail_sent
        receiver_tail_received
      and () ) )

#restart-solver
let lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head_with_next_alignment_and_tails
  (sender:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_after_head:connection_model)
  (receiver_after_head:connection_model)
  (skip_ev:conn_event)
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
        step_model receiver skip_ev == Some receiver_after /\
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
        (match skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake step -> not step.protected_handshake_head
         | ConnCleartextHandshake _ -> False
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender receiver_after /\
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
          (skip_ev :: ConnNetworkEvent {
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
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
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
  with
  ( assert (sender_after_head0 == sender_after_head);
    assert (receiver_after_head0 == receiver_after_head);
    lemma_next_seq_models_preserve_write_read_record_material_alignment
      sender
      receiver_after
      sender_after_head
      receiver_after_head;
    introduce exists
      (pair:protected_message_replay)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      pair.pm_sender == sender /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      write_read_record_material_aligned sender_after_head receiver_after_head /\
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
      pair0
      sender_tail_sent
      sender_tail_received
      receiver_tail_sent
      receiver_tail_received
    and () )

let lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_skip_ev:conn_event)
  (receiver_skip_ev:conn_event)
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
        step_model sender sender_skip_ev == Some sender_after /\
        step_model receiver receiver_skip_ev == Some receiver_after /\
        (match sender_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake _ -> True
         | ConnCleartextHandshake _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake step -> not step.protected_handshake_head
         | ConnCleartextHandshake _ -> False
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        sender_after.model_record.record_write.R.seq ==
          receiver_after.model_record.record_read.R.seq /\
        (match
          record_direction_material sender_after.model_record.record_write,
          record_direction_material receiver_after.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: ConnNetworkEvent {
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
=
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
    (sender1:connection_model)
    (sender_tail_sent:B.bytes)
    (sender_tail_received:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent
      sender_tail_received
      sender_final
  with
  ( assert (sender1 == sender_after);
    lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver1:connection_model)
      (receiver_tail_sent:B.bytes)
      (receiver_tail_received:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver1 /\
      Seq.equal sender_tail_sent receiver_tail_received /\
      conn_events_received_decode_replay
        receiver1
        (received_ev :: receiver_rest)
        receiver_tail_sent
        receiver_tail_received
        receiver_final
    with
    ( assert (receiver1 == receiver_after);
      assert (
        conn_events_sent_seal_replay
          sender_after
          (sent_ev :: sender_rest)
          sender_tail_sent
          sender_tail_received
          sender_final);
      assert (
        conn_events_received_decode_replay
          receiver_after
          (received_ev :: receiver_rest)
          receiver_tail_sent
          receiver_tail_received
          receiver_final);
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
        receiver_final ) )

let lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_skip_ev:conn_event)
  (receiver_skip_ev:conn_event)
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
        step_model sender sender_skip_ev == Some sender_after /\
        step_model receiver receiver_skip_ev == Some receiver_after /\
        (match sender_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake _ -> True
         | ConnCleartextHandshake _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake step -> not step.protected_handshake_head
         | ConnCleartextHandshake _ -> False
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender_after receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: ConnNetworkEvent {
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
    (sender1:connection_model)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes).
    legal_event sender sender_skip_ev /\
    step_model sender sender_skip_ev == Some sender1 /\
    Seq.equal sender_tail_sent0 receiver_raw_received /\
    conn_events_sent_seal_replay
      sender1
      (sent_ev :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final
  with
  ( assert (sender1 == sender_after);
    lemma_received_replay_skip_empty_head_preserves_peer_stream
      sender_tail_sent0
      receiver
      receiver_skip_ev
      (received_ev :: receiver_rest)
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver1:connection_model)
      (receiver_tail_sent0:B.bytes)
      (receiver_tail_received0:B.bytes).
      legal_event receiver receiver_skip_ev /\
      step_model receiver receiver_skip_ev == Some receiver1 /\
      Seq.equal sender_tail_sent0 receiver_tail_received0 /\
      conn_events_received_decode_replay
        receiver1
        (received_ev :: receiver_rest)
        receiver_tail_sent0
        receiver_tail_received0
        receiver_final
    with
    ( assert (receiver1 == receiver_after);
      lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
        sender_after
        receiver_after
        sent_msg
        received_msg
        sender_rest
        receiver_rest
        sender_tail_sent0
        sender_tail_received0
        receiver_tail_sent0
        receiver_tail_received0
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
        Seq.equal sender_tail_sent0 (B.append pair0.pm_raw_sent sender_tail_sent) /\
        Seq.equal receiver_tail_received0 (B.append pair0.pm_raw_received receiver_tail_received) /\
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
      with
      ( introduce exists
          (sender_after_head:connection_model)
          (receiver_after_head:connection_model)
          (pair:protected_message_replay)
          (sender_tail_sent':B.bytes)
          (sender_tail_received':B.bytes)
          (receiver_tail_sent':B.bytes)
          (receiver_tail_received':B.bytes).
          step_model sender_after sent_ev == Some sender_after_head /\
          step_model receiver_after received_ev == Some receiver_after_head /\
          pair.pm_sender == sender_after /\
          pair.pm_receiver == receiver_after /\
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
          sender_after_head0
          receiver_after_head0
          pair0
          sender_tail_sent
          sender_tail_received
          receiver_tail_sent
          receiver_tail_received
        and () ) ) )

let lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_next_alignment_and_tails
  (sender:connection_model)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_after:connection_model)
  (sender_after_head:connection_model)
  (receiver_after_head:connection_model)
  (sender_skip_ev:conn_event)
  (receiver_skip_ev:conn_event)
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
        step_model sender sender_skip_ev == Some sender_after /\
        step_model receiver receiver_skip_ev == Some receiver_after /\
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
        sender_after_head.model_record.record_write ==
          R.next_seq sender_after.model_record.record_write /\
        receiver_after_head.model_record.record_read ==
          R.next_seq receiver_after.model_record.record_read /\
        (match sender_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake _ -> True
         | ConnCleartextHandshake _ -> True
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received) /\
        (match receiver_skip_ev with
         | ConnLocalEvent _ -> True
         | ConnProtectedHandshake step -> not step.protected_handshake_head
         | ConnCleartextHandshake _ -> False
         | ConnNetworkEvent msg -> msg.CL.message_direction == CL.Sent) /\
        write_read_record_material_aligned sender_after receiver_after /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        conn_events_sent_seal_replay
          sender
          (sender_skip_ev :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (receiver_skip_ev :: ConnNetworkEvent {
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
  let sent_ev = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg;
  } in
  let received_ev = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg;
  } in
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
  with
  ( assert (sender_after_head0 == sender_after_head);
    assert (receiver_after_head0 == receiver_after_head);
    lemma_next_seq_models_preserve_write_read_record_material_alignment
      sender_after
      receiver_after
      sender_after_head
      receiver_after_head;
    introduce exists
      (pair:protected_message_replay)
      (sender_tail_sent':B.bytes)
      (sender_tail_received':B.bytes)
      (receiver_tail_sent':B.bytes)
      (receiver_tail_received':B.bytes).
      pair.pm_sender == sender_after /\
      pair.pm_receiver == receiver_after /\
      protected_handshake_event_projection_pair
        pair
        sent_msg
        received_msg /\
      write_read_record_material_aligned sender_after_head receiver_after_head /\
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
      pair0
      sender_tail_sent
      sender_tail_received
      receiver_tail_sent
      receiver_tail_received
    and () )

#restart-solver
let lemma_protected_handshake_event_projection_pairs_from_two_heads_then_both_non_install_local_heads_with_next_alignment_and_tails
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after0:connection_model)
  (receiver_after0:connection_model)
  (sender_after1:connection_model)
  (receiver_after1:connection_model)
  (sender_after_skip:connection_model)
  (receiver_after_skip:connection_model)
  (sender_after2:connection_model)
  (receiver_after2:connection_model)
  (sender_skip:local_event)
  (receiver_skip:local_event)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
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
        local_event_does_not_install_record_keys sender_skip /\
        local_event_does_not_install_record_keys receiver_skip /\
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          }) == Some sender_after0 /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          }) == Some receiver_after0 /\
        sender_after0.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after0.model_record.record_read ==
          R.next_seq receiver.model_record.record_read /\
        step_model
          sender_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          }) == Some sender_after1 /\
        step_model
          receiver_after0
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          }) == Some receiver_after1 /\
        sender_after1.model_record.record_write ==
          R.next_seq sender_after0.model_record.record_write /\
        receiver_after1.model_record.record_read ==
          R.next_seq receiver_after0.model_record.record_read /\
        step_model
          sender_after1
          (ConnLocalEvent sender_skip) == Some sender_after_skip /\
        step_model
          receiver_after1
          (ConnLocalEvent receiver_skip) == Some receiver_after_skip /\
        step_model
          sender_after_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          }) == Some sender_after2 /\
        step_model
          receiver_after_skip
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg2;
          }) == Some receiver_after2 /\
        sender_after2.model_record.record_write ==
          R.next_seq sender_after_skip.model_record.record_write /\
        receiver_after2.model_record.record_read ==
          R.next_seq receiver_after_skip.model_record.record_read /\
        Seq.equal sender_raw_sent receiver_raw_received /\
        protected_handshake_wire_round_trip_message sent_msg0 /\
        protected_handshake_wire_round_trip_message received_msg0 /\
        protected_handshake_wire_round_trip_message sent_msg1 /\
        protected_handshake_wire_round_trip_message received_msg1 /\
        protected_handshake_wire_round_trip_message sent_msg2 /\
        protected_handshake_wire_round_trip_message received_msg2 /\
        conn_events_sent_seal_replay
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg0;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg1;
          } :: ConnLocalEvent sender_skip :: ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg2;
          } :: sender_rest)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg0;
          } :: ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg1;
          } :: ConnLocalEvent receiver_skip :: ConnNetworkEvent {
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
          conn_events_sent_seal_replay
            sender_after2
            sender_rest
            sender_tail_sent
            sender_tail_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_after2
            receiver_rest
            receiver_tail_sent
            receiver_tail_received
            receiver_final)
=
  let sender_skip_ev = ConnLocalEvent sender_skip in
  let receiver_skip_ev = ConnLocalEvent receiver_skip in
  let sent_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake sent_msg2;
  } in
  let received_ev2 = ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake received_msg2;
  } in
  lemma_protected_handshake_event_projection_pairs_from_two_head_replays_with_next_alignment_and_tails
    sender
    receiver
    sender_after0
    receiver_after0
    sender_after1
    receiver_after1
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    (sender_skip_ev :: sent_ev2 :: sender_rest)
    (receiver_skip_ev :: received_ev2 :: receiver_rest)
    sender_raw_sent
    sender_raw_received
    receiver_raw_sent
    receiver_raw_received
    sender_final
    receiver_final;
  eliminate exists
    (pair0:protected_message_replay)
    (pair1:protected_message_replay)
    (sender_tail_sent0:B.bytes)
    (sender_tail_received0:B.bytes)
    (receiver_tail_sent0:B.bytes)
    (receiver_tail_received0:B.bytes).
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
    Seq.equal sender_tail_sent0 receiver_tail_received0 /\
    conn_events_sent_seal_replay
      sender_after1
      (sender_skip_ev :: sent_ev2 :: sender_rest)
      sender_tail_sent0
      sender_tail_received0
      sender_final /\
    conn_events_received_decode_replay
      receiver_after1
      (receiver_skip_ev :: received_ev2 :: receiver_rest)
      receiver_tail_sent0
      receiver_tail_received0
      receiver_final
  with
  ( lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
      sender_after1
      sender_skip
      sender_after_skip
      receiver_after1;
    lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
      sender_after_skip
      receiver_after1
      receiver_skip
      receiver_after_skip;
    lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads_with_next_alignment_and_tails
      sender_after1
      sender_after_skip
      receiver_after1
      receiver_after_skip
      sender_after2
      receiver_after2
      sender_skip_ev
      receiver_skip_ev
      sent_msg2
      received_msg2
      sender_rest
      receiver_rest
      sender_tail_sent0
      sender_tail_received0
      receiver_tail_sent0
      receiver_tail_received0
      sender_final
      receiver_final;
    eliminate exists
      (pair2:protected_message_replay)
      (sender_tail_sent2:B.bytes)
      (sender_tail_received2:B.bytes)
      (receiver_tail_sent2:B.bytes)
      (receiver_tail_received2:B.bytes).
      pair2.pm_sender == sender_after_skip /\
      pair2.pm_receiver == receiver_after_skip /\
      protected_handshake_event_projection_pair
        pair2
        sent_msg2
        received_msg2 /\
      write_read_record_material_aligned sender_after2 receiver_after2 /\
      Seq.equal sender_tail_sent2 receiver_tail_received2 /\
      conn_events_sent_seal_replay
        sender_after2
        sender_rest
        sender_tail_sent2
        sender_tail_received2
        sender_final /\
      conn_events_received_decode_replay
        receiver_after2
        receiver_rest
        receiver_tail_sent2
        receiver_tail_received2
        receiver_final
    with
    ( introduce exists
        (pair0':protected_message_replay)
        (pair1':protected_message_replay)
        (pair2':protected_message_replay)
        (sender_tail_sent:B.bytes)
        (sender_tail_received:B.bytes)
        (receiver_tail_sent:B.bytes)
        (receiver_tail_received:B.bytes).
        pair0'.pm_sender == sender /\
        pair0'.pm_receiver == receiver /\
        protected_handshake_event_projection_pair
          pair0'
          sent_msg0
          received_msg0 /\
        pair1'.pm_sender == sender_after0 /\
        pair1'.pm_receiver == receiver_after0 /\
        protected_handshake_event_projection_pair
          pair1'
          sent_msg1
          received_msg1 /\
        pair2'.pm_sender == sender_after_skip /\
        pair2'.pm_receiver == receiver_after_skip /\
        protected_handshake_event_projection_pair
          pair2'
          sent_msg2
          received_msg2 /\
        write_read_record_material_aligned sender_after1 receiver_after1 /\
        write_read_record_material_aligned sender_after2 receiver_after2 /\
        Seq.equal sender_tail_sent receiver_tail_received /\
        conn_events_sent_seal_replay
          sender_after2
          sender_rest
          sender_tail_sent
          sender_tail_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_after2
          receiver_rest
          receiver_tail_sent
          receiver_tail_received
          receiver_final
      with
        pair0
        pair1
        pair2
        sender_tail_sent2
        sender_tail_received2
        receiver_tail_sent2
        receiver_tail_received2
      and () ) )

#pop-options
