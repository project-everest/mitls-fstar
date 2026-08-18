module TLS13.ConnectionState.ProtectedWireReplay

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

let lemma_conn_events_raw_replay_head
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)
=
  lemma_raw_replay_cons_unfold model ev rest raw_sent raw_received final_model;
  eliminate exists
    (model1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_raw_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  with
  ( introduce exists
      (model1':connection_model)
      (delta_sent':B.bytes)
      (delta_received':B.bytes)
      (tail_sent':B.bytes)
      (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model
    with model1 delta_sent delta_received tail_sent tail_received
    and () )

let lemma_conn_events_sent_seal_replay_head
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          sent_event_nonempty_seal_projection model ev delta_sent /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_sent_seal_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)
=
  lemma_sent_seal_replay_cons_unfold model ev rest raw_sent raw_received final_model;
  eliminate exists
    (model1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  with
  ( introduce exists
      (model1':connection_model)
      (delta_sent':B.bytes)
      (delta_received':B.bytes)
      (tail_sent':B.bytes)
      (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      sent_event_nonempty_seal_projection model ev delta_sent' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_sent_seal_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model
    with model1 delta_sent delta_received tail_sent tail_received
    and () )

let lemma_conn_events_sent_seal_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_sent_seal_replay
          model1
          rest
          tail_sent
          tail_received
          final_model)
      (ensures
        conn_events_sent_seal_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model)

let lemma_conn_events_received_decode_replay_head
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model)
=
  lemma_received_decode_replay_cons_unfold model ev rest raw_sent raw_received final_model;
  eliminate exists
    (model1:connection_model)
    (delta_sent:B.bytes)
    (delta_received:B.bytes)
    (tail_sent:B.bytes)
    (tail_received:B.bytes).
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      model1
      rest
      tail_sent
      tail_received
      final_model
  with
  ( introduce exists
      (model1':connection_model)
      (delta_sent':B.bytes)
      (delta_received':B.bytes)
      (tail_sent':B.bytes)
      (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      received_event_nonempty_decode_projection model ev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model
    with model1 delta_sent delta_received tail_sent tail_received
    and () )

#push-options "--z3rlimit 60"
let lemma_conn_events_received_decode_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_received_decode_replay
          model1
          rest
          tail_sent
          tail_received
          final_model)
      (ensures
        conn_events_received_decode_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model)

#pop-options
let rec lemma_conn_events_sent_received_replays_same_events_final_model_equal
  (model:connection_model)
  (events:list conn_event)
  (sent_raw_sent:B.bytes)
  (sent_raw_received:B.bytes)
  (sent_final:connection_model)
  (received_raw_sent:B.bytes)
  (received_raw_received:B.bytes)
  (received_final:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          events
          sent_raw_sent
          sent_raw_received
          sent_final /\
        conn_events_received_decode_replay
          model
          events
          received_raw_sent
          received_raw_received
          received_final)
      (ensures sent_final == received_final)
      (decreases events)
=
  match events with
  | [] ->
    assert_norm (
      conn_events_sent_seal_replay
        model
        []
        sent_raw_sent
        sent_raw_received
        sent_final ==
      (Seq.equal sent_raw_sent B.empty /\
       Seq.equal sent_raw_received B.empty /\
       sent_final == model));
    assert_norm (
      conn_events_received_decode_replay
        model
        []
        received_raw_sent
        received_raw_received
        received_final ==
      (Seq.equal received_raw_sent B.empty /\
       Seq.equal received_raw_received B.empty /\
       received_final == model));
    assert (sent_final == model);
    assert (received_final == model)
  | ev :: rest ->
    lemma_conn_events_sent_seal_replay_head
      model
      ev
      rest
      sent_raw_sent
      sent_raw_received
      sent_final;
    eliminate exists
      (sent_model1:connection_model)
      (sent_delta_sent:B.bytes)
      (sent_delta_received:B.bytes)
      (sent_tail_sent:B.bytes)
      (sent_tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some sent_model1 /\
      event_raw_delta_legal model ev sent_delta_sent sent_delta_received /\
      sent_event_nonempty_seal_projection model ev sent_delta_sent /\
      Seq.equal sent_raw_sent (B.append sent_delta_sent sent_tail_sent) /\
      Seq.equal sent_raw_received (B.append sent_delta_received sent_tail_received) /\
      conn_events_sent_seal_replay
        sent_model1
        rest
        sent_tail_sent
        sent_tail_received
        sent_final
    with
    ( lemma_conn_events_received_decode_replay_head
        model
        ev
        rest
        received_raw_sent
        received_raw_received
        received_final;
      eliminate exists
        (received_model1:connection_model)
        (received_delta_sent:B.bytes)
        (received_delta_received:B.bytes)
        (received_tail_sent:B.bytes)
        (received_tail_received:B.bytes).
        legal_event model ev /\
        step_model model ev == Some received_model1 /\
        event_raw_delta_legal
          model
          ev
          received_delta_sent
          received_delta_received /\
        received_event_nonempty_decode_projection
          model
          ev
          received_delta_received /\
        Seq.equal
          received_raw_sent
          (B.append received_delta_sent received_tail_sent) /\
        Seq.equal
          received_raw_received
          (B.append received_delta_received received_tail_received) /\
        conn_events_received_decode_replay
          received_model1
          rest
          received_tail_sent
          received_tail_received
          received_final
      with
      ( assert (sent_model1 == received_model1);
        lemma_conn_events_sent_received_replays_same_events_final_model_equal
          sent_model1
          rest
          sent_tail_sent
          sent_tail_received
          sent_final
          received_tail_sent
          received_tail_received
          received_final ) )

let rec lemma_conn_events_raw_sent_seal_replays_same_events_final_model_equal
  (model:connection_model)
  (events:list conn_event)
  (raw_replay_sent:B.bytes)
  (raw_replay_received:B.bytes)
  (raw_final:connection_model)
  (sent_raw_sent:B.bytes)
  (sent_raw_received:B.bytes)
  (sent_final:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay
          model
          events
          raw_replay_sent
          raw_replay_received
          raw_final /\
        conn_events_sent_seal_replay
          model
          events
          sent_raw_sent
          sent_raw_received
          sent_final)
      (ensures raw_final == sent_final)
      (decreases events)
=
  match events with
  | [] ->
    assert_norm (
      conn_events_raw_replay
        model
        []
        raw_replay_sent
        raw_replay_received
        raw_final ==
      (Seq.equal raw_replay_sent B.empty /\
       Seq.equal raw_replay_received B.empty /\
       raw_final == model));
    assert_norm (
      conn_events_sent_seal_replay
        model
        []
        sent_raw_sent
        sent_raw_received
        sent_final ==
      (Seq.equal sent_raw_sent B.empty /\
       Seq.equal sent_raw_received B.empty /\
       sent_final == model));
    assert (raw_final == model);
    assert (sent_final == model)
  | ev :: rest ->
    lemma_conn_events_raw_replay_head
      model
      ev
      rest
      raw_replay_sent
      raw_replay_received
      raw_final;
    eliminate exists
      (raw_model1:connection_model)
      (raw_delta_sent:B.bytes)
      (raw_delta_received:B.bytes)
      (raw_tail_sent:B.bytes)
      (raw_tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some raw_model1 /\
      event_raw_delta_legal model ev raw_delta_sent raw_delta_received /\
      Seq.equal raw_replay_sent (B.append raw_delta_sent raw_tail_sent) /\
      Seq.equal raw_replay_received (B.append raw_delta_received raw_tail_received) /\
      conn_events_raw_replay
        raw_model1
        rest
        raw_tail_sent
        raw_tail_received
        raw_final
    with
    ( lemma_conn_events_sent_seal_replay_head
        model
        ev
        rest
        sent_raw_sent
        sent_raw_received
        sent_final;
      eliminate exists
        (sent_model1:connection_model)
        (sent_delta_sent:B.bytes)
        (sent_delta_received:B.bytes)
        (sent_tail_sent:B.bytes)
        (sent_tail_received:B.bytes).
        legal_event model ev /\
        step_model model ev == Some sent_model1 /\
        event_raw_delta_legal model ev sent_delta_sent sent_delta_received /\
        sent_event_nonempty_seal_projection model ev sent_delta_sent /\
        Seq.equal sent_raw_sent (B.append sent_delta_sent sent_tail_sent) /\
        Seq.equal sent_raw_received (B.append sent_delta_received sent_tail_received) /\
        conn_events_sent_seal_replay
          sent_model1
          rest
          sent_tail_sent
          sent_tail_received
          sent_final
      with
      ( assert (raw_model1 == sent_model1);
        lemma_conn_events_raw_sent_seal_replays_same_events_final_model_equal
          raw_model1
          rest
          raw_tail_sent
          raw_tail_received
          raw_final
          sent_tail_sent
          sent_tail_received
          sent_final ) )

let rec lemma_conn_events_raw_received_decode_replays_same_events_final_model_equal
  (model:connection_model)
  (events:list conn_event)
  (raw_replay_sent:B.bytes)
  (raw_replay_received:B.bytes)
  (raw_final:connection_model)
  (received_raw_sent:B.bytes)
  (received_raw_received:B.bytes)
  (received_final:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay
          model
          events
          raw_replay_sent
          raw_replay_received
          raw_final /\
        conn_events_received_decode_replay
          model
          events
          received_raw_sent
          received_raw_received
          received_final)
      (ensures raw_final == received_final)
      (decreases events)
=
  match events with
  | [] ->
    assert_norm (
      conn_events_raw_replay
        model
        []
        raw_replay_sent
        raw_replay_received
        raw_final ==
      (Seq.equal raw_replay_sent B.empty /\
       Seq.equal raw_replay_received B.empty /\
       raw_final == model));
    assert_norm (
      conn_events_received_decode_replay
        model
        []
        received_raw_sent
        received_raw_received
        received_final ==
      (Seq.equal received_raw_sent B.empty /\
       Seq.equal received_raw_received B.empty /\
       received_final == model));
    assert (raw_final == model);
    assert (received_final == model)
  | ev :: rest ->
    lemma_conn_events_raw_replay_head
      model
      ev
      rest
      raw_replay_sent
      raw_replay_received
      raw_final;
    eliminate exists
      (raw_model1:connection_model)
      (raw_delta_sent:B.bytes)
      (raw_delta_received:B.bytes)
      (raw_tail_sent:B.bytes)
      (raw_tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some raw_model1 /\
      event_raw_delta_legal model ev raw_delta_sent raw_delta_received /\
      Seq.equal raw_replay_sent (B.append raw_delta_sent raw_tail_sent) /\
      Seq.equal raw_replay_received (B.append raw_delta_received raw_tail_received) /\
      conn_events_raw_replay
        raw_model1
        rest
        raw_tail_sent
        raw_tail_received
        raw_final
    with
    ( lemma_conn_events_received_decode_replay_head
        model
        ev
        rest
        received_raw_sent
        received_raw_received
        received_final;
      eliminate exists
        (received_model1:connection_model)
        (received_delta_sent:B.bytes)
        (received_delta_received:B.bytes)
        (received_tail_sent:B.bytes)
        (received_tail_received:B.bytes).
        legal_event model ev /\
        step_model model ev == Some received_model1 /\
        event_raw_delta_legal
          model
          ev
          received_delta_sent
          received_delta_received /\
        received_event_nonempty_decode_projection
          model
          ev
          received_delta_received /\
        Seq.equal
          received_raw_sent
          (B.append received_delta_sent received_tail_sent) /\
        Seq.equal
          received_raw_received
          (B.append received_delta_received received_tail_received) /\
        conn_events_received_decode_replay
          received_model1
          rest
          received_tail_sent
          received_tail_received
          received_final
      with
      ( assert (raw_model1 == received_model1);
        lemma_conn_events_raw_received_decode_replays_same_events_final_model_equal
          raw_model1
          rest
          raw_tail_sent
          raw_tail_received
          raw_final
          received_tail_sent
          received_tail_received
          received_final ) )

let rec lemma_conn_events_sent_seal_replay_implies_raw_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_conn_events_sent_seal_replay_head
      model
      ev
      rest
      raw_sent
      raw_received
      final_model;
    lemma_raw_replay_cons_unfold model ev rest raw_sent raw_received final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
    with
    (
      lemma_conn_events_sent_seal_replay_implies_raw_replay
        model1
        rest
        tail_sent
        tail_received
        final_model;
      introduce exists
        (model1':connection_model)
        (delta_sent':B.bytes)
        (delta_received':B.bytes)
        (tail_sent':B.bytes)
        (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model
      with model1 delta_sent delta_received tail_sent tail_received
      and ()
    )

let rec lemma_conn_events_received_decode_replay_implies_raw_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_conn_events_received_decode_replay_head
      model
      ev
      rest
      raw_sent
      raw_received
      final_model;
    lemma_raw_replay_cons_unfold model ev rest raw_sent raw_received final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
    with
    (
      lemma_conn_events_received_decode_replay_implies_raw_replay
        model1
        rest
        tail_sent
        tail_received
        final_model;
      introduce exists
        (model1':connection_model)
        (delta_sent':B.bytes)
        (delta_received':B.bytes)
        (tail_sent':B.bytes)
        (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model
      with model1 delta_sent delta_received tail_sent tail_received
      and ()
    )

let rec lemma_conn_events_raw_replay_append_split
  (model:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          conn_events_raw_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          conn_events_raw_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)
      (decreases prefix)
=
  match prefix with
  | [] ->
    introduce exists
      (mid:connection_model)
      (prefix_sent:B.bytes)
      (prefix_received:B.bytes)
      (suffix_sent:B.bytes)
      (suffix_received:B.bytes).
      Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
      Seq.equal raw_received (B.append prefix_received suffix_received) /\
      conn_events_raw_replay
        model
        []
        prefix_sent
        prefix_received
        mid /\
      conn_events_raw_replay
        mid
        suffix
        suffix_sent
        suffix_received
        final_model
    with model B.empty B.empty raw_sent raw_received
    and ()
  | ev :: prefix_tail ->
    lemma_conn_events_raw_replay_head
      model
      ev
      (FStar.List.Tot.append prefix_tail suffix)
      raw_sent
      raw_received
      final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_raw_replay
        model1
        (FStar.List.Tot.append prefix_tail suffix)
        tail_sent
        tail_received
        final_model
    with
    ( lemma_conn_events_raw_replay_append_split
        model1
        prefix_tail
        suffix
        tail_sent
        tail_received
        final_model;
      eliminate exists
        (mid:connection_model)
        (tail_prefix_sent:B.bytes)
        (tail_prefix_received:B.bytes)
        (suffix_sent:B.bytes)
        (suffix_received:B.bytes).
        Seq.equal tail_sent (B.append tail_prefix_sent suffix_sent) /\
        Seq.equal tail_received (B.append tail_prefix_received suffix_received) /\
        conn_events_raw_replay
          model1
          prefix_tail
          tail_prefix_sent
          tail_prefix_received
          mid /\
        conn_events_raw_replay
          mid
          suffix
          suffix_sent
          suffix_received
          final_model
      with
      ( let prefix_sent = B.append delta_sent tail_prefix_sent in
        let prefix_received = B.append delta_received tail_prefix_received in
        Seq.append_assoc delta_sent tail_prefix_sent suffix_sent;
        Seq.append_assoc delta_received tail_prefix_received suffix_received;
        assert (Seq.equal raw_sent (B.append prefix_sent suffix_sent));
        assert (Seq.equal raw_received (B.append prefix_received suffix_received));
        introduce exists
          (mid':connection_model)
          (prefix_sent':B.bytes)
          (prefix_received':B.bytes)
          (suffix_sent':B.bytes)
          (suffix_received':B.bytes).
          Seq.equal raw_sent (B.append prefix_sent' suffix_sent') /\
          Seq.equal raw_received (B.append prefix_received' suffix_received') /\
          conn_events_raw_replay
            model
            (ev :: prefix_tail)
            prefix_sent'
            prefix_received'
            mid' /\
          conn_events_raw_replay
            mid'
            suffix
            suffix_sent'
            suffix_received'
            final_model
        with mid prefix_sent prefix_received suffix_sent suffix_received
        and
        ( introduce exists
            (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
            legal_event model ev /\
            step_model model ev == Some model1' /\
            event_raw_delta_legal model ev delta_sent' delta_received' /\
            Seq.equal prefix_sent (B.append delta_sent' tail_sent') /\
            Seq.equal prefix_received (B.append delta_received' tail_received') /\
            conn_events_raw_replay
              model1'
              prefix_tail
              tail_sent'
              tail_received'
              mid
          with
            model1
            delta_sent
            delta_received
            tail_prefix_sent
            tail_prefix_received
          and ();
          assert_norm (
            conn_events_raw_replay
              model
              (ev :: prefix_tail)
              prefix_sent
              prefix_received
              mid ==
            (exists (model1':connection_model)
                    (delta_sent':B.bytes)
                    (delta_received':B.bytes)
                    (tail_sent':B.bytes)
                    (tail_received':B.bytes).
              legal_event model ev /\
              step_model model ev == Some model1' /\
              event_raw_delta_legal model ev delta_sent' delta_received' /\
              Seq.equal prefix_sent (B.append delta_sent' tail_sent') /\
              Seq.equal prefix_received (B.append delta_received' tail_received') /\
              conn_events_raw_replay
                model1'
                prefix_tail
                tail_sent'
                tail_received'
                mid));
          assert (
            conn_events_raw_replay
              model
              (ev :: prefix_tail)
              prefix_sent
              prefix_received
              mid);
          assert (
            conn_events_raw_replay
              mid
              suffix
              suffix_sent
              suffix_received
              final_model);
          () ) ) )

let rec lemma_conn_events_sent_seal_replay_append_split
  (model:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          conn_events_sent_seal_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          conn_events_sent_seal_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)
      (decreases prefix)
=
  match prefix with
  | [] ->
    introduce exists
      (mid:connection_model)
      (prefix_sent:B.bytes)
      (prefix_received:B.bytes)
      (suffix_sent:B.bytes)
      (suffix_received:B.bytes).
      Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
      Seq.equal raw_received (B.append prefix_received suffix_received) /\
      conn_events_sent_seal_replay
        model
        []
        prefix_sent
        prefix_received
        mid /\
      conn_events_sent_seal_replay
        mid
        suffix
        suffix_sent
        suffix_received
        final_model
    with model B.empty B.empty raw_sent raw_received
    and ()
  | ev :: prefix_tail ->
    lemma_conn_events_sent_seal_replay_head
      model
      ev
      (FStar.List.Tot.append prefix_tail suffix)
      raw_sent
      raw_received
      final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_replay
        model1
        (FStar.List.Tot.append prefix_tail suffix)
        tail_sent
        tail_received
        final_model
    with
    ( lemma_conn_events_sent_seal_replay_append_split
        model1
        prefix_tail
        suffix
        tail_sent
        tail_received
        final_model;
      eliminate exists
        (mid:connection_model)
        (tail_prefix_sent:B.bytes)
        (tail_prefix_received:B.bytes)
        (suffix_sent:B.bytes)
        (suffix_received:B.bytes).
        Seq.equal tail_sent (B.append tail_prefix_sent suffix_sent) /\
        Seq.equal tail_received (B.append tail_prefix_received suffix_received) /\
        conn_events_sent_seal_replay
          model1
          prefix_tail
          tail_prefix_sent
          tail_prefix_received
          mid /\
        conn_events_sent_seal_replay
          mid
          suffix
          suffix_sent
          suffix_received
          final_model
      with
      ( let prefix_sent = B.append delta_sent tail_prefix_sent in
        let prefix_received = B.append delta_received tail_prefix_received in
        Seq.append_assoc delta_sent tail_prefix_sent suffix_sent;
        Seq.append_assoc delta_received tail_prefix_received suffix_received;
        assert (Seq.equal raw_sent (B.append prefix_sent suffix_sent));
        assert (Seq.equal raw_received (B.append prefix_received suffix_received));
        introduce exists
          (mid':connection_model)
          (prefix_sent':B.bytes)
          (prefix_received':B.bytes)
          (suffix_sent':B.bytes)
          (suffix_received':B.bytes).
          Seq.equal raw_sent (B.append prefix_sent' suffix_sent') /\
          Seq.equal raw_received (B.append prefix_received' suffix_received') /\
          conn_events_sent_seal_replay
            model
            (ev :: prefix_tail)
            prefix_sent'
            prefix_received'
            mid' /\
          conn_events_sent_seal_replay
            mid'
            suffix
            suffix_sent'
            suffix_received'
            final_model
        with mid prefix_sent prefix_received suffix_sent suffix_received
        and
        ( introduce exists
            (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
            legal_event model ev /\
            step_model model ev == Some model1' /\
            event_raw_delta_legal model ev delta_sent' delta_received' /\
            sent_event_nonempty_seal_projection model ev delta_sent' /\
            Seq.equal prefix_sent (B.append delta_sent' tail_sent') /\
            Seq.equal prefix_received (B.append delta_received' tail_received') /\
            conn_events_sent_seal_replay
              model1'
              prefix_tail
              tail_sent'
              tail_received'
              mid
          with
            model1
            delta_sent
            delta_received
            tail_prefix_sent
            tail_prefix_received
          and ();
          assert_norm (
            conn_events_sent_seal_replay
              model
              (ev :: prefix_tail)
              prefix_sent
              prefix_received
              mid ==
            (exists (model1':connection_model)
                    (delta_sent':B.bytes)
                    (delta_received':B.bytes)
                    (tail_sent':B.bytes)
                    (tail_received':B.bytes).
              legal_event model ev /\
              step_model model ev == Some model1' /\
              event_raw_delta_legal model ev delta_sent' delta_received' /\
              sent_event_nonempty_seal_projection model ev delta_sent' /\
              Seq.equal prefix_sent (B.append delta_sent' tail_sent') /\
              Seq.equal prefix_received (B.append delta_received' tail_received') /\
              conn_events_sent_seal_replay
                model1'
                prefix_tail
                tail_sent'
                tail_received'
                mid));
          assert (
            conn_events_sent_seal_replay
              model
              (ev :: prefix_tail)
              prefix_sent
              prefix_received
              mid);
          assert (
            conn_events_sent_seal_replay
              mid
              suffix
              suffix_sent
              suffix_received
              final_model);
          () ) ) )

let rec lemma_conn_events_received_decode_replay_append_split
  (model:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          conn_events_received_decode_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          conn_events_received_decode_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)
      (decreases prefix)
=
  match prefix with
  | [] ->
    introduce exists
      (mid:connection_model)
      (prefix_sent:B.bytes)
      (prefix_received:B.bytes)
      (suffix_sent:B.bytes)
      (suffix_received:B.bytes).
      Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
      Seq.equal raw_received (B.append prefix_received suffix_received) /\
      conn_events_received_decode_replay
        model
        []
        prefix_sent
        prefix_received
        mid /\
      conn_events_received_decode_replay
        mid
        suffix
        suffix_sent
        suffix_received
        final_model
    with model B.empty B.empty raw_sent raw_received
    and ()
  | ev :: prefix_tail ->
    lemma_conn_events_received_decode_replay_head
      model
      ev
      (FStar.List.Tot.append prefix_tail suffix)
      raw_sent
      raw_received
      final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_replay
        model1
        (FStar.List.Tot.append prefix_tail suffix)
        tail_sent
        tail_received
        final_model
    with
    ( lemma_conn_events_received_decode_replay_append_split
        model1
        prefix_tail
        suffix
        tail_sent
        tail_received
        final_model;
      eliminate exists
        (mid:connection_model)
        (tail_prefix_sent:B.bytes)
        (tail_prefix_received:B.bytes)
        (suffix_sent:B.bytes)
        (suffix_received:B.bytes).
        Seq.equal tail_sent (B.append tail_prefix_sent suffix_sent) /\
        Seq.equal tail_received (B.append tail_prefix_received suffix_received) /\
        conn_events_received_decode_replay
          model1
          prefix_tail
          tail_prefix_sent
          tail_prefix_received
          mid /\
        conn_events_received_decode_replay
          mid
          suffix
          suffix_sent
          suffix_received
          final_model
      with
      ( let prefix_sent = B.append delta_sent tail_prefix_sent in
        let prefix_received = B.append delta_received tail_prefix_received in
        Seq.append_assoc delta_sent tail_prefix_sent suffix_sent;
        Seq.append_assoc delta_received tail_prefix_received suffix_received;
        assert (Seq.equal raw_sent (B.append prefix_sent suffix_sent));
        assert (Seq.equal raw_received (B.append prefix_received suffix_received));
        introduce exists
          (mid':connection_model)
          (prefix_sent':B.bytes)
          (prefix_received':B.bytes)
          (suffix_sent':B.bytes)
          (suffix_received':B.bytes).
          Seq.equal raw_sent (B.append prefix_sent' suffix_sent') /\
          Seq.equal raw_received (B.append prefix_received' suffix_received') /\
          conn_events_received_decode_replay
            model
            (ev :: prefix_tail)
            prefix_sent'
            prefix_received'
            mid' /\
          conn_events_received_decode_replay
            mid'
            suffix
            suffix_sent'
            suffix_received'
            final_model
        with mid prefix_sent prefix_received suffix_sent suffix_received
        and
        ( introduce exists
            (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
            legal_event model ev /\
            step_model model ev == Some model1' /\
            event_raw_delta_legal model ev delta_sent' delta_received' /\
            received_event_nonempty_decode_projection model ev delta_received' /\
            Seq.equal prefix_sent (B.append delta_sent' tail_sent') /\
            Seq.equal prefix_received (B.append delta_received' tail_received') /\
            conn_events_received_decode_replay
              model1'
              prefix_tail
              tail_sent'
              tail_received'
              mid
          with
            model1
            delta_sent
            delta_received
            tail_prefix_sent
            tail_prefix_received
          and ();
          assert_norm (
            conn_events_received_decode_replay
              model
              (ev :: prefix_tail)
              prefix_sent
              prefix_received
              mid ==
            (exists (model1':connection_model)
                    (delta_sent':B.bytes)
                    (delta_received':B.bytes)
                    (tail_sent':B.bytes)
                    (tail_received':B.bytes).
              legal_event model ev /\
              step_model model ev == Some model1' /\
              event_raw_delta_legal model ev delta_sent' delta_received' /\
              received_event_nonempty_decode_projection model ev delta_received' /\
              Seq.equal prefix_sent (B.append delta_sent' tail_sent') /\
              Seq.equal prefix_received (B.append delta_received' tail_received') /\
              conn_events_received_decode_replay
                model1'
                prefix_tail
                tail_sent'
                tail_received'
                mid));
          assert (
            conn_events_received_decode_replay
              model
              (ev :: prefix_tail)
              prefix_sent
              prefix_received
              mid);
          assert (
            conn_events_received_decode_replay
              mid
              suffix
              suffix_sent
              suffix_received
              final_model);
          () ) ) )

let lemma_sent_received_replay_append_split_equal_tails
  (sender_model:connection_model)
  (receiver_model:connection_model)
  (sender_prefix:list conn_event)
  (sender_suffix:list conn_event)
  (receiver_prefix:list conn_event)
  (receiver_suffix:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay
          sender_model
          (FStar.List.Tot.append sender_prefix sender_suffix)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_model
          (FStar.List.Tot.append receiver_prefix receiver_suffix)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        Seq.equal sender_raw_sent receiver_raw_received)
      (ensures
        exists sender_mid receiver_mid
          sender_prefix_sent sender_prefix_received
          sender_suffix_sent sender_suffix_received
          receiver_prefix_sent receiver_prefix_received
          receiver_suffix_sent receiver_suffix_received.
          Seq.equal
            sender_raw_sent
            (B.append sender_prefix_sent sender_suffix_sent) /\
          Seq.equal
            sender_raw_received
            (B.append sender_prefix_received sender_suffix_received) /\
          Seq.equal
            receiver_raw_sent
            (B.append receiver_prefix_sent receiver_suffix_sent) /\
          Seq.equal
            receiver_raw_received
            (B.append receiver_prefix_received receiver_suffix_received) /\
          conn_events_sent_seal_replay
            sender_model
            sender_prefix
            sender_prefix_sent
            sender_prefix_received
            sender_mid /\
          conn_events_sent_seal_replay
            sender_mid
            sender_suffix
            sender_suffix_sent
            sender_suffix_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_model
            receiver_prefix
            receiver_prefix_sent
            receiver_prefix_received
            receiver_mid /\
          conn_events_received_decode_replay
            receiver_mid
            receiver_suffix
            receiver_suffix_sent
            receiver_suffix_received
            receiver_final /\
          (Seq.length sender_prefix_sent ==
             Seq.length receiver_prefix_received ==>
           Seq.equal sender_suffix_sent receiver_suffix_received))
=
  lemma_conn_events_sent_seal_replay_append_split
    sender_model
    sender_prefix
    sender_suffix
    sender_raw_sent
    sender_raw_received
    sender_final;
  eliminate exists
    (sender_mid:connection_model)
    (sender_prefix_sent:B.bytes)
    (sender_prefix_received:B.bytes)
    (sender_suffix_sent:B.bytes)
    (sender_suffix_received:B.bytes).
    Seq.equal
      sender_raw_sent
      (B.append sender_prefix_sent sender_suffix_sent) /\
    Seq.equal
      sender_raw_received
      (B.append sender_prefix_received sender_suffix_received) /\
    conn_events_sent_seal_replay
      sender_model
      sender_prefix
      sender_prefix_sent
      sender_prefix_received
      sender_mid /\
    conn_events_sent_seal_replay
      sender_mid
      sender_suffix
      sender_suffix_sent
      sender_suffix_received
      sender_final
  with
  ( lemma_conn_events_received_decode_replay_append_split
      receiver_model
      receiver_prefix
      receiver_suffix
      receiver_raw_sent
      receiver_raw_received
      receiver_final;
    eliminate exists
      (receiver_mid:connection_model)
      (receiver_prefix_sent:B.bytes)
      (receiver_prefix_received:B.bytes)
      (receiver_suffix_sent:B.bytes)
      (receiver_suffix_received:B.bytes).
      Seq.equal
        receiver_raw_sent
        (B.append receiver_prefix_sent receiver_suffix_sent) /\
      Seq.equal
        receiver_raw_received
        (B.append receiver_prefix_received receiver_suffix_received) /\
      conn_events_received_decode_replay
        receiver_model
        receiver_prefix
        receiver_prefix_sent
        receiver_prefix_received
        receiver_mid /\
      conn_events_received_decode_replay
        receiver_mid
        receiver_suffix
        receiver_suffix_sent
        receiver_suffix_received
        receiver_final
    with
    ( introduce exists
        (sender_mid':connection_model)
        (receiver_mid':connection_model)
        (sender_prefix_sent':B.bytes)
        (sender_prefix_received':B.bytes)
        (sender_suffix_sent':B.bytes)
        (sender_suffix_received':B.bytes)
        (receiver_prefix_sent':B.bytes)
        (receiver_prefix_received':B.bytes)
        (receiver_suffix_sent':B.bytes)
        (receiver_suffix_received':B.bytes).
        Seq.equal
          sender_raw_sent
          (B.append sender_prefix_sent' sender_suffix_sent') /\
        Seq.equal
          sender_raw_received
          (B.append sender_prefix_received' sender_suffix_received') /\
        Seq.equal
          receiver_raw_sent
          (B.append receiver_prefix_sent' receiver_suffix_sent') /\
        Seq.equal
          receiver_raw_received
          (B.append receiver_prefix_received' receiver_suffix_received') /\
        conn_events_sent_seal_replay
          sender_model
          sender_prefix
          sender_prefix_sent'
          sender_prefix_received'
          sender_mid' /\
        conn_events_sent_seal_replay
          sender_mid'
          sender_suffix
          sender_suffix_sent'
          sender_suffix_received'
          sender_final /\
        conn_events_received_decode_replay
          receiver_model
          receiver_prefix
          receiver_prefix_sent'
          receiver_prefix_received'
          receiver_mid' /\
        conn_events_received_decode_replay
          receiver_mid'
          receiver_suffix
          receiver_suffix_sent'
          receiver_suffix_received'
          receiver_final /\
        (Seq.length sender_prefix_sent' ==
           Seq.length receiver_prefix_received' ==>
         Seq.equal sender_suffix_sent' receiver_suffix_received')
      with
        sender_mid
        receiver_mid
        sender_prefix_sent
        sender_prefix_received
        sender_suffix_sent
        sender_suffix_received
        receiver_prefix_sent
        receiver_prefix_received
        receiver_suffix_sent
        receiver_suffix_received
      and
      ( assert (
          Seq.equal
            (B.append sender_prefix_sent sender_suffix_sent)
            (B.append receiver_prefix_received receiver_suffix_received));
        introduce
          Seq.length sender_prefix_sent ==
            Seq.length receiver_prefix_received ==>
          Seq.equal sender_suffix_sent receiver_suffix_received
        with
        lemma_append_tails_equal_same_len
          sender_prefix_sent
          sender_suffix_sent
          receiver_prefix_received
          receiver_suffix_received ) ) )

let lemma_sent_received_replay_append_split_equal_tails_from_aligned_prefixes
  (sender_model:connection_model)
  (receiver_model:connection_model)
  (sender_prefix:list conn_event)
  (sender_suffix:list conn_event)
  (receiver_prefix:list conn_event)
  (receiver_suffix:list conn_event)
  (sender_raw_sent:B.bytes)
  (sender_raw_received:B.bytes)
  (receiver_raw_sent:B.bytes)
  (receiver_raw_received:B.bytes)
  (sender_final:connection_model)
  (receiver_final:connection_model)
  (prefix_lengths_aligned:
    (sender_mid:connection_model) ->
    (receiver_mid:connection_model) ->
    (sender_prefix_sent:B.bytes) ->
    (sender_prefix_received:B.bytes) ->
    (sender_suffix_sent:B.bytes) ->
    (sender_suffix_received:B.bytes) ->
    (receiver_prefix_sent:B.bytes) ->
    (receiver_prefix_received:B.bytes) ->
    (receiver_suffix_sent:B.bytes) ->
    (receiver_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal
          sender_raw_sent
          (B.append sender_prefix_sent sender_suffix_sent) /\
        Seq.equal
          sender_raw_received
          (B.append sender_prefix_received sender_suffix_received) /\
        Seq.equal
          receiver_raw_sent
          (B.append receiver_prefix_sent receiver_suffix_sent) /\
        Seq.equal
          receiver_raw_received
          (B.append receiver_prefix_received receiver_suffix_received) /\
        conn_events_sent_seal_replay
          sender_model
          sender_prefix
          sender_prefix_sent
          sender_prefix_received
          sender_mid /\
        conn_events_sent_seal_replay
          sender_mid
          sender_suffix
          sender_suffix_sent
          sender_suffix_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_model
          receiver_prefix
          receiver_prefix_sent
          receiver_prefix_received
          receiver_mid /\
        conn_events_received_decode_replay
          receiver_mid
          receiver_suffix
          receiver_suffix_sent
          receiver_suffix_received
          receiver_final)
      (ensures
        Seq.length sender_prefix_sent == Seq.length receiver_prefix_received))
  : Lemma
      (requires
        conn_events_sent_seal_replay
          sender_model
          (FStar.List.Tot.append sender_prefix sender_suffix)
          sender_raw_sent
          sender_raw_received
          sender_final /\
        conn_events_received_decode_replay
          receiver_model
          (FStar.List.Tot.append receiver_prefix receiver_suffix)
          receiver_raw_sent
          receiver_raw_received
          receiver_final /\
        Seq.equal sender_raw_sent receiver_raw_received)
      (ensures
        exists sender_mid receiver_mid
          sender_prefix_sent sender_prefix_received
          sender_suffix_sent sender_suffix_received
          receiver_prefix_sent receiver_prefix_received
          receiver_suffix_sent receiver_suffix_received.
          Seq.equal
            sender_raw_sent
            (B.append sender_prefix_sent sender_suffix_sent) /\
          Seq.equal
            sender_raw_received
            (B.append sender_prefix_received sender_suffix_received) /\
          Seq.equal
            receiver_raw_sent
            (B.append receiver_prefix_sent receiver_suffix_sent) /\
          Seq.equal
            receiver_raw_received
            (B.append receiver_prefix_received receiver_suffix_received) /\
          conn_events_sent_seal_replay
            sender_model
            sender_prefix
            sender_prefix_sent
            sender_prefix_received
            sender_mid /\
          conn_events_sent_seal_replay
            sender_mid
            sender_suffix
            sender_suffix_sent
            sender_suffix_received
            sender_final /\
          conn_events_received_decode_replay
            receiver_model
            receiver_prefix
            receiver_prefix_sent
            receiver_prefix_received
            receiver_mid /\
          conn_events_received_decode_replay
            receiver_mid
            receiver_suffix
            receiver_suffix_sent
            receiver_suffix_received
            receiver_final /\
          Seq.equal sender_suffix_sent receiver_suffix_received)
=
  lemma_sent_received_replay_append_split_equal_tails
    sender_model
    receiver_model
    sender_prefix
    sender_suffix
    receiver_prefix
    receiver_suffix
    sender_raw_sent
    sender_raw_received
    receiver_raw_sent
    receiver_raw_received
    sender_final
    receiver_final;
  eliminate exists
    (sender_mid:connection_model)
    (receiver_mid:connection_model)
    (sender_prefix_sent:B.bytes)
    (sender_prefix_received:B.bytes)
    (sender_suffix_sent:B.bytes)
    (sender_suffix_received:B.bytes)
    (receiver_prefix_sent:B.bytes)
    (receiver_prefix_received:B.bytes)
    (receiver_suffix_sent:B.bytes)
    (receiver_suffix_received:B.bytes).
    Seq.equal
      sender_raw_sent
      (B.append sender_prefix_sent sender_suffix_sent) /\
    Seq.equal
      sender_raw_received
      (B.append sender_prefix_received sender_suffix_received) /\
    Seq.equal
      receiver_raw_sent
      (B.append receiver_prefix_sent receiver_suffix_sent) /\
    Seq.equal
      receiver_raw_received
      (B.append receiver_prefix_received receiver_suffix_received) /\
    conn_events_sent_seal_replay
      sender_model
      sender_prefix
      sender_prefix_sent
      sender_prefix_received
      sender_mid /\
    conn_events_sent_seal_replay
      sender_mid
      sender_suffix
      sender_suffix_sent
      sender_suffix_received
      sender_final /\
    conn_events_received_decode_replay
      receiver_model
      receiver_prefix
      receiver_prefix_sent
      receiver_prefix_received
      receiver_mid /\
    conn_events_received_decode_replay
      receiver_mid
      receiver_suffix
      receiver_suffix_sent
      receiver_suffix_received
      receiver_final /\
    (Seq.length sender_prefix_sent ==
       Seq.length receiver_prefix_received ==>
     Seq.equal sender_suffix_sent receiver_suffix_received)
  with
  ( prefix_lengths_aligned
      sender_mid
      receiver_mid
      sender_prefix_sent
      sender_prefix_received
      sender_suffix_sent
      sender_suffix_received
      receiver_prefix_sent
      receiver_prefix_received
      receiver_suffix_sent
      receiver_suffix_received;
    assert (Seq.equal sender_suffix_sent receiver_suffix_received);
    introduce exists
      (sender_mid':connection_model)
      (receiver_mid':connection_model)
      (sender_prefix_sent':B.bytes)
      (sender_prefix_received':B.bytes)
      (sender_suffix_sent':B.bytes)
      (sender_suffix_received':B.bytes)
      (receiver_prefix_sent':B.bytes)
      (receiver_prefix_received':B.bytes)
      (receiver_suffix_sent':B.bytes)
      (receiver_suffix_received':B.bytes).
      Seq.equal
        sender_raw_sent
        (B.append sender_prefix_sent' sender_suffix_sent') /\
      Seq.equal
        sender_raw_received
        (B.append sender_prefix_received' sender_suffix_received') /\
      Seq.equal
        receiver_raw_sent
        (B.append receiver_prefix_sent' receiver_suffix_sent') /\
      Seq.equal
        receiver_raw_received
        (B.append receiver_prefix_received' receiver_suffix_received') /\
      conn_events_sent_seal_replay
        sender_model
        sender_prefix
        sender_prefix_sent'
        sender_prefix_received'
        sender_mid' /\
      conn_events_sent_seal_replay
        sender_mid'
        sender_suffix
        sender_suffix_sent'
        sender_suffix_received'
        sender_final /\
      conn_events_received_decode_replay
        receiver_model
        receiver_prefix
        receiver_prefix_sent'
        receiver_prefix_received'
        receiver_mid' /\
      conn_events_received_decode_replay
        receiver_mid'
        receiver_suffix
        receiver_suffix_sent'
        receiver_suffix_received'
        receiver_final /\
      Seq.equal sender_suffix_sent' receiver_suffix_received'
    with
      sender_mid
      receiver_mid
      sender_prefix_sent
      sender_prefix_received
      sender_suffix_sent
      sender_suffix_received
      receiver_prefix_sent
      receiver_prefix_received
      receiver_suffix_sent
      receiver_suffix_received
    and () )

let lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
  (model:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (prefixes_equal:
    (sent_mid:connection_model) ->
    (received_mid:connection_model) ->
    (sent_prefix_sent:B.bytes) ->
    (sent_prefix_received:B.bytes) ->
    (sent_suffix_sent:B.bytes) ->
    (sent_suffix_received:B.bytes) ->
    (received_prefix_sent:B.bytes) ->
    (received_prefix_received:B.bytes) ->
    (received_suffix_sent:B.bytes) ->
    (received_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
        Seq.equal raw_received
          (B.append sent_prefix_received sent_suffix_received) /\
        Seq.equal raw_sent
          (B.append received_prefix_sent received_suffix_sent) /\
        Seq.equal raw_received
          (B.append received_prefix_received received_suffix_received) /\
        conn_events_sent_seal_replay
          model
          prefix
          sent_prefix_sent
          sent_prefix_received
          sent_mid /\
        conn_events_sent_seal_replay
          sent_mid
          suffix
          sent_suffix_sent
          sent_suffix_received
          final_model /\
        conn_events_received_decode_replay
          model
          prefix
          received_prefix_sent
          received_prefix_received
          received_mid /\
        conn_events_received_decode_replay
          received_mid
          suffix
          received_suffix_sent
          received_suffix_received
          final_model)
      (ensures
        Seq.equal sent_prefix_sent received_prefix_sent /\
        Seq.equal sent_prefix_received received_prefix_received))
  : Lemma
      (requires
        conn_events_sent_seal_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model /\
        conn_events_received_decode_replay
          model
          (FStar.List.Tot.append prefix suffix)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists mid prefix_sent prefix_received suffix_sent suffix_received.
          Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
          Seq.equal raw_received (B.append prefix_received suffix_received) /\
          conn_events_sent_seal_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          conn_events_sent_seal_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model /\
          conn_events_received_decode_replay
            model
            prefix
            prefix_sent
            prefix_received
            mid /\
          conn_events_received_decode_replay
            mid
            suffix
            suffix_sent
            suffix_received
            final_model)
=
  lemma_conn_events_sent_seal_replay_append_split
    model
    prefix
    suffix
    raw_sent
    raw_received
    final_model;
  eliminate exists
    (sent_mid:connection_model)
    (sent_prefix_sent:B.bytes)
    (sent_prefix_received:B.bytes)
    (sent_suffix_sent:B.bytes)
    (sent_suffix_received:B.bytes).
    Seq.equal raw_sent (B.append sent_prefix_sent sent_suffix_sent) /\
    Seq.equal raw_received
      (B.append sent_prefix_received sent_suffix_received) /\
    conn_events_sent_seal_replay
      model
      prefix
      sent_prefix_sent
      sent_prefix_received
      sent_mid /\
    conn_events_sent_seal_replay
      sent_mid
      suffix
      sent_suffix_sent
      sent_suffix_received
      final_model
  with
  ( lemma_conn_events_received_decode_replay_append_split
      model
      prefix
      suffix
      raw_sent
      raw_received
      final_model;
    eliminate exists
      (received_mid:connection_model)
      (received_prefix_sent:B.bytes)
      (received_prefix_received:B.bytes)
      (received_suffix_sent:B.bytes)
      (received_suffix_received:B.bytes).
      Seq.equal raw_sent
        (B.append received_prefix_sent received_suffix_sent) /\
      Seq.equal raw_received
        (B.append received_prefix_received received_suffix_received) /\
      conn_events_received_decode_replay
        model
        prefix
        received_prefix_sent
        received_prefix_received
        received_mid /\
      conn_events_received_decode_replay
        received_mid
        suffix
        received_suffix_sent
        received_suffix_received
        final_model
    with
    ( prefixes_equal
        sent_mid
        received_mid
        sent_prefix_sent
        sent_prefix_received
        sent_suffix_sent
        sent_suffix_received
        received_prefix_sent
        received_prefix_received
        received_suffix_sent
        received_suffix_received;
      assert (Seq.equal sent_prefix_sent received_prefix_sent);
      assert (Seq.equal sent_prefix_received received_prefix_received);
      assert (
        Seq.equal
          (B.append sent_prefix_sent sent_suffix_sent)
          (B.append received_prefix_sent received_suffix_sent));
      assert (
        Seq.equal
          (B.append sent_prefix_received sent_suffix_received)
          (B.append received_prefix_received received_suffix_received));
      lemma_append_tails_equal_from_equal_heads
        sent_prefix_sent
        sent_suffix_sent
        received_prefix_sent
        received_suffix_sent;
      lemma_append_tails_equal_from_equal_heads
        sent_prefix_received
        sent_suffix_received
        received_prefix_received
        received_suffix_received;
      assert (Seq.equal sent_suffix_sent received_suffix_sent);
      assert (Seq.equal sent_suffix_received received_suffix_received);
      lemma_conn_events_sent_received_replays_same_events_final_model_equal
        model
        prefix
        sent_prefix_sent
        sent_prefix_received
        sent_mid
        received_prefix_sent
        received_prefix_received
        received_mid;
      assert (sent_mid == received_mid);
      Seq.lemma_eq_elim received_prefix_sent sent_prefix_sent;
      Seq.lemma_eq_elim received_prefix_received sent_prefix_received;
      Seq.lemma_eq_elim received_suffix_sent sent_suffix_sent;
      Seq.lemma_eq_elim received_suffix_received sent_suffix_received;
      assert (
        conn_events_received_decode_replay
          model
          prefix
          sent_prefix_sent
          sent_prefix_received
          sent_mid);
      assert (
        conn_events_received_decode_replay
          sent_mid
          suffix
          sent_suffix_sent
          sent_suffix_received
          final_model);
      introduce exists
        (mid:connection_model)
        (prefix_sent:B.bytes)
        (prefix_received:B.bytes)
        (suffix_sent:B.bytes)
        (suffix_received:B.bytes).
        Seq.equal raw_sent (B.append prefix_sent suffix_sent) /\
        Seq.equal raw_received (B.append prefix_received suffix_received) /\
        conn_events_sent_seal_replay
          model
          prefix
          prefix_sent
          prefix_received
          mid /\
        conn_events_sent_seal_replay
          mid
          suffix
          suffix_sent
          suffix_received
          final_model /\
        conn_events_received_decode_replay
          model
          prefix
          prefix_sent
          prefix_received
          mid /\
        conn_events_received_decode_replay
          mid
          suffix
          suffix_sent
          suffix_received
          final_model
      with
        sent_mid
        sent_prefix_sent
        sent_prefix_received
        sent_suffix_sent
        sent_suffix_received
      and () ) )

let lemma_paired_replay_suffixes_equal_from_equal_prefixes
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_prefix_sent:B.bytes)
  (server_prefix_received:B.bytes)
  (server_suffix_sent:B.bytes)
  (server_suffix_received:B.bytes)
  (client_prefix_sent:B.bytes)
  (client_prefix_received:B.bytes)
  (client_suffix_sent:B.bytes)
  (client_suffix_received:B.bytes)
  : Lemma
    (requires
      Seq.equal server_full_sent client_full_received /\
      Seq.equal client_full_sent server_full_received /\
      Seq.equal server_full_sent
        (B.append server_prefix_sent server_suffix_sent) /\
      Seq.equal server_full_received
        (B.append server_prefix_received server_suffix_received) /\
      Seq.equal client_full_sent
        (B.append client_prefix_sent client_suffix_sent) /\
      Seq.equal client_full_received
        (B.append client_prefix_received client_suffix_received) /\
      Seq.equal server_prefix_sent client_prefix_received /\
      Seq.equal client_prefix_sent server_prefix_received)
    (ensures
      Seq.equal server_suffix_sent client_suffix_received /\
      Seq.equal client_suffix_sent server_suffix_received)
=
  assert (
    Seq.equal
      (B.append server_prefix_sent server_suffix_sent)
      (B.append client_prefix_received client_suffix_received));
  lemma_append_tails_equal_from_equal_heads
    server_prefix_sent
    server_suffix_sent
    client_prefix_received
    client_suffix_received;
  assert (
    Seq.equal
      (B.append client_prefix_sent client_suffix_sent)
      (B.append server_prefix_received server_suffix_received));
  lemma_append_tails_equal_from_equal_heads
    client_prefix_sent
    client_suffix_sent
    server_prefix_received
    server_suffix_received;
  assert (Seq.equal server_suffix_sent client_suffix_received);
  assert (Seq.equal client_suffix_sent server_suffix_received)

let lemma_paired_replay_suffix_views_from_full_replays_with_equal_prefixes
  (server_model:connection_model)
  (client_model:connection_model)
  (server_prefix:list conn_event)
  (server_suffix:list conn_event)
  (client_prefix:list conn_event)
  (client_suffix:list conn_event)
  (server_full_sent:B.bytes)
  (server_full_received:B.bytes)
  (client_full_sent:B.bytes)
  (client_full_received:B.bytes)
  (server_final:connection_model)
  (client_final:connection_model)
  (server_prefixes_equal:
    (sent_mid:connection_model) ->
    (received_mid:connection_model) ->
    (sent_prefix_sent:B.bytes) ->
    (sent_prefix_received:B.bytes) ->
    (sent_suffix_sent:B.bytes) ->
    (sent_suffix_received:B.bytes) ->
    (received_prefix_sent:B.bytes) ->
    (received_prefix_received:B.bytes) ->
    (received_suffix_sent:B.bytes) ->
    (received_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal
          server_full_sent
          (B.append sent_prefix_sent sent_suffix_sent) /\
        Seq.equal
          server_full_received
          (B.append sent_prefix_received sent_suffix_received) /\
        Seq.equal
          server_full_sent
          (B.append received_prefix_sent received_suffix_sent) /\
        Seq.equal
          server_full_received
          (B.append received_prefix_received received_suffix_received) /\
        conn_events_sent_seal_replay
          server_model
          server_prefix
          sent_prefix_sent
          sent_prefix_received
          sent_mid /\
        conn_events_sent_seal_replay
          sent_mid
          server_suffix
          sent_suffix_sent
          sent_suffix_received
          server_final /\
        conn_events_received_decode_replay
          server_model
          server_prefix
          received_prefix_sent
          received_prefix_received
          received_mid /\
        conn_events_received_decode_replay
          received_mid
          server_suffix
          received_suffix_sent
          received_suffix_received
          server_final)
      (ensures
        Seq.equal sent_prefix_sent received_prefix_sent /\
        Seq.equal sent_prefix_received received_prefix_received))
  (client_prefixes_equal:
    (sent_mid:connection_model) ->
    (received_mid:connection_model) ->
    (sent_prefix_sent:B.bytes) ->
    (sent_prefix_received:B.bytes) ->
    (sent_suffix_sent:B.bytes) ->
    (sent_suffix_received:B.bytes) ->
    (received_prefix_sent:B.bytes) ->
    (received_prefix_received:B.bytes) ->
    (received_suffix_sent:B.bytes) ->
    (received_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal
          client_full_sent
          (B.append sent_prefix_sent sent_suffix_sent) /\
        Seq.equal
          client_full_received
          (B.append sent_prefix_received sent_suffix_received) /\
        Seq.equal
          client_full_sent
          (B.append received_prefix_sent received_suffix_sent) /\
        Seq.equal
          client_full_received
          (B.append received_prefix_received received_suffix_received) /\
        conn_events_sent_seal_replay
          client_model
          client_prefix
          sent_prefix_sent
          sent_prefix_received
          sent_mid /\
        conn_events_sent_seal_replay
          sent_mid
          client_suffix
          sent_suffix_sent
          sent_suffix_received
          client_final /\
        conn_events_received_decode_replay
          client_model
          client_prefix
          received_prefix_sent
          received_prefix_received
          received_mid /\
        conn_events_received_decode_replay
          received_mid
          client_suffix
          received_suffix_sent
          received_suffix_received
          client_final)
      (ensures
        Seq.equal sent_prefix_sent received_prefix_sent /\
        Seq.equal sent_prefix_received received_prefix_received))
  (paired_prefixes_equal:
    (server_mid:connection_model) ->
    (client_mid:connection_model) ->
    (server_prefix_sent:B.bytes) ->
    (server_prefix_received:B.bytes) ->
    (server_suffix_sent:B.bytes) ->
    (server_suffix_received:B.bytes) ->
    (client_prefix_sent:B.bytes) ->
    (client_prefix_received:B.bytes) ->
    (client_suffix_sent:B.bytes) ->
    (client_suffix_received:B.bytes) ->
    Lemma
      (requires
        Seq.equal
          server_full_sent
          (B.append server_prefix_sent server_suffix_sent) /\
        Seq.equal
          server_full_received
          (B.append server_prefix_received server_suffix_received) /\
        Seq.equal
          client_full_sent
          (B.append client_prefix_sent client_suffix_sent) /\
        Seq.equal
          client_full_received
          (B.append client_prefix_received client_suffix_received) /\
        conn_events_sent_seal_replay
          server_model
          server_prefix
          server_prefix_sent
          server_prefix_received
          server_mid /\
        conn_events_sent_seal_replay
          server_mid
          server_suffix
          server_suffix_sent
          server_suffix_received
          server_final /\
        conn_events_received_decode_replay
          server_model
          server_prefix
          server_prefix_sent
          server_prefix_received
          server_mid /\
        conn_events_received_decode_replay
          server_mid
          server_suffix
          server_suffix_sent
          server_suffix_received
          server_final /\
        conn_events_sent_seal_replay
          client_model
          client_prefix
          client_prefix_sent
          client_prefix_received
          client_mid /\
        conn_events_sent_seal_replay
          client_mid
          client_suffix
          client_suffix_sent
          client_suffix_received
          client_final /\
        conn_events_received_decode_replay
          client_model
          client_prefix
          client_prefix_sent
          client_prefix_received
          client_mid /\
        conn_events_received_decode_replay
          client_mid
          client_suffix
          client_suffix_sent
          client_suffix_received
          client_final)
      (ensures
        Seq.equal server_prefix_sent client_prefix_received /\
        Seq.equal client_prefix_sent server_prefix_received))
  : Lemma
      (requires
        Seq.equal server_full_sent client_full_received /\
        Seq.equal client_full_sent server_full_received /\
        conn_events_sent_seal_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_received_decode_replay
          server_model
          (FStar.List.Tot.append server_prefix server_suffix)
          server_full_sent
          server_full_received
          server_final /\
        conn_events_sent_seal_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final /\
        conn_events_received_decode_replay
          client_model
          (FStar.List.Tot.append client_prefix client_suffix)
          client_full_sent
          client_full_received
          client_final)
      (ensures
        exists server_mid client_mid
          server_suffix_sent server_suffix_received
          client_suffix_sent client_suffix_received.
          Seq.equal server_suffix_sent client_suffix_received /\
          Seq.equal client_suffix_sent server_suffix_received /\
          conn_events_sent_seal_replay
            server_mid
            server_suffix
            server_suffix_sent
            server_suffix_received
            server_final /\
          conn_events_received_decode_replay
            server_mid
            server_suffix
            server_suffix_sent
            server_suffix_received
            server_final /\
          conn_events_sent_seal_replay
            client_mid
            client_suffix
            client_suffix_sent
            client_suffix_received
            client_final /\
          conn_events_received_decode_replay
            client_mid
            client_suffix
            client_suffix_sent
            client_suffix_received
            client_final)
=
  lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
    server_model
    server_prefix
    server_suffix
    server_full_sent
    server_full_received
    server_final
    server_prefixes_equal;
  eliminate exists
    (server_mid:connection_model)
    (server_prefix_sent:B.bytes)
    (server_prefix_received:B.bytes)
    (server_suffix_sent:B.bytes)
    (server_suffix_received:B.bytes).
    Seq.equal server_full_sent
      (B.append server_prefix_sent server_suffix_sent) /\
    Seq.equal server_full_received
      (B.append server_prefix_received server_suffix_received) /\
    conn_events_sent_seal_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_sent_seal_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final /\
    conn_events_received_decode_replay
      server_model
      server_prefix
      server_prefix_sent
      server_prefix_received
      server_mid /\
    conn_events_received_decode_replay
      server_mid
      server_suffix
      server_suffix_sent
      server_suffix_received
      server_final
  with
  ( lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
      client_model
      client_prefix
      client_suffix
      client_full_sent
      client_full_received
      client_final
      client_prefixes_equal;
    eliminate exists
      (client_mid:connection_model)
      (client_prefix_sent:B.bytes)
      (client_prefix_received:B.bytes)
      (client_suffix_sent:B.bytes)
      (client_suffix_received:B.bytes).
      Seq.equal client_full_sent
        (B.append client_prefix_sent client_suffix_sent) /\
      Seq.equal client_full_received
        (B.append client_prefix_received client_suffix_received) /\
      conn_events_sent_seal_replay
        client_model
        client_prefix
        client_prefix_sent
        client_prefix_received
        client_mid /\
      conn_events_sent_seal_replay
        client_mid
        client_suffix
        client_suffix_sent
        client_suffix_received
        client_final /\
      conn_events_received_decode_replay
        client_model
        client_prefix
        client_prefix_sent
        client_prefix_received
        client_mid /\
      conn_events_received_decode_replay
        client_mid
        client_suffix
        client_suffix_sent
        client_suffix_received
        client_final
    with
    ( paired_prefixes_equal
        server_mid
        client_mid
        server_prefix_sent
        server_prefix_received
        server_suffix_sent
        server_suffix_received
        client_prefix_sent
        client_prefix_received
        client_suffix_sent
        client_suffix_received;
      lemma_paired_replay_suffixes_equal_from_equal_prefixes
        server_full_sent
        server_full_received
        client_full_sent
        client_full_received
        server_prefix_sent
        server_prefix_received
        server_suffix_sent
        server_suffix_received
        client_prefix_sent
        client_prefix_received
        client_suffix_sent
        client_suffix_received;
      assert (Seq.equal server_suffix_sent client_suffix_received);
      assert (Seq.equal client_suffix_sent server_suffix_received);
      introduce exists
        (server_mid':connection_model)
        (client_mid':connection_model)
        (server_suffix_sent':B.bytes)
        (server_suffix_received':B.bytes)
        (client_suffix_sent':B.bytes)
        (client_suffix_received':B.bytes).
        Seq.equal server_suffix_sent' client_suffix_received' /\
        Seq.equal client_suffix_sent' server_suffix_received' /\
        conn_events_sent_seal_replay
          server_mid'
          server_suffix
          server_suffix_sent'
          server_suffix_received'
          server_final /\
        conn_events_received_decode_replay
          server_mid'
          server_suffix
          server_suffix_sent'
          server_suffix_received'
          server_final /\
        conn_events_sent_seal_replay
          client_mid'
          client_suffix
          client_suffix_sent'
          client_suffix_received'
          client_final /\
        conn_events_received_decode_replay
          client_mid'
          client_suffix
          client_suffix_sent'
          client_suffix_received'
          client_final
      with
        server_mid
        client_mid
        server_suffix_sent
        server_suffix_received
        client_suffix_sent
        client_suffix_received
      and () ) )
