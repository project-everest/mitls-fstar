module TLS13.Spec.StateMachine.Replay

(**
  Auxiliary: raw-wire seal/decode projections and replay consistency
  (segmented raw replay, sent-seal and received-decode replay, full-log
  consistency). Builds on TLS13.Spec.StateMachine and the Log/KeyMaterial layers.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

open FStar.List.Tot

open TLS13.Spec.StateMachine
include TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log

let rec raw_records_segmented
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Tot prop
        (decreases count)
  =
  if count == 0 then
    Seq.equal raw B.empty
  else
    exists fragment. exists (consumed:nat).
      W.parse_record raw == Some (outer, fragment, consumed) /\
      consumed > 0 /\
      consumed <= B.length raw /\
      raw_records_segmented
        (Seq.slice raw consumed (B.length raw))
        outer
        (count - 1)
let event_protected_single_raw_parse_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else if protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then
      match msg.CL.message_direction with
      | CL.Sent ->
        exists fragment.
          W.parse_record raw_sent ==
            Some (T.Application_data, fragment, B.length raw_sent)
      | CL.Received ->
        exists fragment.
         W.parse_record_wire raw_received ==
            Some (T.Application_data, fragment, B.length raw_received)
    else True
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
     exists fragment.
       W.parse_record_wire raw_received ==
         Some (T.Application_data, fragment, B.length raw_received)
    else True
  | ConnLocalEvent _ -> True
let event_protected_raw_parse_prefix_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else
      (match msg.CL.message_direction with
      | CL.Sent ->
        (exists fragment. exists (consumed:nat).
          W.parse_record raw_sent ==
            Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_sent)
      | CL.Received ->
        (exists fragment. exists (consumed:nat).
         W.parse_record_wire raw_received ==
            Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received))
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
      exists fragment. exists (consumed:nat).
       W.parse_record_wire raw_received ==
         Some (T.Application_data, fragment, consumed) /\
       consumed > 0 /\
       consumed <= B.length raw_received
    else True
  | ConnLocalEvent _ -> True
let event_protected_raw_decompose_prefix_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else
      (match msg.CL.message_direction with
      | CL.Sent ->
        (exists fragment. exists (consumed:nat).
          W.parse_record raw_sent ==
            Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_sent /\
          raw_records_exactly
            (Seq.slice raw_sent consumed (B.length raw_sent))
            T.Application_data
            (protected_record_count msg.CL.message_direction msg.CL.message_value - 1))
      | CL.Received ->
        (exists fragment. exists (consumed:nat).
         W.parse_record_wire raw_received ==
            Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received /\
          raw_records_exactly
            (Seq.slice raw_received consumed (B.length raw_received))
            T.Application_data
            (protected_record_count msg.CL.message_direction msg.CL.message_value - 1)))
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
      exists fragment. exists (consumed:nat).
        W.parse_record_wire raw_received ==
          Some (T.Application_data, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw_received /\
        raw_records_exactly
          (Seq.slice raw_received consumed (B.length raw_received))
          T.Application_data
          0
    else True
  | ConnLocalEvent _ -> True
let event_protected_raw_segmented_success
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : GTot prop =
  match ev with
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then True
    else
      (match msg.CL.message_direction with
      | CL.Sent ->
        raw_records_segmented
          raw_sent
          T.Application_data
          (protected_record_count msg.CL.message_direction msg.CL.message_value)
      | CL.Received ->
        raw_records_segmented
          raw_received
          T.Application_data
          (protected_record_count msg.CL.message_direction msg.CL.message_value))
  | ConnProtectedHandshake step ->
    raw_records_segmented
      raw_received
      T.Application_data
      (if step.protected_handshake_head then 1 else 0)
  | ConnLocalEvent _ -> True
let rec conn_events_raw_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_raw_replay model1 rest tail_sent tail_received final_model
let rec conn_events_protected_raw_segmented_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      event_protected_raw_segmented_success ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_protected_raw_segmented_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
let connection_state_raw_event_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_raw_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
let connection_state_protected_raw_segmented_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_protected_raw_segmented_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
let rec conn_events_sent_seal_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model
let rec conn_events_sent_seal_key_schedule_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
       (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      record_write_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_sent_seal_key_schedule_replay
       model1
       rest
       tail_sent
       tail_received
       final_model
let rec conn_events_received_decode_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_replay model1 rest tail_sent tail_received final_model
let rec conn_events_received_decode_key_schedule_replay
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Tot prop
        (decreases events)
  =
  match events with
  | [] ->
    Seq.equal raw_sent B.empty /\
    Seq.equal raw_received B.empty /\
    final_model == model
  | ev :: rest ->
    exists model1 delta_sent delta_received tail_sent tail_received.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      record_read_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_received_decode_key_schedule_replay
        model1
        rest
        tail_sent
        tail_received
        final_model
let connection_state_sent_seal_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_sent_seal_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
let connection_state_sent_seal_key_schedule_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_sent_seal_key_schedule_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
let connection_state_received_decode_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_received_decode_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
let connection_state_received_decode_key_schedule_replay_consistent
  (st:connection_state)
  : prop =
  conn_events_received_decode_key_schedule_replay
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
let connection_state_raw_to_message_replay_consistent
  (st:connection_state)
  : prop =
  connection_state_raw_event_replay_consistent st /\
  connection_state_protected_raw_segmented_replay_consistent st /\
  connection_state_sent_seal_replay_consistent st /\
  connection_state_sent_seal_key_schedule_replay_consistent st /\
  connection_state_received_decode_replay_consistent st /\
  connection_state_received_decode_key_schedule_replay_consistent st
let connection_state_full_log_consistent_for_role
  (role:endpoint_role)
  (st:connection_state)
  : prop =
  connection_state_layered_log_consistent_for_role role st /\
  connection_state_connection_log_view_consistent st /\
  connection_state_raw_event_replay_consistent st
let connection_state_full_log_consistent_for_config_role
  (st:connection_state)
  : prop =
  connection_state_full_log_consistent_for_role
    st.cs_model.model_config.config_role
    st
let connection_state_full_log_consistent
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ClientEndpoint /\
  connection_state_full_log_consistent_for_role ClientEndpoint st
