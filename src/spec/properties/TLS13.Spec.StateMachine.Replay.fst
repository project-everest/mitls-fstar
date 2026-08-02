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

(* ==================================================================== *)
(* Single-message head steps normalise to network events.               *)
(*                                                                      *)
(* A client-received protected handshake record carrying exactly one    *)
(* message is described by a HEAD [ConnProtectedHandshake] step whose    *)
(* [consumed] saturates the fragment.  The implementation emits only    *)
(* this form.  The lemmas below show that such a step denotes the SAME   *)
(* transition -- same legality, same successor model, same raw          *)
(* accounting, same decode projection -- as the [ConnNetworkEvent]      *)
(* carrying the message.  This is what lets the receiver-side pairing   *)
(* proofs, which are written against the network shape, apply unchanged. *)
(* ==================================================================== *)

let single_message_head_step_shape (step:protected_handshake_step) : prop =
  step.protected_handshake_head /\
  step.protected_handshake_offset == 0 /\
  step.protected_handshake_consumed ==
    B.length step.protected_handshake_fragment

let head_step_network_event (step:protected_handshake_step) : conn_event =
  ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake step.protected_handshake_message;
  }

let lemma_single_message_head_step_legal
  (model:connection_model)
  (step:protected_handshake_step)
  : Lemma
      (requires legal_protected_handshake_step model step)
      (ensures legal_event model (head_step_network_event step))
  = ()

let lemma_single_message_head_step_model
  (model:connection_model)
  (step:protected_handshake_step)
  : Lemma
      (requires
        legal_protected_handshake_step model step /\
        single_message_head_step_shape step)
      (ensures
        step_model model (ConnProtectedHandshake step) ==
        step_model model (head_step_network_event step))
  =
  match step_handshake_message model CL.Received step.protected_handshake_message with
  | None -> ()
  | Some stepped ->
    Seq.lemma_eq_elim
      stepped.model_handshake.hs_buffers.hb_encrypted_server_handshake_bytes
      B.empty

let lemma_single_message_head_step_raw_delta
  (model:connection_model)
  (step:protected_handshake_step)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        legal_protected_handshake_step model step /\
        single_message_head_step_shape step /\
        event_raw_delta_legal model (ConnProtectedHandshake step) raw_sent raw_received)
      (ensures
        event_raw_delta_legal model (head_step_network_event step) raw_sent raw_received)
  = ()

let lemma_single_message_head_step_decode
  (model:connection_model)
  (step:protected_handshake_step)
  (raw_received:B.bytes)
  : Lemma
      (requires
        legal_protected_handshake_step model step /\
        single_message_head_step_shape step /\
        received_event_nonempty_decode_projection
          model
          (ConnProtectedHandshake step)
          raw_received)
      (ensures
        received_event_nonempty_decode_projection
          model
          (head_step_network_event step)
          raw_received)
  =
  if B.length raw_received == 0
  then ()
  else begin
    FStar.Seq.Properties.slice_length step.protected_handshake_fragment;
    eliminate exists outer_fragment opened plaintext.
      W.parse_record_wire raw_received ==
        Some (T.Application_data, outer_fragment, B.length raw_received) /\
      received_record_opened model raw_received outer_fragment opened /\
      W.parse_plaintext opened == Some plaintext /\
      plaintext.M.content_type == T.Handshake /\
      Seq.equal plaintext.M.fragment step.protected_handshake_fragment /\
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
    returns
      received_event_nonempty_decode_projection
        model
        (head_step_network_event step)
        raw_received
    with _.
    ( Seq.lemma_eq_elim plaintext.M.fragment step.protected_handshake_fragment;
      W.lemma_parse_handshake_stream_def step.protected_handshake_fragment;
      W.lemma_parse_handshake_stream_whole step.protected_handshake_fragment;
      assert (W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
                Some (M.TlsHandshake step.protected_handshake_message));
      assert (received_single_protected_message_decode
                model
                (M.TlsHandshake step.protected_handshake_message)
                raw_received) )
  end

(* The replay-level statement: a received-decode replay whose head is a
   saturating head step is also a received-decode replay whose head is the
   corresponding network event, with the same tail, the same raw split and
   the same final model. *)
let lemma_single_message_head_step_replay_normalizes
  (model:connection_model)
  (step:protected_handshake_step)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        single_message_head_step_shape step /\
        conn_events_received_decode_replay
          model
          (ConnProtectedHandshake step :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_received_decode_replay
          model
          (head_step_network_event step :: rest)
          raw_sent
          raw_received
          final_model)
  =
  let ev = ConnProtectedHandshake step in
  let nev = head_step_network_event step in
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay model1 rest tail_sent tail_received final_model
  returns
    conn_events_received_decode_replay model (nev :: rest) raw_sent raw_received final_model
  with _.
  ( lemma_single_message_head_step_legal model step;
    lemma_single_message_head_step_model model step;
    lemma_single_message_head_step_raw_delta model step delta_sent delta_received;
    lemma_single_message_head_step_decode model step delta_received;
    introduce exists model1' delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model nev /\
      step_model model nev == Some model1' /\
      event_raw_delta_legal model nev delta_sent' delta_received' /\
      received_event_nonempty_decode_projection model nev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model
    with model1 delta_sent delta_received tail_sent tail_received
    and () )

(* The same normalisation one event later: the head step is the SECOND event
   of the replay, behind an arbitrary first event (in practice the client's
   traffic-key install).  Used by the server-flight inversion, which reasons
   about the flight starting from before the read-key install. *)

(* Explicit-witness introduction for a received-decode replay cons cell.

   The unfolding equation is established by normalisation rather than left to
   the SMT solver: with the tail list itself a cons, the fuel-guarded encoding
   of the recursive definition does not line up with the hypothesis. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_received_decode_replay_cons
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
        conn_events_received_decode_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model)
  =
  assert (conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_received_decode_replay model1 rest tail_sent tail_received final_model))
    by (FStar.Tactics.norm [delta_only [`%conn_events_received_decode_replay]; zeta; iota];
        FStar.Tactics.trefl ())
#pop-options

(* The same normalisation one event later: the head step is the SECOND event
   of the replay, behind the client's traffic-key install. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_single_message_head_step_replay_normalizes_after
  (model:connection_model)
  (local:local_event)
  (step:protected_handshake_step)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        single_message_head_step_shape step /\
        conn_events_received_decode_replay
          model
          (ConnLocalEvent local :: ConnProtectedHandshake step :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_received_decode_replay
          model
          (ConnLocalEvent local :: head_step_network_event step :: rest)
          raw_sent
          raw_received
          final_model)
  =
  let ev0 = ConnLocalEvent local in
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    legal_event model ev0 /\
    step_model model ev0 == Some model1 /\
    event_raw_delta_legal model ev0 delta_sent delta_received /\
    received_event_nonempty_decode_projection model ev0 delta_received /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_received_decode_replay
      model1 (ConnProtectedHandshake step :: rest) tail_sent tail_received final_model
  returns
    conn_events_received_decode_replay
      model (ConnLocalEvent local :: head_step_network_event step :: rest)
      raw_sent raw_received final_model
  with _.
  ( lemma_single_message_head_step_replay_normalizes
      model1 step rest tail_sent tail_received final_model;
    lemma_received_decode_replay_cons
      model ev0 (head_step_network_event step :: rest)
      raw_sent raw_received final_model
      model1 delta_sent delta_received tail_sent tail_received )
#pop-options

(* ==================================================================== *)
(* The same normalisation for SENT-seal replays.                        *)
(*                                                                      *)
(* A client's own log is replayed both ways: the received-decode replay  *)
(* accounts the bytes it decoded, the sent-seal replay accounts the      *)
(* bytes it sealed.  A received head step contributes nothing to the     *)
(* sent side, exactly like the network event it normalises to.          *)
(* ==================================================================== *)

let lemma_single_message_head_step_seal
  (model:connection_model)
  (step:protected_handshake_step)
  (raw_sent:B.bytes)
  : Lemma
      (requires
        sent_event_nonempty_seal_projection
          model
          (ConnProtectedHandshake step)
          raw_sent)
      (ensures
        sent_event_nonempty_seal_projection
          model
          (head_step_network_event step)
          raw_sent)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_sent_seal_replay_cons
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
        conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model)
  =
  assert (conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model))
    by (FStar.Tactics.norm [delta_only [`%conn_events_sent_seal_replay]; zeta; iota];
        FStar.Tactics.trefl ())
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_single_message_head_step_seal_replay_normalizes
  (model:connection_model)
  (step:protected_handshake_step)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        single_message_head_step_shape step /\
        conn_events_sent_seal_replay
          model
          (ConnProtectedHandshake step :: rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_sent_seal_replay
          model
          (head_step_network_event step :: rest)
          raw_sent
          raw_received
          final_model)
  =
  let ev = ConnProtectedHandshake step in
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
    legal_event model ev /\
    step_model model ev == Some model1 /\
    event_raw_delta_legal model ev delta_sent delta_received /\
    sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal raw_sent (B.append delta_sent tail_sent) /\
    Seq.equal raw_received (B.append delta_received tail_received) /\
    conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model
  returns
    conn_events_sent_seal_replay
      model (head_step_network_event step :: rest) raw_sent raw_received final_model
  with _.
  ( lemma_single_message_head_step_legal model step;
    lemma_single_message_head_step_model model step;
    lemma_single_message_head_step_raw_delta model step delta_sent delta_received;
    lemma_single_message_head_step_seal model step delta_sent;
    lemma_sent_seal_replay_cons
      model (head_step_network_event step) rest
      raw_sent raw_received final_model
      model1 delta_sent delta_received tail_sent tail_received )
#pop-options

(* The converse accounting transport: an implementation call site knows the
   record delta in the ORDINARY network-event form; the head step it actually
   emits accounts for exactly the same bytes. *)
let lemma_single_message_head_step_raw_delta_converse
  (model:connection_model)
  (step:protected_handshake_step)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        legal_protected_handshake_step model step /\
        single_message_head_step_shape step /\
        event_raw_delta_legal model (head_step_network_event step) raw_sent raw_received)
      (ensures
        event_raw_delta_legal model (ConnProtectedHandshake step) raw_sent raw_received)
  = ()
