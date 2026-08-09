module TLS13.ConnectionState.ProtectedWireServerFlightInversion.Region

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module SMReplay = TLS13.Spec.StateMachine.Replay
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module Seq = FStar.Seq
module L = FStar.List.Tot

(* The model reached after stepping [ev] from [model] (identity on failure). *)
let step_next (m:CS.connection_model) (ev:CS.conn_event) : GTot CS.connection_model =
  match CS.step_model m ev with
  | Some m' -> m'
  | None -> m

#push-options "--z3rlimit 10"
let peel_sent_empty_dsent
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Received)) /\
        SMReplay.conn_events_sent_seal_replay model (ev :: rest) rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        (exists (tr:B.bytes).
          SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs tr final))
=
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_sent B.empty);
    Seq.append_empty_l tail_sent;
    assert (Seq.equal rs tail_sent);
    Seq.lemma_eq_elim rs tail_sent;
    assert (step_next model ev == model1);
    introduce exists (tr:B.bytes).
      SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs tr final
    with tail_received
    and ()
  )
#pop-options

#push-options "--z3rlimit 10"
let peel_received_empty_drecv
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Sent)) /\
        SMReplay.conn_events_received_decode_replay model (ev :: rest) rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        (exists (ts:B.bytes).
          SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts rr final))
=
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_received B.empty);
    Seq.append_empty_l tail_received;
    assert (Seq.equal rr tail_received);
    Seq.lemma_eq_elim rr tail_received;
    assert (step_next model ev == model1);
    introduce exists (ts:B.bytes).
      SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts rr final
    with tail_sent
    and ()
  )
#pop-options

#push-options "--z3rlimit 10 --ifuel 1"
let rec lemma_empty_sent_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay model evs rs rr final /\
        L.for_all is_empty_sent_ev evs)
      (ensures Seq.equal rs B.empty)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    peel_sent_empty_dsent model ev rest rs rr final;
    eliminate exists (tr:B.bytes).
      SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs tr final
    with (
      lemma_empty_sent_tail_collapses (step_next model ev) rest rs tr final
    )
#pop-options

#push-options "--z3rlimit 10 --ifuel 1"
let rec lemma_empty_recv_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model evs rs rr final /\
        L.for_all is_empty_recv_ev evs)
      (ensures Seq.equal rr B.empty)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    peel_received_empty_drecv model ev rest rs rr final;
    eliminate exists (ts:B.bytes).
      SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts rr final
    with (
      lemma_empty_recv_tail_collapses (step_next model ev) rest ts rr final
    )
#pop-options
