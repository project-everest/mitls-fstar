module TLS13.Impl.Channel

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.Spec.StateMachine.Log
module L = FStar.List.Tot

open FStar.List.Tot

let rec observable_received (messages:list B.bytes)
  : GTot (list B.bytes) (decreases messages)
=
  match messages with
  | [] -> []
  | message :: rest ->
    if B.length message == 0
    then observable_received rest
    else message :: observable_received rest

let application_log (st:CS.connection_state)
  : GTot (CI.application_log B.bytes) =
  {
    CI.sent = st.CS.cs_model.CS.model_application.CS.app_log.CL.app_sent;
    CI.received =
      observable_received
        st.CS.cs_model.CS.model_application.CS.app_log.CL.app_received;
  }

let rec lemma_observable_received_append
  (left right:list B.bytes)
  : Lemma
      (ensures
        observable_received (left @ right) ==
          observable_received left @ observable_received right)
      (decreases left)
=
  match left with
  | [] -> ()
  | message :: rest ->
    lemma_observable_received_append rest right

let event_log_extends
  (old_events:list CS.conn_event)
  (new_events:list CS.conn_event)
  : prop =
  exists delta. new_events == old_events @ delta

let lemma_event_log_extends_refl (events:list CS.conn_event)
  : Lemma (event_log_extends events events)
=
  L.append_l_nil events

let lemma_event_log_extends_snoc
  (events:list CS.conn_event)
  (ev:CS.conn_event)
  : Lemma (event_log_extends events (events @ [ev]))
=
  ()

let lemma_event_log_extends_trans
  (events0 events1 events2:list CS.conn_event)
  : Lemma
      (requires
        event_log_extends events0 events1 /\
        event_log_extends events1 events2)
      (ensures event_log_extends events0 events2)
=
  let delta01 =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (list CS.conn_event)
      (fun delta -> events1 == events0 @ delta) in
  let delta12 =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (list CS.conn_event)
      (fun delta -> events2 == events1 @ delta) in
  L.append_assoc events0 (Ghost.reveal delta01) (Ghost.reveal delta12);
  assert (events2 ==
    events0 @ ((Ghost.reveal delta01) @ (Ghost.reveal delta12)))

let rec lemma_app_sent_messages_append
  (left right:list CS.conn_event)
  : Lemma
      (ensures
        CSL.app_sent_messages (left @ right) ==
        CSL.app_sent_messages left @ CSL.app_sent_messages right)
      (decreases left)
=
  match left with
  | [] -> ()
  | ev :: rest ->
    lemma_app_sent_messages_append rest right;
    L.append_assoc
      (CSL.conn_event_app_sent_delta ev)
      (CSL.app_sent_messages rest)
      (CSL.app_sent_messages right)

let rec lemma_app_received_messages_append
  (left right:list CS.conn_event)
  : Lemma
      (ensures
        CSL.app_received_messages (left @ right) ==
        CSL.app_received_messages left @ CSL.app_received_messages right)
      (decreases left)
=
  match left with
  | [] -> ()
  | ev :: rest ->
    lemma_app_received_messages_append rest right;
    L.append_assoc
      (CSL.conn_event_app_received_delta ev)
      (CSL.app_received_messages rest)
      (CSL.app_received_messages right)

let lemma_application_log_extends_from_event_logs
  (st0 st1:CS.connection_state)
  : Lemma
      (requires
        CSL.connection_state_app_log_consistent st0 /\
        CSL.connection_state_app_log_consistent st1 /\
        event_log_extends st0.CS.cs_event_log st1.CS.cs_event_log)
      (ensures
        CI.application_log_extends (application_log st0) (application_log st1))
=
  let delta =
    FStar.IndefiniteDescription.indefinite_description_ghost
      (list CS.conn_event)
      (fun delta -> st1.CS.cs_event_log == st0.CS.cs_event_log @ delta) in
  lemma_app_sent_messages_append
    st0.CS.cs_event_log
    (Ghost.reveal delta);
  lemma_app_received_messages_append
    st0.CS.cs_event_log
    (Ghost.reveal delta);
  lemma_observable_received_append
    (CSL.app_received_messages st0.CS.cs_event_log)
    (CSL.app_received_messages (Ghost.reveal delta));
  assert (exists sent_delta received_delta.
    (application_log st1).CI.sent ==
      (application_log st0).CI.sent @ sent_delta /\
    (application_log st1).CI.received ==
      (application_log st0).CI.received @ received_delta)
