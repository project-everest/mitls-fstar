module TLS13.Impl.Server.ChannelLog

(**
  Application-log accounting for the server's channel surface.

  [TLS13.Impl.Channel.application_log] projects a connection state onto the
  pair of application byte-message lists that [Common.ChannelImplementation]
  reasons about.  The server driver's primitives are specified against
  [TLS13.Impl.Server.Types.server_local_event_end_to_end_correct] and its
  network counterpart, which speak about *events* rather than about the log.
  The lemmas here bridge the two, so that the channel layer can state the
  strong [CI.send_transition] / [CI.receive_transition] postconditions the
  generic [CI.channel_implementation] class requires.

  These are pure lemmas with no separation-logic content; they live in their
  own module so the Pulse channel module stays small.
**)

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.Spec.StateMachine.Log
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module TChannel = TLS13.Impl.Channel

(**
  A locally-generated send leaves the application *received* log alone and
  appends exactly [payload] to the application *sent* log when the step
  succeeds.  On any failure path the log is untouched.
**)
#push-options ""
let lemma_local_send_application_log
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (payload:B.bytes)
  (network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          ST.LocalSendApplicationData
          payload
          network_out
          app_out)
      (ensures
        TChannel.application_log st1 ==
          (if resp.ST.status == ST.StepOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  assert (ST.legal_handled_local_response
    st0
    st1
    resp
    ST.LocalSendApplicationData
    payload
    network_out
    app_out);
  if resp.ST.status == ST.StepOk then (
    assert (exists ev raw_sent raw_received.
      ST.legal_local_response
        st0
        st1
        resp
        ST.LocalSendApplicationData
        payload
        ev
        raw_sent
        raw_received
        network_out
        app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0
            st1
            resp
            ST.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0
            st1
            resp
            ST.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0
            st1
            resp
            ST.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    ST.lemma_legal_response_for_event_app_log_delta
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CSL.conn_event_app_sent_delta ev == [payload]);
    assert (CSL.conn_event_app_received_delta ev == []);
    assert (TChannel.application_log st1 ==
      CI.append_sent (TChannel.application_log st0) payload)
  ) else (
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    ST.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  )
#pop-options

(**
  The two application-data kinds are the only local events that move the
  application log; every other kind has empty sent and received deltas.
**)
let lemma_non_application_local_event_deltas
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : Lemma
      (requires
        ST.local_event_kind_matches kind payload ev /\
        kind <> ST.LocalDeliverApplicationData /\
        kind <> ST.LocalSendApplicationData)
      (ensures
        CSL.conn_event_app_sent_delta ev == [] /\
        CSL.conn_event_app_received_delta ev == [])
=
  match kind, ev with
  | ST.LocalDeliverApplicationData, _ -> assert False
  | ST.LocalSendApplicationData, _ -> assert False
  | _, _ -> ()

(**
  Every local event other than an application-data send or delivery leaves the
  application log completely alone -- successful or not.  This is what lets a
  KeyUpdate (spontaneous, or the RFC 8446 4.6.3 mandated reply) be inserted
  ahead of a channel operation without disturbing that operation's log
  equation.
**)
let lemma_local_event_preserves_application_log
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp kind payload network_out app_out /\
        kind <> ST.LocalSendApplicationData /\
        kind <> ST.LocalDeliverApplicationData)
      (ensures TChannel.application_log st1 == TChannel.application_log st0)
=
  assert (ST.legal_handled_local_response
    st0 st1 resp kind payload network_out app_out);
  if resp.ST.status == ST.StepOk then (
    assert (exists ev raw_sent raw_received.
      ST.legal_local_response
        st0 st1 resp kind payload ev raw_sent raw_received
        network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received
            network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received
            network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received
            network_out app_out) in
    ST.lemma_legal_response_for_event_app_log_delta
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    lemma_non_application_local_event_deltas kind payload ev;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  ) else (
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    ST.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  )

(**
  A received event whose *sent* application delta is empty moves the
  application log by exactly the response's application output.  A zero-length
  output leaves the log alone -- that is what
  [TChannel.observable_received] is for: the record layer can legally deliver a
  zero-length application-data fragment, and the channel must not report it as
  an application message.
**)
let lemma_legal_response_observable_receive_log
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent raw_received network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CSL.conn_event_app_sent_delta ev == [])
      (ensures
        (let output = ST.response_app_out resp app_out in
         TChannel.application_log st1 ==
           (if B.length output == 0
            then TChannel.application_log st0
            else CI.append_received (TChannel.application_log st0) output)))
=
  ST.lemma_legal_response_for_event_app_log_delta
    st0 st1 resp ev raw_sent raw_received network_out app_out;
  match ev with
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsApplicationData _ ->
       assert False
     | CL.Received, M.TlsApplicationData bytes ->
       assert (Seq.equal (ST.response_app_out resp app_out) bytes);
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [bytes]
     | _, _ ->
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [])
  | CS.ConnProtectedHandshake _ ->
    TChannel.lemma_observable_received_append
      st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
      []
  (* A cleartext buffering step delivers no application data. *)
  | CS.ConnCleartextHandshake _ ->
    TChannel.lemma_observable_received_append
      st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
      []
  | CS.ConnLocalEvent local ->
    (match local with
     | CS.LocalDeliverApplicationData bytes ->
       assert (Seq.equal (ST.response_app_out resp app_out) bytes);
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [bytes]
     | _ ->
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [])

(**
  A *received* network message never contributes to the application sent log:
  only a locally-originated [TlsApplicationData] send does, and the server's
  receive path emits none.
**)
let lemma_received_message_event_no_sent_delta
  (msg:M.tls_message)
  : Lemma
      (ensures
        CSL.conn_event_app_sent_delta (ST.received_message_event msg) == [])
=
  ()

(**
  A failing-alert transition rewrites only the control and failure fields of the
  model, so it leaves the application log untouched.
**)
let lemma_received_alert_failure_application_log
  (st:CS.connection_state)
  (alert:T.alert_description)
  (raw_received:B.bytes)
  : Lemma
      (ensures
        TChannel.application_log
          (CM.received_alert_failure_state st alert raw_received) ==
        TChannel.application_log st)
=
  ()

(**
  The application-log equation for one network step of the server's receive
  path, stated purely in terms of
  [ST.server_network_consumed_input_projection] -- which the buffered driver
  already establishes for every drive outcome.

  All six [ST.endpoint_status] cases are discharged:
  - [StepOk] delivers the decoded message's application delta, which is
    [ST.response_app_out] by [ST.response_app_out_matches_event];
  - [NeedMoreInput] and [IllegalTransition] do not move the state at all;
  - [DecodeError] steps through a [LocalFail] event, whose delta is empty;
  - [ConnectionFailed] steps through [CM.received_alert_failure_state];
  - [OutputBufferTooSmall] is refuted.
**)
#push-options "--z3rlimit 30"
let lemma_network_step_application_log
  (st0 st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out app_out)
      (ensures
        (let output = ST.response_app_out resp.ST.response app_out in
         TChannel.application_log st1 ==
           (if resp.ST.response.ST.status = ST.StepOk && B.length output <> 0
            then CI.append_received (TChannel.application_log st0) output
            else TChannel.application_log st0)))
=
  let output = ST.response_app_out resp.ST.response app_out in
  match resp.ST.response.ST.status with
  | ST.NeedMoreInput -> ()
  | ST.IllegalTransition -> ()
  | ST.OutputBufferTooSmall -> assert False
  | ST.DecodeError ->
    assert (ST.decode_error_response
      st0 st1 resp.ST.response network_out app_out);
    ST.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp.ST.response
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  | ST.ConnectionFailed ->
    assert (exists alert raw_received.
      st1 == CM.received_alert_failure_state st0 alert raw_received);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 == CM.received_alert_failure_state st0 alert raw_received) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 == CM.received_alert_failure_state st0 alert raw_received) in
    lemma_received_alert_failure_application_log st0 alert raw_received;
    assert (TChannel.application_log st1 == TChannel.application_log st0);
    assert (ST.legal_network_response
      st0 st1 resp.ST.response (M.TlsAlert alert)
      (ST.server_network_consumed_prefix resp input)
      network_out app_out);
    assert (Seq.equal output B.empty)
  | ST.StepOk ->
    if (exists step.
          ST.cleartext_handshake_step_correct
            st0
            st1
            resp.ST.response
            step
            (ST.server_network_consumed_prefix resp input)
            network_out
            app_out)
    then (
      (* G3: a cleartext buffering step delivers no message and no application
         bytes, so the application log is untouched. *)
      let step =
        ID.indefinite_description_ghost
          CS.cleartext_handshake_step
          (fun step ->
            ST.cleartext_handshake_step_correct
              st0
              st1
              resp.ST.response
              step
              (ST.server_network_consumed_prefix resp input)
              network_out
              app_out) in
      lemma_legal_response_observable_receive_log
        st0
        st1
        resp.ST.response
        (CS.ConnCleartextHandshake step)
        B.empty
        (ST.server_network_consumed_prefix resp input)
        network_out
        app_out
    ) else (
    assert (exists msg.
      ST.server_decoded_message_event_projection
        st0
        st1
        resp.ST.response
        msg
        (ST.server_network_consumed_prefix resp input)
        network_out
        app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          ST.server_decoded_message_event_projection
            st0
            st1
            resp.ST.response
            msg
            (ST.server_network_consumed_prefix resp input)
            network_out
            app_out) in
    (* [unexpected_message_response] forces [IllegalTransition], so the
       [StepOk] hypothesis selects the [legal_network_response] disjunct. *)
    assert (ST.legal_network_response
      st0
      st1
      resp.ST.response
      msg
      (ST.server_network_consumed_prefix resp input)
      network_out
      app_out);
    lemma_received_message_event_no_sent_delta msg;
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp.ST.response
      (ST.received_message_event msg)
      B.empty
      (ST.server_network_consumed_prefix resp input)
      network_out
      app_out
    )
#pop-options
