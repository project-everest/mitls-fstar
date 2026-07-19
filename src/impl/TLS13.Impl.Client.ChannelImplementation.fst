module TLS13.Impl.Client.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CP = TLS13.Impl.Client.CanonicalProtocol
module CPI = Common.ProtocolImplementation
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.Spec.StateMachine.Log
module CT = TLS13.Impl.Client.Types
module DS = TLS13.Impl.Client.Driver.State
module ID = FStar.IndefiniteDescription
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module TChannel = TLS13.Impl.Channel

let message_of_bytes (bytes:B.bytes) : B.bytes = bytes

let send_succeeded (status:DS.driver_workflow_status) : bool =
  match status with
  | DS.DriverWorkflowOk -> true
  | _ -> false

let send_reusable (_status:DS.driver_workflow_status) : bool = true

let lemma_send_reusable (status:DS.driver_workflow_status)
  : Lemma (send_reusable status == true)
=
  ()

let lemma_channel_state_valid
  (d:DS.client_driver)
  (raw_received:B.bytes)
  (raw_sent:B.bytes)
  (app_log:CI.application_log B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        Common.WireFormatStateMachine.valid_byte_trace
          (CP.client_protocol_implementation.CPI.pi_system
            (DS.client_driver_canonical d))
          raw_received
          st
          raw_sent
          Seq.empty /\
        app_log == TChannel.application_log st)
      (ensures
        CI.channel_state_valid
          CP.client_protocol_implementation
          DS.client_driver_canonical
          TChannel.application_log
          d
          raw_received
          raw_sent
          app_log)
=
  assert (exists state residual_input.
    Common.WireFormatStateMachine.valid_byte_trace
      (CP.client_protocol_implementation.CPI.pi_system
        (DS.client_driver_canonical d))
      raw_received
      state
      raw_sent
      residual_input /\
    app_log == TChannel.application_log state)

let lemma_channel_snapshot_ahead
  (d:DS.client_driver)
  (old_received:B.bytes)
  (old_sent:B.bytes)
  (old_log:CI.application_log B.bytes)
  (new_received:B.bytes)
  (new_sent:B.bytes)
  (new_log:CI.application_log B.bytes)
  (old_st:CS.connection_state)
  (new_st:CS.connection_state)
  : Lemma
      (requires
        CPI.state_ahead
          (CP.client_protocol_implementation.CPI.pi_system
            (DS.client_driver_canonical d))
          old_st
          new_st /\
        CPI.histories_ahead
          old_received
          old_sent
          new_received
          new_sent /\
        CI.application_log_extends old_log new_log /\
        old_log == TChannel.application_log old_st /\
        new_log == TChannel.application_log new_st)
      (ensures
        CI.channel_snapshot_ahead
          CP.client_protocol_implementation
          DS.client_driver_canonical
          TChannel.application_log
          d
          old_received
          old_sent
          old_log
          new_received
          new_sent
          new_log)
=
  assert (exists old_state new_state.
    old_log == TChannel.application_log old_state /\
    new_log == TChannel.application_log new_state /\
    CPI.state_ahead
      (CP.client_protocol_implementation.CPI.pi_system
        (DS.client_driver_canonical d))
      old_state
      new_state)

let lemma_local_send_application_log
  (st0 st1:CS.connection_state)
  (resp:CT.client_response)
  (payload:B.bytes)
  (network_out app_out:B.bytes)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0
          st1
          resp
          CT.LocalSendApplicationData
          payload
          network_out
          app_out)
      (ensures
        TChannel.application_log st1 ==
          (if resp.CT.status == CT.StepOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  assert (CT.local_event_step_correct
    st0
    st1
    resp
    CT.LocalSendApplicationData
    payload
    network_out
    app_out);
  assert (CT.legal_handled_local_response
    st0
    st1
    resp
    CT.LocalSendApplicationData
    payload
    network_out
    app_out);
  if resp.CT.status == CT.StepOk then (
    assert (exists ev raw_sent raw_received.
      CT.legal_local_response
        st0
        st1
        resp
        CT.LocalSendApplicationData
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
          CT.legal_local_response
            st0
            st1
            resp
            CT.LocalSendApplicationData
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
          CT.legal_local_response
            st0
            st1
            resp
            CT.LocalSendApplicationData
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
          CT.legal_local_response
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    CT.lemma_legal_response_for_event_app_log_delta
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CSL.conn_event_app_sent_delta ev == [payload]);
    assert (CSL.conn_event_app_received_delta ev == []);
    assert (TChannel.application_log st1 ==
      CI.append_sent (TChannel.application_log st0) payload)
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    CT.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  ) else (
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    CT.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  )

let lemma_driver_send_application_log
  (st0 st1:CS.connection_state)
  (status:DS.driver_workflow_status)
  (payload sent0 sent1:B.bytes)
  : Lemma
      (requires
        DS.client_driver_send_correct
          st0 st1 status payload sent0 sent1)
      (ensures
        TChannel.application_log st1 ==
          (if status == DS.DriverWorkflowOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  if status == DS.DriverWorkflowPayloadTooLarge then ()
  else (
    assert (exists resp.
      DS.client_driver_local_write_correct
        st0
        st1
        resp
        CT.LocalSendApplicationData
        payload
        sent0
        sent1 /\
      DS.client_driver_send_status_correct status resp);
    let resp =
      ID.indefinite_description_ghost
        CT.client_response
        (fun resp ->
          DS.client_driver_local_write_correct
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            sent0
            sent1 /\
          DS.client_driver_send_status_correct status resp) in
    assert (exists network_out app_out.
      CT.local_event_end_to_end_correct
        st0
        st1
        resp
        CT.LocalSendApplicationData
        payload
        network_out
        app_out /\
      Seq.equal
        sent1
        (B.append sent0 (CT.response_network_out resp network_out)));
    let network_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun network_out -> exists app_out.
          CT.local_event_end_to_end_correct
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            network_out
            app_out /\
          Seq.equal
            sent1
            (B.append sent0 (CT.response_network_out resp network_out))) in
    let app_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun app_out ->
          CT.local_event_end_to_end_correct
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            network_out
            app_out /\
          Seq.equal
            sent1
            (B.append sent0 (CT.response_network_out resp network_out))) in
    lemma_local_send_application_log
      st0 st1 resp payload network_out app_out
  )

ghost fn pack_channel_invariant
  (d:DS.client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  (transport_received:Ghost.erased B.bytes)
  (transport_sent:Ghost.erased B.bytes)
  (ch:Ghost.erased Common.TCP.channel)
  (buffered:Ghost.erased B.bytes)
  (buffered_len:Ghost.erased FStar.SizeT.t)
  requires
    CP.client_invariant
      (DS.client_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal st) **
    TLS13.OpenSSL.is_auth_context d.DS.client_driver_auth **
    Pulse.Lib.Box.pts_to
      d.DS.client_driver_channel
      (Some (Ghost.reveal ch)) **
    Common.TCP.is_channel
      (Ghost.reveal ch)
      (Ghost.reveal transport_received)
      (Ghost.reveal transport_sent) **
    DS.client_driver_buffers
      d
      (Ghost.reveal buffered)
      (Ghost.reveal buffered_len) **
    pure (
      DS.client_driver_wire_logs_match
        (Ghost.reveal st)
        (Ghost.reveal transport_received)
        (Ghost.reveal transport_sent)
        (Ghost.reveal buffered)
        (Ghost.reveal buffered_len) /\
      (Ghost.reveal app_log) ==
        TChannel.application_log (Ghost.reveal st))
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  fold (DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn pack_channel_terminal
  (d:DS.client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  (transport_received:Ghost.erased B.bytes)
  (transport_sent:Ghost.erased B.bytes)
  (ch:Ghost.erased Common.TCP.channel)
  (buffered:Ghost.erased B.bytes)
  (buffered_len:Ghost.erased FStar.SizeT.t)
  requires
    CP.client_invariant
      (DS.client_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal st) **
    TLS13.OpenSSL.is_auth_context d.DS.client_driver_auth **
    Pulse.Lib.Box.pts_to
      d.DS.client_driver_channel
      (Some (Ghost.reveal ch)) **
    Common.TCP.is_channel
      (Ghost.reveal ch)
      (Ghost.reveal transport_received)
      (Ghost.reveal transport_sent) **
    DS.client_driver_buffers
      d
      (Ghost.reveal buffered)
      (Ghost.reveal buffered_len) **
    pure (
      DS.client_driver_wire_logs_match
        (Ghost.reveal st)
        (Ghost.reveal transport_received)
        (Ghost.reveal transport_sent)
        (Ghost.reveal buffered)
        (Ghost.reveal buffered_len) /\
      (Ghost.reveal app_log) ==
        TChannel.application_log (Ghost.reveal st))
  ensures
    DS.client_channel_terminal
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  fold (DS.client_channel_terminal
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn open_channel_invariant
  (d:DS.client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st transport_received transport_sent.
      DS.client_driver_connected
        d
        st
        transport_received
        transport_sent **
      pure (
        Seq.equal
          (Ghost.reveal raw_received)
          st.CS.cs_wire_log.CL.raw_received /\
        Seq.equal
          (Ghost.reveal raw_sent)
          st.CS.cs_wire_log.CL.raw_sent /\
        (Ghost.reveal app_log) == TChannel.application_log st)
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st transport_received transport_sent ch buffered buffered_len.
    assert (CP.client_invariant
      (DS.client_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      st);
  unfold (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    st);
  fold (DS.client_driver_canonical_progress d st);
  fold (DS.client_driver_connected
    d st transport_received transport_sent)
}

ghost fn pack_connected_after_send
  (d:DS.client_driver)
  (_status:DS.driver_workflow_status)
  (st:Ghost.erased CS.connection_state)
  (transport_received:Ghost.erased B.bytes)
  (transport_sent:Ghost.erased B.bytes)
  requires
    DS.client_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal transport_received)
      (Ghost.reveal transport_sent)
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
      (TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.client_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal transport_received)
    (Ghost.reveal transport_sent));
  with ch buffered buffered_len.
    assert (
      Pulse.Lib.Box.pts_to d.DS.client_driver_channel (Some ch) **
      Common.TCP.is_channel
        ch
        (Ghost.reveal transport_received)
        (Ghost.reveal transport_sent) **
      DS.client_driver_buffers d buffered buffered_len **
      pure (DS.client_driver_wire_logs_match
        (Ghost.reveal st)
        (Ghost.reveal transport_received)
        (Ghost.reveal transport_sent)
        buffered
        buffered_len));
  unfold (DS.client_driver_canonical_progress d (Ghost.reveal st));
  fold (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  assert (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  assert (pure (
    DS.client_driver_wire_logs_match
      (Ghost.reveal st)
      (Ghost.reveal transport_received)
      (Ghost.reveal transport_sent)
      buffered
      buffered_len /\
    TChannel.application_log (Ghost.reveal st) ==
      TChannel.application_log (Ghost.reveal st)));
  fold (DS.client_channel_inv
    d
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (TChannel.application_log (Ghost.reveal st)))
}

ghost fn pack_channel_snapshot
  (d:DS.client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  requires
    CP.client_snapshot
      (DS.client_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal st) **
    pure (
      (Ghost.reveal app_log) ==
        TChannel.application_log (Ghost.reveal st))
  ensures
    DS.client_channel_snapshot
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  fold (DS.client_channel_snapshot
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn channel_invariant_valid
  (d:DS.client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log) **
    pure (
      CI.channel_state_valid
        CP.client_protocol_implementation
        DS.client_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal raw_received)
        (Ghost.reveal raw_sent)
        (Ghost.reveal app_log))
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st transport_received transport_sent ch buffered buffered_len.
    assert (CP.client_invariant
      (DS.client_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      st);
  CP.client_invariant_valid
    (DS.client_driver_canonical d)
    raw_received
    raw_sent
    (Ghost.hide st);
  lemma_channel_state_valid
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log)
    st;
  assert (pure (CI.channel_state_valid
    CP.client_protocol_implementation
    DS.client_driver_canonical
    TChannel.application_log
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log)));
  fold (DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn take_channel_snapshot
  (d:DS.client_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log) **
    DS.client_channel_snapshot
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st transport_received transport_sent ch buffered buffered_len.
    assert (CP.client_invariant
      (DS.client_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      st);
  CP.take_client_snapshot
    (DS.client_driver_canonical d)
    raw_received
    raw_sent
    (Ghost.hide st);
  pack_channel_snapshot
    d
    raw_received
    raw_sent
    app_log
    (Ghost.hide st);
  pack_channel_invariant
    d
    raw_received
    raw_sent
    app_log
    (Ghost.hide st)
    (Ghost.hide transport_received)
    (Ghost.hide transport_sent)
    (Ghost.hide ch)
    (Ghost.hide buffered)
    (Ghost.hide buffered_len)
}

ghost fn recall_channel_snapshot
  (d:DS.client_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  (new_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.client_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_log)
  ensures
    DS.client_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.client_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_log) **
    pure (
      CI.channel_snapshot_ahead
        CP.client_protocol_implementation
        DS.client_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal old_log)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent)
        (Ghost.reveal new_log))
{
  unfold (DS.client_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st.
    assert (CP.client_snapshot
      (DS.client_driver_canonical d)
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      old_st);
  unfold (CP.client_snapshot
    (DS.client_driver_canonical d)
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    old_st);
  assert (pure (CSL.connection_state_app_log_consistent old_st));
  fold (CP.client_snapshot
    (DS.client_driver_canonical d)
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    old_st);
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log));
  with new_st transport_received transport_sent ch buffered buffered_len.
    assert (CP.client_invariant
      (DS.client_driver_canonical d)
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      new_st);
  unfold (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    new_st);
  assert (pure (CSL.connection_state_app_log_consistent new_st));
  fold (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    new_st);
  CP.recall_client_snapshot
    (DS.client_driver_canonical d)
    old_received
    old_sent
    (Ghost.hide old_st)
    new_received
    new_sent
    (Ghost.hide new_st);
  assert (pure (
    CSL.connection_state_app_log_consistent old_st /\
    CSL.connection_state_app_log_consistent new_st /\
    TChannel.event_log_extends
      old_st.CS.cs_event_log
      new_st.CS.cs_event_log));
  TChannel.lemma_application_log_extends_from_event_logs old_st new_st;
  lemma_channel_snapshot_ahead
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log)
    old_st
    new_st;
  assert (pure (CI.channel_snapshot_ahead
    CP.client_protocol_implementation
    DS.client_driver_canonical
    TChannel.application_log
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log)));
  pack_channel_snapshot
    d
    old_received
    old_sent
    old_log
    (Ghost.hide old_st);
  pack_channel_invariant
    d
    new_received
    new_sent
    new_log
    (Ghost.hide new_st)
    (Ghost.hide transport_received)
    (Ghost.hide transport_sent)
    (Ghost.hide ch)
    (Ghost.hide buffered)
    (Ghost.hide buffered_len)
}
