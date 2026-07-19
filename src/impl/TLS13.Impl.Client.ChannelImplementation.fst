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
module DS = TLS13.Impl.Client.Driver.State
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module TChannel = TLS13.Impl.Channel

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
        TChannel.application_log (Ghost.reveal st) /\
      DS.client_driver_application_ready (Ghost.reveal st))
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
  CP.recall_client_snapshot
    (DS.client_driver_canonical d)
    old_received
    old_sent
    (Ghost.hide old_st)
    new_received
    new_sent
    (Ghost.hide new_st);
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
