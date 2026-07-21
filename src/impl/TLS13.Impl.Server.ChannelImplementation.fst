module TLS13.Impl.Server.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
module CP = TLS13.Impl.Server.CanonicalProtocol
module CSL = TLS13.Spec.StateMachine.Log
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module TChannel = TLS13.Impl.Channel

let lemma_server_end_to_end_app_log_consistent
  (st:CS.connection_state)
  : Lemma
      (requires ST.server_end_to_end_invariant st)
      (ensures CSL.connection_state_app_log_consistent st)
=
  ()

let lemma_channel_state_valid
  (d:DS.server_driver)
  (raw_received:B.bytes)
  (raw_sent:B.bytes)
  (app_log:CI.application_log B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        Common.WireFormatStateMachine.valid_byte_trace
          (CP.server_protocol_implementation.CPI.pi_system
            (DS.server_driver_canonical d))
          raw_received
          st
          raw_sent
          Seq.empty /\
        app_log == TChannel.application_log st)
      (ensures
        CI.channel_state_valid
          CP.server_protocol_implementation
          DS.server_driver_canonical
          TChannel.application_log
          d
          raw_received
          raw_sent
          app_log)
=
  assert (exists state residual_input.
    Common.WireFormatStateMachine.valid_byte_trace
      (CP.server_protocol_implementation.CPI.pi_system
        (DS.server_driver_canonical d))
      raw_received
      state
      raw_sent
      residual_input /\
    app_log == TChannel.application_log state)

let lemma_channel_snapshot_ahead
  (d:DS.server_driver)
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
          (CP.server_protocol_implementation.CPI.pi_system
            (DS.server_driver_canonical d))
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
          CP.server_protocol_implementation
          DS.server_driver_canonical
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
      (CP.server_protocol_implementation.CPI.pi_system
        (DS.server_driver_canonical d))
      old_state
      new_state)

ghost fn open_channel_invariant
  (d:DS.server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity received sent.
      DS.server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        received
        sent **
      pure (
        Seq.equal
          (Ghost.reveal raw_received)
          st.CS.cs_wire_log.TLS13.ConnectionLog.raw_received /\
        Seq.equal
          (Ghost.reveal raw_sent)
          st.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent /\
        (Ghost.reveal app_log) == TChannel.application_log st)
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st received sent ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      st);
  unfold (CP.server_invariant
    (DS.server_driver_canonical d)
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    st);
  with certificate_chain credential_identity. _;
  (Ghost.reveal
    (DS.server_driver_canonical d).CP.canonical_server_supported_profile)
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    st
    certificate_chain
    credential_identity;
  DS.lemma_supported_profile_selection_driver st credential_identity;
  fold (DS.server_driver_canonical_progress d st);
  assert (pure (ST.server_end_to_end_invariant st));
  assert (pure (DS.server_driver_config_matches_credentials
    st certificate_chain credential_identity));
  assert (pure (DS.server_driver_supported_profile_selection
    st credential_identity));
  fold (DS.server_driver_connected
    d st certificate_chain credential_identity received sent)
}

ghost fn open_io_channel
  (d:DS.server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  returns ch:Common.TCP.channel
  ensures
    exists* received sent.
      Common.TCP.is_channel ch received sent **
      DS.server_channel_io_frame
        d
        ch
        (Ghost.reveal raw_received)
        (Ghost.reveal raw_sent)
        received
        sent
        (Ghost.reveal app_log) **
      pure (
        CI.channel_io_history_matches
          (Ghost.reveal raw_received)
          (Ghost.reveal raw_sent)
          received
          sent)
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st received sent ch buffered buffered_len.
    assert (
      Common.TCP.is_channel ch received sent **
      pure (
        CI.channel_io_history_matches
          (Ghost.reveal raw_received)
          (Ghost.reveal raw_sent)
          received
          sent));
  fold (DS.server_channel_io_frame
    d
    ch
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    received
    sent
    (Ghost.reveal app_log));
  ch
}

ghost fn close_io_channel
  (d:DS.server_driver)
  (ch:Common.TCP.channel)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    Common.TCP.is_channel
      ch
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    DS.server_channel_io_frame
      d
      ch
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal app_log) **
    pure (
      CI.channel_io_history_matches
        (Ghost.reveal raw_received)
        (Ghost.reveal raw_sent)
        (Ghost.reveal received)
        (Ghost.reveal sent))
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  unfold (DS.server_channel_io_frame
    d
    ch
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal app_log));
  with st buffered buffered_len. _;
  fold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn pack_connected_channel_invariant
  (d:DS.server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent)
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_received
      (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
      (TChannel.application_log (Ghost.reveal st))
{
  DS.expose_server_driver_io_history
    d st certificate_chain credential_identity received sent;
  unfold (DS.server_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal received)
    (Ghost.reveal sent));
  with ch buffered buffered_len.
    assert (DS.server_driver_canonical_progress d (Ghost.reveal st));
  unfold (DS.server_driver_canonical_progress d (Ghost.reveal st));
  Pulse.Lib.MonotonicGhostRef.recall_snapshot
    d.DS.server_driver_progress
    #1.0R
    #(Ghost.reveal st)
    #(Ghost.reveal d.DS.server_driver_initial);
  CP.lemma_server_progress_state_ahead
    (Ghost.reveal d.DS.server_driver_initial)
    (Ghost.reveal d.DS.server_driver_initial)
    (Ghost.reveal st);
  assert (pure (CP.server_invariant_pure
    (Ghost.reveal d.DS.server_driver_initial)
    (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_received
    (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
    (Ghost.reveal st)));
  assert (pure (CP.server_config_matches_credentials
    (Ghost.reveal d.DS.server_driver_initial)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)));
  fold (CP.server_invariant
    (DS.server_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_received
    (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
    (Ghost.reveal st));
  fold (DS.server_channel_inv
    d
    (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_received
    (Ghost.reveal st).CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
    (TChannel.application_log (Ghost.reveal st)))
}

ghost fn pack_connected_channel
  (d:DS.server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent)
  ensures
    exists* raw_received raw_sent app_log.
      DS.server_channel_inv d raw_received raw_sent app_log
{
  pack_connected_channel_invariant
    d st certificate_chain credential_identity received sent
}

ghost fn pack_channel_snapshot
  (d:DS.server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  requires
    CP.server_snapshot
      (DS.server_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal st) **
    pure (
      (Ghost.reveal app_log) ==
        TChannel.application_log (Ghost.reveal st))
  ensures
    DS.server_channel_snapshot
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  fold (DS.server_channel_snapshot
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn channel_invariant_valid
  (d:DS.server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log) **
    pure (
      CI.channel_state_valid
        CP.server_protocol_implementation
        DS.server_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal raw_received)
        (Ghost.reveal raw_sent)
        (Ghost.reveal app_log))
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st received sent ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      st);
  CP.server_invariant_valid
    (DS.server_driver_canonical d)
    raw_received
    raw_sent
    (Ghost.hide st);
  lemma_channel_state_valid
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log)
    st;
  fold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn take_channel_snapshot
  (d:DS.server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log) **
    DS.server_channel_snapshot
      d
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      (Ghost.reveal app_log)
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log));
  with st received sent ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      (Ghost.reveal raw_received)
      (Ghost.reveal raw_sent)
      st);
  CP.take_server_snapshot
    (DS.server_driver_canonical d)
    raw_received
    raw_sent
    (Ghost.hide st);
  pack_channel_snapshot d raw_received raw_sent app_log (Ghost.hide st);
  fold (DS.server_channel_inv
    d
    (Ghost.reveal raw_received)
    (Ghost.reveal raw_sent)
    (Ghost.reveal app_log))
}

ghost fn recall_channel_snapshot
  (d:DS.server_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  (new_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.server_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_log)
  ensures
    DS.server_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.server_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_log) **
    pure (
      CI.channel_snapshot_ahead
        CP.server_protocol_implementation
        DS.server_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal old_log)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent)
        (Ghost.reveal new_log))
{
  unfold (DS.server_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st.
    assert (CP.server_snapshot
      (DS.server_driver_canonical d)
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      old_st);
  unfold (CP.server_snapshot
    (DS.server_driver_canonical d)
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    old_st);
  lemma_server_end_to_end_app_log_consistent old_st;
  assert (pure (CSL.connection_state_app_log_consistent old_st));
  fold (CP.server_snapshot
    (DS.server_driver_canonical d)
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    old_st);
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log));
  with new_st received sent ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      new_st);
  unfold (CP.server_invariant
    (DS.server_driver_canonical d)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    new_st);
  with current_certificate_chain current_credential_identity. _;
  lemma_server_end_to_end_app_log_consistent new_st;
  assert (pure (CSL.connection_state_app_log_consistent new_st));
  fold (CP.server_invariant
    (DS.server_driver_canonical d)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    new_st);
  CP.recall_server_snapshot
    (DS.server_driver_canonical d)
    old_received
    old_sent
    (Ghost.hide old_st)
    new_received
    new_sent
    (Ghost.hide new_st);
  assert (pure (
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
  pack_channel_snapshot
    d old_received old_sent old_log (Ghost.hide old_st);
  fold (DS.server_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log))
}
