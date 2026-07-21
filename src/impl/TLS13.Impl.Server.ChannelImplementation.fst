module TLS13.Impl.Server.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
module CP = TLS13.Impl.Server.CanonicalProtocol
module CSL = TLS13.Spec.StateMachine.Log
module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module DS = TLS13.Impl.Server.Driver.State
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module SZ = FStar.SizeT
module ST = TLS13.Impl.Server.Types
module TChannel = TLS13.Impl.Channel
module WFSM = Common.WireFormatStateMachine

let lemma_server_end_to_end_app_log_consistent
  (st:CS.connection_state)
  : Lemma
      (requires ST.server_end_to_end_invariant st)
      (ensures CSL.connection_state_app_log_consistent st)
=
  ()

let lemma_channel_state_valid
  (d:DS.server_driver)
  (wire_received:B.bytes)
  (wire_sent:B.bytes)
  (pending:B.bytes)
  (app_log:CI.application_log B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (CP.server_protocol_implementation.CPI.pi_system
            (DS.server_driver_canonical d))
          st.CS.cs_wire_log.CL.raw_received
          st
          st.CS.cs_wire_log.CL.raw_sent
          Seq.empty /\
        Seq.equal wire_received
          (B.append st.CS.cs_wire_log.CL.raw_received pending) /\
        Seq.equal wire_sent st.CS.cs_wire_log.CL.raw_sent /\
        app_log == TChannel.application_log st)
      (ensures
        CI.channel_state_valid
          CP.server_protocol_implementation
          DS.server_driver_canonical
          TChannel.application_log
          d
          wire_received
          wire_sent
          pending
          app_log)
=
  Seq.lemma_eq_elim wire_sent st.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim
    wire_received
    (B.append st.CS.cs_wire_log.CL.raw_received pending);
  introduce
    exists (state:CS.connection_state) (consumed:B.bytes).
      Seq.equal wire_received (Seq.append consumed pending) /\
      WFSM.valid_byte_trace
        (CP.server_protocol_implementation.CPI.pi_system
          (DS.server_driver_canonical d))
        consumed
        state
        wire_sent
        Seq.empty /\
      app_log == TChannel.application_log state
  with st st.CS.cs_wire_log.CL.raw_received
  and ()

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
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent) **
      pure (
        Seq.equal
          (Ghost.reveal wire_received)
          (B.append st.CS.cs_wire_log.CL.raw_received (Ghost.reveal pending)) /\
        Seq.equal
          (Ghost.reveal wire_sent)
          st.CS.cs_wire_log.CL.raw_sent /\
        ST.server_connection_control_not_failed st /\
        (Ghost.reveal app_log) == TChannel.application_log st)
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st);
  unfold (CP.server_invariant
    (DS.server_driver_canonical d)
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_wire_log.CL.raw_sent
    st);
  with certificate_chain credential_identity. _;
  (Ghost.reveal
    (DS.server_driver_canonical d).CP.canonical_server_supported_profile)
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_wire_log.CL.raw_sent
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
    d st certificate_chain credential_identity
    (Ghost.reveal wire_received) (Ghost.reveal wire_sent))
}

(**
  Reopen a terminal (hard-failed) channel back to the lower-level connected
  ownership so the shared abort/cleanup path can dispose of it.  Terminal owns
  exactly the same concrete resources as the live invariant (server invariant,
  channel box, TCP channel, TCP-history witness, driver buffers), only without
  the not-failed / pending claims, so the conversion is total.
**)
ghost fn open_terminal_invariant
  (d:DS.server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_terminal
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
{
  unfold (DS.server_channel_terminal
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log));
  with st ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st);
  unfold (CP.server_invariant
    (DS.server_driver_canonical d)
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_wire_log.CL.raw_sent
    st);
  with certificate_chain credential_identity. _;
  (Ghost.reveal
    (DS.server_driver_canonical d).CP.canonical_server_supported_profile)
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_wire_log.CL.raw_sent
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
    d st certificate_chain credential_identity
    (Ghost.reveal wire_received) (Ghost.reveal wire_sent))
}

ghost fn open_io_channel
  (d:DS.server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns ch:Common.TCP.channel
  ensures
    Common.TCP.is_channel
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    DS.server_channel_io_frame
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st ch buffered buffered_len.
    assert (
      Common.TCP.is_channel
        ch
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent));
  fold (DS.server_channel_io_frame
    d
    ch
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  ch
}

ghost fn close_io_channel
  (d:DS.server_driver)
  (ch:Common.TCP.channel)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    Common.TCP.is_channel
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    DS.server_channel_io_frame
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
{
  unfold (DS.server_channel_io_frame
    d
    ch
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st buffered buffered_len. _;
  fold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

let lemma_channel_received_buffered_decomp
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        DS.server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures
        Seq.equal received
          (B.append st.CS.cs_wire_log.CL.raw_received buffered) /\
        Seq.equal sent st.CS.cs_wire_log.CL.raw_sent)
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        DS.server_driver_wire_logs_match_witness
          st received sent consumed buffered buffered_len) in
  assert (DS.server_driver_wire_logs_match_witness
    st received sent (Ghost.reveal consumed) buffered buffered_len);
  Seq.lemma_eq_elim st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed);
  Seq.lemma_eq_elim
    (B.append st.CS.cs_wire_log.CL.raw_received buffered) received

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
      (Ghost.reveal sent) **
    pure (ST.server_connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* pending.
      DS.server_channel_inv
        d
        (Ghost.reveal received)
        (Ghost.reveal sent)
        pending
        (TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.server_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal received)
    (Ghost.reveal sent));
  with ch buffered buffered_len.
    assert (DS.server_driver_buffers d buffered buffered_len);
  lemma_channel_received_buffered_decomp
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    buffered
    buffered_len;
  assert (pure (Seq.equal
    (Ghost.reveal received)
    (B.append (Ghost.reveal st).CS.cs_wire_log.CL.raw_received buffered)));
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
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st)));
  assert (pure (CP.server_config_matches_credentials
    (Ghost.reveal d.DS.server_driver_initial)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)));
  fold (CP.server_invariant
    (DS.server_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  fold (DS.server_channel_inv
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    buffered
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
      (Ghost.reveal sent) **
    pure (ST.server_connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* wire_received wire_sent pending app_log.
      DS.server_channel_inv d wire_received wire_sent pending app_log
{
  pack_connected_channel_invariant
    d st certificate_chain credential_identity received sent
}

ghost fn pack_connected_channel_terminal
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
    DS.server_channel_terminal
      d
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (TChannel.application_log (Ghost.reveal st))
{
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
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st)));
  assert (pure (CP.server_config_matches_credentials
    (Ghost.reveal d.DS.server_driver_initial)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)));
  fold (CP.server_invariant
    (DS.server_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  fold (DS.server_channel_terminal
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (TChannel.application_log (Ghost.reveal st)))
}

ghost fn pack_channel_snapshot
  (d:DS.server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  requires
    CP.server_snapshot
      (DS.server_driver_canonical d)
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
      (Ghost.reveal st) **
    DS.server_driver_io_history_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    pure (
      (Ghost.reveal app_log) ==
        TChannel.application_log (Ghost.reveal st))
  ensures
    DS.server_channel_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
{
  fold (DS.server_channel_snapshot
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log))
}

ghost fn channel_invariant_valid
  (d:DS.server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log) **
    pure (
      CI.channel_state_valid
        CP.server_protocol_implementation
        DS.server_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
        (Ghost.reveal pending)
        (Ghost.reveal app_log))
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st);
  CP.server_invariant_valid
    (DS.server_driver_canonical d)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide st);
  lemma_channel_state_valid
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st;
  fold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

ghost fn take_channel_snapshot
  (d:DS.server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log) **
    DS.server_channel_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
{
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st);
  CP.take_server_snapshot
    (DS.server_driver_canonical d)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide st);
  unfold (DS.server_driver_io_history
    d (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  MR.take_snapshot
    d.DS.server_driver_tcp_history
    (DS.server_driver_history
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  fold (DS.server_driver_io_history
    d (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  fold (DS.server_driver_io_history_snapshot
    d (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  pack_channel_snapshot d wire_received wire_sent app_log (Ghost.hide st);
  fold (DS.server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

ghost fn recall_channel_snapshot
  (d:DS.server_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  (new_pending:Ghost.erased B.bytes)
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
      (Ghost.reveal new_pending)
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
      (Ghost.reveal new_pending)
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
      old_st.CS.cs_wire_log.CL.raw_received
      old_st.CS.cs_wire_log.CL.raw_sent
      old_st);
  unfold (CP.server_snapshot
    (DS.server_driver_canonical d)
    old_st.CS.cs_wire_log.CL.raw_received
    old_st.CS.cs_wire_log.CL.raw_sent
    old_st);
  lemma_server_end_to_end_app_log_consistent old_st;
  assert (pure (CSL.connection_state_app_log_consistent old_st));
  fold (CP.server_snapshot
    (DS.server_driver_canonical d)
    old_st.CS.cs_wire_log.CL.raw_received
    old_st.CS.cs_wire_log.CL.raw_sent
    old_st);
  unfold (DS.server_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log));
  with new_st ch buffered buffered_len.
    assert (CP.server_invariant
      (DS.server_driver_canonical d)
      new_st.CS.cs_wire_log.CL.raw_received
      new_st.CS.cs_wire_log.CL.raw_sent
      new_st);
  unfold (CP.server_invariant
    (DS.server_driver_canonical d)
    new_st.CS.cs_wire_log.CL.raw_received
    new_st.CS.cs_wire_log.CL.raw_sent
    new_st);
  with current_certificate_chain current_credential_identity. _;
  lemma_server_end_to_end_app_log_consistent new_st;
  assert (pure (CSL.connection_state_app_log_consistent new_st));
  fold (CP.server_invariant
    (DS.server_driver_canonical d)
    new_st.CS.cs_wire_log.CL.raw_received
    new_st.CS.cs_wire_log.CL.raw_sent
    new_st);
  CP.recall_server_snapshot
    (DS.server_driver_canonical d)
    (Ghost.hide old_st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide old_st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide old_st)
    (Ghost.hide new_st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide new_st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide new_st);
  assert (pure (
    TChannel.event_log_extends
      old_st.CS.cs_event_log
      new_st.CS.cs_event_log));
  unfold (DS.server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
  unfold (DS.server_driver_io_history
    d (Ghost.reveal new_received) (Ghost.reveal new_sent));
  MR.recall_snapshot
    d.DS.server_driver_tcp_history
    #1.0R
    #(DS.server_driver_history
        (Ghost.reveal new_received) (Ghost.reveal new_sent))
    #(DS.server_driver_history
        (Ghost.reveal old_received) (Ghost.reveal old_sent));
  CI.lemma_io_history_preorder_extends
    (DS.server_driver_history
      (Ghost.reveal old_received) (Ghost.reveal old_sent))
    (DS.server_driver_history
      (Ghost.reveal new_received) (Ghost.reveal new_sent));
  assert (pure (CPI.histories_ahead
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)));
  fold (DS.server_driver_io_history
    d (Ghost.reveal new_received) (Ghost.reveal new_sent));
  fold (DS.server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
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
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log))
}

ghost fn recall_channel_snapshot_terminal
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
    DS.server_channel_terminal
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
    DS.server_channel_terminal
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_log) **
    pure (
      CPI.histories_ahead
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent))
{
  unfold (DS.server_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st. _;
  unfold (DS.server_channel_terminal
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log));
  with new_st ch buffered buffered_len. _;
  unfold (DS.server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
  unfold (DS.server_driver_io_history
    d (Ghost.reveal new_received) (Ghost.reveal new_sent));
  MR.recall_snapshot
    d.DS.server_driver_tcp_history
    #1.0R
    #(DS.server_driver_history
        (Ghost.reveal new_received) (Ghost.reveal new_sent))
    #(DS.server_driver_history
        (Ghost.reveal old_received) (Ghost.reveal old_sent));
  CI.lemma_io_history_preorder_extends
    (DS.server_driver_history
      (Ghost.reveal old_received) (Ghost.reveal old_sent))
    (DS.server_driver_history
      (Ghost.reveal new_received) (Ghost.reveal new_sent));
  assert (pure (CPI.histories_ahead
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)));
  fold (DS.server_driver_io_history
    d (Ghost.reveal new_received) (Ghost.reveal new_sent));
  fold (DS.server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
  fold (DS.server_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  fold (DS.server_channel_terminal
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log))
}
