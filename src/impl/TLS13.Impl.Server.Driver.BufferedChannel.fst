module TLS13.Impl.Server.Driver.BufferedChannel

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CP = TLS13.Impl.Server.CanonicalProtocol
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module TChannel = TLS13.Impl.Channel

ghost fn open_terminal_indexed
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (channel:Ghost.erased BT.t)
  (model:Ghost.erased BT.phys_buffer)
  (committed:Ghost.erased B.bytes)
  (buffered_len:Ghost.erased FStar.SizeT.t)
  requires
    DS.top_server_channel_terminal_indexed
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal channel)
      (Ghost.reveal model)
      (Ghost.reveal committed)
      (Ghost.reveal buffered_len)
  ensures
    exists* actual_certificate_chain actual_credential_identity.
      DS.top_server_driver_connected_indexed
        d
        (Ghost.reveal st)
        actual_certificate_chain
        actual_credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
        (Ghost.reveal channel)
        (Ghost.reveal model)
        (Ghost.reveal committed)
        (Ghost.reveal buffered_len) **
      pure (
        (Ghost.reveal app_log) ==
          TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.top_server_channel_terminal_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log)
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal channel)
    (Ghost.reveal model)
    (Ghost.reveal committed)
    (Ghost.reveal buffered_len));
  unfold (CP.server_invariant
    (DS.top_server_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  with actual_certificate_chain actual_credential_identity. _;
  (Ghost.reveal
    (DS.top_server_driver_canonical d)
      .CP.canonical_server_supported_profile)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st)
    actual_certificate_chain
    actual_credential_identity;
  DS.lemma_supported_profile_selection_driver
    (Ghost.reveal st)
    actual_credential_identity;
  fold (DS.buffered_driver_canonical_progress
    (DS.top_server_as_buffered d (Ghost.reveal channel))
    (Ghost.reveal st));
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d (Ghost.reveal channel))
    (Ghost.reveal st)
    actual_certificate_chain
    actual_credential_identity
    (BT.pending (Ghost.reveal model))
    (Ghost.reveal buffered_len)
    (Ghost.reveal model)
    (Ghost.reveal wire_received)
    (Ghost.reveal committed)
    (Ghost.reveal wire_sent));
  fold (DS.top_server_driver_connected_indexed
    d
    (Ghost.reveal st)
    actual_certificate_chain
    actual_credential_identity
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal channel)
    (Ghost.reveal model)
    (Ghost.reveal committed)
    (Ghost.reveal buffered_len))
}

ghost fn open_channel_invariant
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent) **
      pure (
        ST.server_connection_control_not_failed st /\
        (Ghost.reveal app_log) == TChannel.application_log st)
{
  unfold (DS.top_server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st certificate_chain credential_identity channel model committed buffered_len.
    assert (DS.top_server_channel_terminal_indexed
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
      st
      certificate_chain
      credential_identity
      channel
      model
      committed
      buffered_len);
  open_terminal_indexed
    d wire_received wire_sent app_log
    (Ghost.hide st)
    (Ghost.hide certificate_chain)
    (Ghost.hide credential_identity)
    (Ghost.hide channel)
    (Ghost.hide model)
    (Ghost.hide committed)
    (Ghost.hide buffered_len);
  with actual_certificate_chain actual_credential_identity.
    assert (DS.top_server_driver_connected_indexed
      d
      st
      actual_certificate_chain
      actual_credential_identity
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      channel
      model
      committed
      buffered_len);
  fold (DS.top_server_driver_connected
    d
    st
    actual_certificate_chain
    actual_credential_identity
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent))
}

ghost fn open_terminal_invariant
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_terminal
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
{
  unfold (DS.top_server_channel_terminal
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log));
  with st certificate_chain credential_identity channel model committed buffered_len.
    assert (DS.top_server_channel_terminal_indexed
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
      st
      certificate_chain
      credential_identity
      channel
      model
      committed
      buffered_len);
  open_terminal_indexed
    d wire_received wire_sent app_log
    (Ghost.hide st)
    (Ghost.hide certificate_chain)
    (Ghost.hide credential_identity)
    (Ghost.hide channel)
    (Ghost.hide model)
    (Ghost.hide committed)
    (Ghost.hide buffered_len);
  with actual_certificate_chain actual_credential_identity.
    assert (DS.top_server_driver_connected_indexed
      d
      st
      actual_certificate_chain
      actual_credential_identity
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      channel
      model
      committed
      buffered_len);
  fold (DS.top_server_driver_connected
    d
    st
    actual_certificate_chain
    actual_credential_identity
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent))
}

let lemma_channel_received_buffered_decomp
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (committed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:FStar.SizeT.t)
  : Lemma
      (requires
        DS.server_driver_wire_logs_match_witness
          st received sent committed buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures
        Seq.equal received
          (B.append st.CS.cs_wire_log.CL.raw_received buffered) /\
        Seq.equal sent st.CS.cs_wire_log.CL.raw_sent)
=
  Seq.lemma_eq_elim st.CS.cs_wire_log.CL.raw_received committed;
  Seq.lemma_eq_elim
    (B.append st.CS.cs_wire_log.CL.raw_received buffered)
    received

ghost fn pack_connected_channel_invariant
  (d:DS.top_server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    pure (ST.server_connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* pending.
      DS.top_server_channel_inv
        d
        (Ghost.reveal received)
        (Ghost.reveal sent)
        pending
        (TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.top_server_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal received)
    (Ghost.reveal sent));
  with channel model committed buffered_len.
    assert (DS.top_server_driver_connected_indexed
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      channel
      model
      committed
      buffered_len);
  unfold (DS.top_server_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    channel
    model
    committed
    buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal received)
    committed
    (Ghost.reveal sent));
  lemma_channel_received_buffered_decomp
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    committed
    (BT.pending model)
    buffered_len;
  unfold (DS.buffered_driver_canonical_progress
    (DS.top_server_as_buffered d channel)
    (Ghost.reveal st));
  MR.recall_snapshot
    d.DS.top_server_driver_progress
    #1.0R
    #(Ghost.reveal st)
    #(Ghost.reveal d.DS.top_server_driver_initial);
  CP.lemma_server_progress_state_ahead
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal st);
  assert (pure (CP.server_invariant_pure
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st)));
  assert (pure (CP.server_config_matches_credentials
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)));
  fold (CP.server_invariant
    (DS.top_server_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  fold (DS.top_server_channel_terminal_indexed
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (TChannel.application_log (Ghost.reveal st))
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    channel
    model
    committed
    buffered_len);
  fold (DS.top_server_channel_inv
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (BT.pending model)
    (TChannel.application_log (Ghost.reveal st)))
}

ghost fn pack_connected_channel
  (d:DS.top_server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    pure (ST.server_connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* wire_received wire_sent pending app_log.
      DS.top_server_channel_inv
        d wire_received wire_sent pending app_log
{
  pack_connected_channel_invariant
    d st certificate_chain credential_identity received sent
}

ghost fn pack_connected_channel_terminal
  (d:DS.top_server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent)
  ensures
    DS.top_server_channel_terminal
      d
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.top_server_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal received)
    (Ghost.reveal sent));
  with channel model committed buffered_len.
    assert (DS.top_server_driver_connected_indexed
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      channel
      model
      committed
      buffered_len);
  unfold (DS.top_server_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    channel
    model
    committed
    buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal received)
    committed
    (Ghost.reveal sent));
  unfold (DS.buffered_driver_canonical_progress
    (DS.top_server_as_buffered d channel)
    (Ghost.reveal st));
  MR.recall_snapshot
    d.DS.top_server_driver_progress
    #1.0R
    #(Ghost.reveal st)
    #(Ghost.reveal d.DS.top_server_driver_initial);
  CP.lemma_server_progress_state_ahead
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal st);
  assert (pure (CP.server_invariant_pure
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st)));
  assert (pure (CP.server_config_matches_credentials
    (Ghost.reveal d.DS.top_server_driver_initial)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)));
  fold (CP.server_invariant
    (DS.top_server_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  fold (DS.top_server_channel_terminal_indexed
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (TChannel.application_log (Ghost.reveal st))
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    channel
    model
    committed
    buffered_len);
  fold (DS.top_server_channel_terminal
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (TChannel.application_log (Ghost.reveal st)))
}
