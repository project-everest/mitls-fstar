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
