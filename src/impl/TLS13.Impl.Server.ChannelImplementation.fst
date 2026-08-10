module TLS13.Impl.Server.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Class.Duplicable

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
module CP = TLS13.Impl.Server.CanonicalProtocol
module CSL = TLS13.Spec.StateMachine.Log
module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module DS = TLS13.Impl.Server.Driver.State
module BT = Common.BufferedTCP
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
  (d:DS.top_server_driver)
  (wire_received:B.bytes)
  (wire_sent:B.bytes)
  (pending:B.bytes)
  (app_log:CI.application_log B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (CP.server_protocol_implementation.CPI.pi_system
            (DS.top_server_driver_canonical d))
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
          DS.top_server_driver_canonical
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
          (DS.top_server_driver_canonical d))
        consumed
        state
        wire_sent
        Seq.empty /\
      app_log == TChannel.application_log state
  with st st.CS.cs_wire_log.CL.raw_received
  and ()

let lemma_channel_snapshot_ahead
  (d:DS.top_server_driver)
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
            (DS.top_server_driver_canonical d))
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
          DS.top_server_driver_canonical
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
        (DS.top_server_driver_canonical d))
      old_state
      new_state)

(**
  Package a past connection state and TCP history as a duplicable channel
  snapshot.
**)
ghost fn pack_channel_snapshot
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  requires
    CP.server_snapshot
      (DS.top_server_driver_canonical d)
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
      (Ghost.reveal st) **
    DS.top_server_driver_io_history_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    pure (
      (Ghost.reveal app_log) ==
        TChannel.application_log (Ghost.reveal st))
  ensures
    DS.top_server_channel_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
{
  fold (DS.top_server_channel_snapshot
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log))
}

(**
  The channel invariant entails the generic [CI.channel_state_valid]: the
  concrete ownership implies that the wire histories admit a valid byte trace
  for the server's protocol implementation, with [pending] the unconsumed
  suffix.  This is [CI.ci_invariant_valid].
**)
ghost fn channel_invariant_valid
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
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log) **
    pure (
      CI.channel_state_valid
        CP.server_protocol_implementation
        DS.top_server_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
        (Ghost.reveal pending)
        (Ghost.reveal app_log))
{
  unfold (DS.top_server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st certificate_chain credential_identity channel model committed buffered_len.
    unfold (DS.top_server_channel_terminal_indexed
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
      st certificate_chain credential_identity
      channel model committed buffered_len);
  CP.server_invariant_valid
    (DS.top_server_driver_canonical d)
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
  fold (DS.top_server_channel_terminal_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log)
    st certificate_chain credential_identity
    channel model committed buffered_len);
  fold (DS.top_server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

(**
  [CI.ci_take_snapshot]: record the current channel state duplicably, keeping
  full ownership.
**)
ghost fn take_channel_snapshot
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
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log) **
    DS.top_server_channel_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
{
  unfold (DS.top_server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st certificate_chain credential_identity channel model committed buffered_len.
    unfold (DS.top_server_channel_terminal_indexed
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
      st certificate_chain credential_identity
      channel model committed buffered_len);
  CP.take_server_snapshot
    (DS.top_server_driver_canonical d)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide st);
  MR.take_snapshot
    d.DS.top_server_driver_tcp_history
    (DS.server_driver_history
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  fold (DS.top_server_driver_io_history_snapshot
    d (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  pack_channel_snapshot d wire_received wire_sent app_log (Ghost.hide st);
  fold (DS.top_server_channel_terminal_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log)
    st certificate_chain credential_identity
    channel model committed buffered_len);
  fold (DS.top_server_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

(**
  Recall a snapshot against a *lower-level* connected bundle.  This is the
  workhorse behind the [CPI.histories_ahead] conjunct of
  [CI.send_transition] / [CI.receive_transition]: the TCP-history witness is
  monotonic under [IO.bytes_extends], so a snapshot taken before an operation
  proves the wire histories only grew.
**)
ghost fn recall_tcp_history
  (d:DS.top_server_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  requires
    DS.top_server_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
  ensures
    DS.top_server_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent) **
    pure (
      CPI.histories_ahead
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent))
{
  unfold (DS.top_server_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st. _;
  unfold (DS.top_server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
  dup (MR.snapshot
    d.DS.top_server_driver_tcp_history
    (DS.server_driver_history
      (Ghost.reveal old_received) (Ghost.reveal old_sent))) ();
  unfold (DS.top_server_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent));
  with channel model committed buffered_len. _;
  unfold (DS.top_server_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    channel model committed buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal new_received)
    committed
    (Ghost.reveal new_sent));
  MR.recall_snapshot
    d.DS.top_server_driver_tcp_history
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
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (BT.pending model)
    buffered_len
    model
    (Ghost.reveal new_received)
    committed
    (Ghost.reveal new_sent));
  fold (DS.top_server_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    channel model committed buffered_len);
  fold (DS.top_server_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent));
  fold (DS.top_server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
  pack_channel_snapshot
    d old_received old_sent old_log (Ghost.hide old_st)
}

(**
  [CI.ci_recall_snapshot]: a snapshot taken earlier is *ahead-of* the current
  channel state -- wire histories extend, application log extends, and the
  protocol states are related by [CPI.state_ahead].
**)
ghost fn recall_channel_snapshot
  (d:DS.top_server_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  (new_pending:Ghost.erased B.bytes)
  (new_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.top_server_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_pending)
      (Ghost.reveal new_log)
  ensures
    DS.top_server_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.top_server_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_pending)
      (Ghost.reveal new_log) **
    pure (
      CI.channel_snapshot_ahead
        CP.server_protocol_implementation
        DS.top_server_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal old_log)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent)
        (Ghost.reveal new_log))
{
  unfold (DS.top_server_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st. _;
  unfold (CP.server_snapshot
    (DS.top_server_driver_canonical d)
    old_st.CS.cs_wire_log.CL.raw_received
    old_st.CS.cs_wire_log.CL.raw_sent
    old_st);
  lemma_server_end_to_end_app_log_consistent old_st;
  fold (CP.server_snapshot
    (DS.top_server_driver_canonical d)
    old_st.CS.cs_wire_log.CL.raw_received
    old_st.CS.cs_wire_log.CL.raw_sent
    old_st);
  unfold (DS.top_server_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log));
  with new_st certificate_chain credential_identity channel model committed buffered_len.
    unfold (DS.top_server_channel_terminal_indexed
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_log)
      new_st certificate_chain credential_identity
      channel model committed buffered_len);
  unfold (CP.server_invariant
    (DS.top_server_driver_canonical d)
    new_st.CS.cs_wire_log.CL.raw_received
    new_st.CS.cs_wire_log.CL.raw_sent
    new_st);
  with current_certificate_chain current_credential_identity. _;
  lemma_server_end_to_end_app_log_consistent new_st;
  fold (CP.server_invariant
    (DS.top_server_driver_canonical d)
    new_st.CS.cs_wire_log.CL.raw_received
    new_st.CS.cs_wire_log.CL.raw_sent
    new_st);
  CP.recall_server_snapshot
    (DS.top_server_driver_canonical d)
    (Ghost.hide old_st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide old_st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide old_st)
    (Ghost.hide new_st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide new_st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide new_st);
  unfold (DS.top_server_driver_io_history_snapshot
    d (Ghost.reveal old_received) (Ghost.reveal old_sent));
  MR.recall_snapshot
    d.DS.top_server_driver_tcp_history
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
  fold (DS.top_server_driver_io_history_snapshot
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
  fold (DS.top_server_channel_terminal_indexed
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log)
    new_st certificate_chain credential_identity
    channel model committed buffered_len);
  fold (DS.top_server_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log))
}
