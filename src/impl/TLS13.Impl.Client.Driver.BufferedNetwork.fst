module TLS13.Impl.Client.Driver.BufferedNetwork

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BS = Common.BufferedStream
module BT = Common.BufferedTCP
module C = TLS13.Impl.Client
module CL = TLS13.ConnectionLog
module CP = TLS13.Impl.Client.CanonicalProtocol
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec
module D = TLS13.Impl.Client.Drain
module DL = TLS13.Impl.Client.DrainLoop
module DP = TLS13.Impl.Client.DrainProgress
module V = Pulse.Lib.Vec
module DS = TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.State

noeq type endpoint_state = {
  endpoint_connection: CS.connection_state;
  endpoint_network_out: B.bytes;
  endpoint_app_out: B.bytes;
}

noeq type endpoint = {
  endpoint_driver: top_buffered_driver;
  endpoint_network_out_buffer: array U8.t;
  endpoint_network_out_capacity: SZ.t;
  endpoint_app_out_buffer: array U8.t;
  endpoint_app_out_capacity: SZ.t;
}

let decide
  (result:buffered_network_result)
  : BS.classification unit CT.client_status =
  let buffer_resp = result.buffered_network_read.network_read_buffer_resp in
  match buffer_resp.CT.response.CT.status with
  | CT.NeedMoreInput ->
    BS.NeedMore
  | CT.StepOk ->
    BS.Yield buffer_resp.CT.consumed_len ()
  | status ->
    BS.Reject status

let needs_more
  (_:endpoint_state)
  (pending:B.bytes)
  : prop =
  W.record_prefix_incomplete pending

let lemma_yield_transition
  (k:SZ.t)
  (committed committed':B.bytes)
  (model model':BT.phys_buffer)
  : Lemma
      (requires
        0 < SZ.v k /\
        SZ.v k <= Seq.length (BT.pending model) /\
        Seq.equal committed' (BT.committed_after committed model (SZ.v k)) /\
        model' == BT.compact model (SZ.v k))
      (ensures
        BS.process_transition
          (BS.Yield k () <: BS.classification unit CT.client_status)
          committed
          committed'
          model
          model')
=
  ()

let lemma_needmore_transition
  (decision:BS.classification unit CT.client_status)
  (committed committed':B.bytes)
  (model model':BT.phys_buffer)
  : Lemma
      (requires
        BS.process_transition
          decision
          committed
          committed'
          model
          model' /\
        decision == BS.NeedMore)
      (ensures
        Seq.equal committed' committed /\
        model' == model)
=
  ()

let result_valid
  (_:endpoint)
  (before:endpoint_state)
  (result:buffered_network_result)
  (after:endpoint_state)
  : prop =
  let buffer_resp =
    result.buffered_network_read.network_read_buffer_resp in
  D.drained_network_bytes_end_to_end_correct
    before.endpoint_connection
    after.endpoint_connection
    buffer_resp
    (Ghost.reveal result.buffered_network_read.network_read_prefix)
    before.endpoint_network_out
    after.endpoint_network_out
    before.endpoint_app_out
    after.endpoint_app_out /\
  (SZ.v buffer_resp.CT.response.CT.app_out_len > 0 ==>
   buffer_resp.CT.response.CT.status == CT.StepOk)

let lemma_result_valid_preserves
  (e:endpoint)
  (before:endpoint_state)
  (result:buffered_network_result)
  (after:endpoint_state)
  : Lemma
      (requires result_valid e before result after)
      (ensures
        after.endpoint_connection.CS.cs_model.CS.model_config ==
          before.endpoint_connection.CS.cs_model.CS.model_config /\
        (CT.client_end_to_end_invariant before.endpoint_connection ==>
         CT.client_end_to_end_invariant after.endpoint_connection))
=
  let response =
    result.buffered_network_read.network_read_buffer_resp in
  let prefix =
    Ghost.reveal result.buffered_network_read.network_read_prefix in
  D.lemma_drained_network_preserves_config
    before.endpoint_connection
    after.endpoint_connection
    response
    prefix
    before.endpoint_network_out
    after.endpoint_network_out
    before.endpoint_app_out
    after.endpoint_app_out;
  if CT.client_end_to_end_invariant before.endpoint_connection
  then
    D.lemma_drained_network_preserves_invariant
      before.endpoint_connection
      after.endpoint_connection
      response
      prefix
      before.endpoint_network_out
      after.endpoint_network_out
      before.endpoint_app_out
      after.endpoint_app_out

noextract
let owns
  (e:endpoint)
  (st:endpoint_state)
  (received committed:B.bytes)
  (model:BT.phys_buffer)
  : slprop =
  exists* pending_len sent.
    buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      st.endpoint_connection
      (BT.pending model)
      pending_len
      model
      received
      committed
      sent **
    O.is_auth_context e.endpoint_driver.top_buffered_driver_auth **
    pts_to e.endpoint_network_out_buffer st.endpoint_network_out **
    pts_to e.endpoint_app_out_buffer st.endpoint_app_out **
    pure (
      SZ.v pending_len == B.length (BT.pending model) /\
      B.length st.endpoint_network_out ==
        SZ.v e.endpoint_network_out_capacity /\
      B.length st.endpoint_app_out ==
        SZ.v e.endpoint_app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <=
        SZ.v e.endpoint_app_out_capacity)

noextract
let terminal
  (e:endpoint)
  (st:endpoint_state)
  (received:B.bytes)
  : slprop =
  exists* committed model.
    owns e st received committed model

noextract
let buffer_full
  (e:endpoint)
  (st:endpoint_state)
  (received:B.bytes)
  : slprop =
  terminal e st received **
  pure False

noextract
let read_auth
  (e:endpoint)
  (st:endpoint_state)
  (received committed:B.bytes)
  (model:BT.phys_buffer)
  : slprop =
  owns e st received committed model **
  pure (needs_more st (BT.pending model))

ghost
fn owns_wf
  (e:endpoint)
  (st:Ghost.erased endpoint_state)
  (received:Ghost.erased B.bytes)
  (committed:Ghost.erased B.bytes)
  (model:Ghost.erased BT.phys_buffer)
  requires
    owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model)
  ensures
    owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model) **
    pure (
      BT.buffer_wf (Ghost.reveal model) /\
      BT.received_split
        (Ghost.reveal received)
        (Ghost.reveal committed)
        (Ghost.reveal model))
{
  unfold (owns
    e
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    (Ghost.reveal model));
  with pending_len sent.
    assert (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending (Ghost.reveal model))
      pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  BT.recall_model e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
  fold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  fold (owns
    e
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    (Ghost.reveal model))
}

fn process
  (e:endpoint)
  (st:Ghost.erased endpoint_state)
  (received:Ghost.erased B.bytes)
  (committed:Ghost.erased B.bytes)
  (model:Ghost.erased BT.phys_buffer)
  requires
    owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model)
  returns outcome:BS.process_outcome unit CT.client_status buffered_network_result
  ensures
    BS.process_post
      decide
      needs_more
      result_valid
      owns
      terminal
      buffer_full
      read_auth
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model)
      outcome
{
  unfold (owns
    e
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    (Ghost.reveal model));
  with pending_len sent.
    assert (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending (Ghost.reveal model))
      pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  BT.recall_model
    e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
  // Expose client_end_to_end_invariant, which process_coalesced_network_bytes
  // demands; the fact survives the re-fold in Pulse's logical context.
  unfold (buffered_driver_canonical_progress
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection);
  fold (buffered_driver_canonical_progress
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection);
  let view =
    BT.borrow_pending
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
  rewrite
    (C.connection_exactly
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
      (Ghost.reveal st).endpoint_connection)
    as
    (CR.connection_exactly
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
      (Ghost.reveal st).endpoint_connection);
  let buffer_resp =
    C.process_coalesced_network_bytes
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
      (BT.view_data view)
      (BT.view_length view)
      e.endpoint_network_out_buffer
      e.endpoint_network_out_capacity
      e.endpoint_app_out_buffer
      e.endpoint_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      CR.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1 **
      pts_to (BT.view_data view) (BT.pending (Ghost.reveal model)) **
      pts_to e.endpoint_network_out_buffer network_out_bytes **
      pts_to e.endpoint_app_out_buffer app_out_bytes);
  rewrite
    (CR.connection_exactly
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
      st1)
    as
    (C.connection_exactly
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
      st1);
  assert (pure (CT.coalesced_network_bytes_end_to_end_correct
    (Ghost.reveal st).endpoint_connection
    st1
    buffer_resp
    (BT.pending (Ghost.reveal model))
    (Ghost.reveal st).endpoint_network_out
    network_out_bytes
    (Ghost.reveal st).endpoint_app_out
    app_out_bytes));
  CP.lemma_client_coalesced_network_bytes_step_correct
    (Ghost.reveal st).endpoint_connection
    st1
    buffer_resp
    (BT.pending (Ghost.reveal model))
    (Ghost.reveal st).endpoint_network_out
    network_out_bytes
    (Ghost.reveal st).endpoint_app_out
    app_out_bytes;
  lemma_network_bytes_wire_lengths
    (Ghost.reveal st).endpoint_connection
    st1
    buffer_resp
    (BT.pending (Ghost.reveal model))
    (Ghost.reveal st).endpoint_network_out
    network_out_bytes
    (Ghost.reveal st).endpoint_app_out
    app_out_bytes;
  assert (pure (
    SZ.v buffer_resp.CT.consumed_len <=
      B.length (BT.pending (Ghost.reveal model))));
  let read_result = {
    network_read_len = BT.view_length view;
    network_read_buffer_resp = buffer_resp;
    network_read_written = buffer_resp.CT.response.CT.network_out_len;
    network_read_prefix = Ghost.hide (BT.pending (Ghost.reveal model));
  };
  BT.release_pending
    e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
    view;
  let need_more =
    buffer_resp.CT.response.CT.status = CT.NeedMoreInput;
  if need_more {
    assert (pure (buffer_resp.CT.consumed_len == 0sz));
    assert (pure (CT.response_stuttered
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp.CT.response
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes));
    assert (pure (st1 == (Ghost.reveal st).endpoint_connection));
    assert (pure (
      Seq.equal network_out_bytes (Ghost.reveal st).endpoint_network_out));
    assert (pure (
      Seq.equal app_out_bytes (Ghost.reveal st).endpoint_app_out));
    rewrite
      (C.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1)
      as
      (C.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        (Ghost.reveal st).endpoint_connection);
    rewrite
      (pts_to e.endpoint_network_out_buffer network_out_bytes)
      as
      (pts_to
        e.endpoint_network_out_buffer
        (Ghost.reveal st).endpoint_network_out);
    rewrite
      (pts_to e.endpoint_app_out_buffer app_out_bytes)
      as
      (pts_to
        e.endpoint_app_out_buffer
        (Ghost.reveal st).endpoint_app_out);
    W.lemma_record_prefix_incomplete_bound (BT.pending (Ghost.reveal model));
    assert (pure (Seq.length (BT.pending (Ghost.reveal model)) < 5 + 16640));
    assert (pure (BT.capacity (Ghost.reveal model) == 65535));
    assert (pure (Seq.length (BT.pending (Ghost.reveal model)) <
      BT.capacity (Ghost.reveal model)));
    assert (pure (BT.can_read (Ghost.reveal model)));
    D.lemma_coalesced_implies_drained_network
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes;
    let result = {
      buffered_network_read = read_result;
      buffered_network_new_len = read_result.network_read_len;
    };
    fold (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending (Ghost.reveal model))
      pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
    fold (owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model));
    fold (read_auth
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model));
    fold
      (BS.process_post
        decide
        needs_more
        result_valid
        owns
        terminal
        buffer_full
        read_auth
        e
        (Ghost.reveal st)
        (Ghost.reveal received)
        (Ghost.reveal committed)
        (Ghost.reveal model)
        (BS.Processed result BS.NeedMore));
    BS.Processed result BS.NeedMore
  } else {
    let remaining =
      BT.commit_prefix
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        buffer_resp.CT.consumed_len;
    with model'.
      assert (
        BT.is_buffered
          e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
          model'
          (Ghost.reveal received)
          (BT.committed_after
            (Ghost.reveal committed)
            (Ghost.reveal model)
            (SZ.v buffer_resp.CT.consumed_len))
          sent);
    let written =
      BT.write
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        e.endpoint_network_out_buffer
        buffer_resp.CT.response.CT.network_out_len;
    assert (pure (
      written == buffer_resp.CT.response.CT.network_out_len));
    tcp_history_note_write
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_tcp_history
      received
      (Ghost.hide sent)
      (Ghost.hide
        (CT.response_network_out buffer_resp.CT.response network_out_bytes));
    let sent' =
      Ghost.hide
        (B.append sent
          (CT.response_network_out buffer_resp.CT.response network_out_bytes));
    assert (pure (Seq.equal
      (Ghost.reveal sent')
      (B.append sent
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty))));
    rewrite
      (BT.is_buffered
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.CT.consumed_len))
        (B.append sent
          (if SZ.v written <= B.length network_out_bytes
           then Seq.slice network_out_bytes 0 (SZ.v written)
           else B.empty)))
      as
      (BT.is_buffered
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.CT.consumed_len))
        (Ghost.reveal sent'));
    rewrite
      (MR.pts_to
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_tcp_history
        #1.0R
        (wire_history
          (Ghost.reveal received)
          (B.append sent
            (CT.response_network_out
              buffer_resp.CT.response
              network_out_bytes))))
      as
      (MR.pts_to
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_tcp_history
        #1.0R
        (wire_history
          (Ghost.reveal received)
          (Ghost.reveal sent')));
    lemma_network_bytes_logged_received_accounted
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes
      (Ghost.reveal committed);
    lemma_coalesced_logged_received_exact_when_nonfailed
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes
      (Ghost.reveal received)
      sent
      (Ghost.reveal committed)
      (BT.pending (Ghost.reveal model))
      pending_len;
    BT.recall_model
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
    let new_committed =
      Ghost.hide
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.CT.consumed_len));
    rewrite
      (BT.is_buffered
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.CT.consumed_len))
        (Ghost.reveal sent'))
      as
      (BT.is_buffered
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        (Ghost.reveal sent'));
    assert (pure (client_driver_wire_logs_match_witness
      st1
      (Ghost.reveal received)
      (Ghost.reveal sent')
      (Ghost.reveal new_committed)
      (BT.pending model')
      remaining));
    unfold (buffered_driver_canonical_progress
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection);
    CP.lemma_client_coalesced_network_progress
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes;
    CP.lemma_client_coalesced_preserves_config
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes;
    // A protected record can carry several coalesced handshake messages, and
    // the receive primitive applies only the head one.  Unlike the engine,
    // which drains across successive polls, this driver owns the socket and so
    // must run the internal drain to completion here.
    let empty_payload = V.alloc 0uy 0sz;
    V.to_array_pts_to empty_payload;
    rewrite
      (C.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1)
      as
      (CR.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1);
    let drain_quiescent =
      DL.drain_pending
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        (V.vec_to_array empty_payload);
    with st1d. assert (
      CR.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1d);
    rewrite
      (CR.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1d)
      as
      (C.connection_exactly
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_client
        st1d);
    V.to_vec_pts_to empty_payload;
    V.free empty_payload;
    D.lemma_drained_facts st1 st1d;
    DP.lemma_drained_progress st1 st1d;
    D.lemma_drained_nonfailed_previous_imp st1 st1d;
    D.lemma_drained_network_intro
      (Ghost.reveal st).endpoint_connection
      st1
      st1d
      buffer_resp
      (BT.pending (Ghost.reveal model))
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      (Ghost.reveal st).endpoint_app_out
      app_out_bytes;
    MR.update
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_progress
      st1d;
    assert (pure (CT.client_end_to_end_invariant st1d));
    assert (pure (
      st1d.CS.cs_model.CS.model_config ==
        (Ghost.reveal
          e.endpoint_driver.top_buffered_driver_core.buffered_driver_initial)
          .CS.cs_model.CS.model_config));
    assert (pure (
      CP.client_initial_wire_logs_empty
        (Ghost.reveal
          e.endpoint_driver.top_buffered_driver_core.buffered_driver_initial)));
    fold (buffered_driver_canonical_progress
      e.endpoint_driver.top_buffered_driver_core
      st1d);
    fold (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      st1d
      (BT.pending model')
      remaining
      model'
      (Ghost.reveal received)
      (Ghost.reveal new_committed)
      (Ghost.reveal sent'));
    let st' : Ghost.erased endpoint_state = Ghost.hide {
      endpoint_connection = st1d;
      endpoint_network_out = network_out_bytes;
      endpoint_app_out = app_out_bytes;
    };
    rewrite
      (buffered_driver_indexed
        e.endpoint_driver.top_buffered_driver_core
        st1d
        (BT.pending model')
        remaining
        model'
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        (Ghost.reveal sent'))
      as
      (buffered_driver_indexed
        e.endpoint_driver.top_buffered_driver_core
        (Ghost.reveal st').endpoint_connection
        (BT.pending model')
        remaining
        model'
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        (Ghost.reveal sent'));
    rewrite
      (pts_to e.endpoint_network_out_buffer network_out_bytes)
      as
      (pts_to
        e.endpoint_network_out_buffer
        (Ghost.reveal st').endpoint_network_out);
    rewrite
      (pts_to e.endpoint_app_out_buffer app_out_bytes)
      as
      (pts_to
        e.endpoint_app_out_buffer
        (Ghost.reveal st').endpoint_app_out);
    let result = {
      buffered_network_read = {
        network_read_len = read_result.network_read_len;
        network_read_buffer_resp = buffer_resp;
        network_read_written = written;
        network_read_prefix = read_result.network_read_prefix;
      };
      buffered_network_new_len = remaining;
    };
    let step_ok =
      buffer_resp.CT.response.CT.status = CT.StepOk;
    if step_ok {
      let decision : BS.classification unit CT.client_status =
        BS.Yield buffer_resp.CT.consumed_len ();
      assert (pure (0 < SZ.v buffer_resp.CT.consumed_len));
      assert (pure (
        decide result == decision));
      assert (pure (
        result_valid e (Ghost.reveal st) result (Ghost.reveal st')));
      assert (pure (
        model' ==
          BT.compact
            (Ghost.reveal model)
            (SZ.v buffer_resp.CT.consumed_len)));
      Seq.lemma_eq_intro
        (Ghost.reveal new_committed)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.CT.consumed_len));
      assert (pure (
        0 < SZ.v buffer_resp.CT.consumed_len /\
        SZ.v buffer_resp.CT.consumed_len <=
          Seq.length (BT.pending (Ghost.reveal model)) /\
        Seq.equal
          (Ghost.reveal new_committed)
          (BT.committed_after
            (Ghost.reveal committed)
            (Ghost.reveal model)
            (SZ.v buffer_resp.CT.consumed_len)) /\
        model' ==
          BT.compact
            (Ghost.reveal model)
            (SZ.v buffer_resp.CT.consumed_len)));
      lemma_yield_transition
        buffer_resp.CT.consumed_len
        (Ghost.reveal committed)
        (Ghost.reveal new_committed)
        (Ghost.reveal model)
        model';
      assert (pure (
        BS.process_transition
          decision
          (Ghost.reveal committed)
          (Ghost.reveal new_committed)
          (Ghost.reveal model)
          model'));
      fold (owns
        e
        (Ghost.reveal st')
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        model');
      assert (pure (
        decision == decide result));
      assert (pure (
        result_valid e (Ghost.reveal st) result (Ghost.reveal st')));
      assert (pure (
        decision == decide result /\
        result_valid e (Ghost.reveal st) result (Ghost.reveal st') /\
        BS.process_transition
          decision
          (Ghost.reveal committed)
          (Ghost.reveal new_committed)
          (Ghost.reveal model)
          model'));
      fold
        (BS.process_post
          decide
          needs_more
          result_valid
          owns
          terminal
          buffer_full
          read_auth
          e
          (Ghost.reveal st)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (BS.Processed
            result
            (BS.Yield buffer_resp.CT.consumed_len ())));
      BS.Processed
        result
        (BS.Yield buffer_resp.CT.consumed_len ())
    } else {
      fold (owns
        e
        (Ghost.reveal st')
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        model');
      fold (terminal e (Ghost.reveal st') (Ghost.reveal received));
      fold
        (BS.process_post
          decide
          needs_more
          result_valid
          owns
          terminal
          buffer_full
          read_auth
          e
          (Ghost.reveal st)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (BS.Processed
            result
            (BS.Reject buffer_resp.CT.response.CT.status)));
      BS.Processed
        result
        (BS.Reject buffer_resp.CT.response.CT.status)
    }
  }
}

fn read
  (e:endpoint)
  (st:Ghost.erased endpoint_state)
  (received:Ghost.erased B.bytes)
  (committed:Ghost.erased B.bytes)
  (model:Ghost.erased BT.phys_buffer)
  requires
    read_auth
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model) **
    pure (
      BT.buffer_wf (Ghost.reveal model) /\
      BT.can_read (Ghost.reveal model) /\
      needs_more
        (Ghost.reveal st)
        (BT.pending (Ghost.reveal model)))
  ensures
    exists* received' model'.
      owns
        e
        (Ghost.reveal st)
        received'
        (Ghost.reveal committed)
        model' **
      pure (
        BS.read_delivers
          (Ghost.reveal received)
          received'
          (Ghost.reveal model)
          model')
{
  unfold (read_auth
    e
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    (Ghost.reveal model));
  unfold (owns
    e
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    (Ghost.reveal model));
  with pending_len sent.
    assert (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending (Ghost.reveal model))
      pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  let _ =
    BT.read_more
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
  with chunk model'.
    assert (
      BT.is_buffered
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
        model'
        (Seq.append (Ghost.reveal received) chunk)
        (Ghost.reveal committed)
        sent **
      MR.pts_to
        e.endpoint_driver.top_buffered_driver_core.buffered_driver_tcp_history
        #1.0R
        (wire_history (Ghost.reveal received) sent));
  tcp_history_note_read
    e.endpoint_driver.top_buffered_driver_core.buffered_driver_tcp_history
    received
    (Ghost.hide sent)
    (Ghost.hide chunk);
  let new_pending_len =
    BT.pending_length
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
  Seq.append_assoc
    (Ghost.reveal committed)
    (BT.pending (Ghost.reveal model))
    chunk;
  assert (pure (client_driver_wire_logs_match_witness
    (Ghost.reveal st).endpoint_connection
    (Seq.append (Ghost.reveal received) chunk)
    sent
    (Ghost.reveal committed)
    (BT.pending model')
    new_pending_len));
  fold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending model')
    new_pending_len
    model'
    (Seq.append (Ghost.reveal received) chunk)
    (Ghost.reveal committed)
    sent);
  fold (owns
    e
    (Ghost.reveal st)
    (Seq.append (Ghost.reveal received) chunk)
    (Ghost.reveal committed)
    model');
  BT.lemma_pending_length (Ghost.reveal model);
  BT.lemma_pending_length model';
  Seq.lemma_len_append (BT.pending (Ghost.reveal model)) chunk;
  assert (pure (
    BS.read_delivers
      (Ghost.reveal received)
      (Seq.append (Ghost.reveal received) chunk)
      (Ghost.reveal model)
      model'))
}

fn process_local_event
  (d:top_buffered_driver)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires
    top_buffered_driver_exactly d 'st0 'buffered 'buffered_len **
    pts_to payload 'payload_bytes **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'payload_bytes == SZ.v payload_len /\
      B.length 'old_network_out == SZ.v network_out_len /\
      B.length 'old_app_out == SZ.v app_out_len /\
      CT.local_input_wf 'st0 kind (Ghost.reveal 'payload_bytes))
  returns result:local_write_result
  ensures
    exists* st1 network_out_bytes app_out_bytes.
      top_buffered_driver_exactly d st1 'buffered 'buffered_len **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length network_out_bytes == SZ.v network_out_len /\
        B.length app_out_bytes == SZ.v app_out_len /\
        CT.local_event_end_to_end_correct
          'st0
          st1
          result.local_write_resp
          kind
          (Ghost.reveal 'payload_bytes)
          network_out_bytes
          app_out_bytes /\
        result.local_write_written ==
          result.local_write_resp.CT.network_out_len /\
        (result.local_write_resp.CT.status == CT.StepOk ==>
          SZ.v result.local_write_written <=
            SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (top_buffered_driver_exactly
    d
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len));
  unfold (buffered_driver_exactly
    d.top_buffered_driver_core
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len));
  with model received committed sent.
    assert (buffered_driver_indexed
      d.top_buffered_driver_core
      'st0
      (Ghost.reveal 'buffered)
      (Ghost.reveal 'buffered_len)
      model
      received
      committed
      sent);
  unfold (buffered_driver_indexed
    d.top_buffered_driver_core
    'st0
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len)
    model
    received
    committed
    sent);
  unfold (buffered_driver_canonical_progress
    d.top_buffered_driver_core
    'st0);
  rewrite
    (C.connection_exactly
      d.top_buffered_driver_core.buffered_driver_client
      'st0)
    as
    (CR.connection_exactly
      d.top_buffered_driver_core.buffered_driver_client
      'st0);
  let resp =
    C.process_local_event
      d.top_buffered_driver_core.buffered_driver_client
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (
      CR.connection_exactly
        d.top_buffered_driver_core.buffered_driver_client
        st1 **
      pts_to payload 'payload_bytes **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes);
  rewrite
    (CR.connection_exactly
      d.top_buffered_driver_core.buffered_driver_client
      st1)
    as
    (C.connection_exactly
      d.top_buffered_driver_core.buffered_driver_client
      st1);
  assert (pure (CT.local_event_end_to_end_correct
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes));
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  DS.lemma_local_event_wire_lengths
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (CT.response_wf resp network_out_bytes app_out_bytes));
  assert (pure (SZ.v resp.CT.network_out_len <= B.length network_out_bytes));
  let written =
    BT.write
      d.top_buffered_driver_core.buffered_driver_channel
      network_out
      resp.CT.network_out_len;
  tcp_history_note_write
    d.top_buffered_driver_core.buffered_driver_tcp_history
    (Ghost.hide received)
    (Ghost.hide sent)
    (Ghost.hide
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  assert (pure (written == resp.CT.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  Seq.lemma_len_append sent (Seq.slice network_out_bytes 0 (SZ.v written));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (CT.response_network_out resp network_out_bytes)));
  assert (pure (Seq.equal sent 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim sent 'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (CT.response_network_out resp network_out_bytes))));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received;
  DS.lemma_local_event_received_exact_when_nonfailed
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes
    received
    sent
    committed
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len);
  assert (pure (client_driver_wire_logs_match_witness
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    committed
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len)));
  CP.lemma_client_local_progress
    'st0
    st1
    {
      CTypes.client_local_kind = kind;
      CTypes.client_local_payload = Ghost.reveal 'payload_bytes;
    }
    resp
    network_out_bytes
    app_out_bytes;
  MR.update
    d.top_buffered_driver_core.buffered_driver_progress
    st1;
  assert (pure (CT.client_end_to_end_invariant st1));
  fold (buffered_driver_canonical_progress
    d.top_buffered_driver_core
    st1);
  fold (buffered_driver_indexed
    d.top_buffered_driver_core
    st1
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len)
    model
    received
    committed
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty)));
  fold (buffered_driver_exactly
    d.top_buffered_driver_core
    st1
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len));
  fold (top_buffered_driver_exactly
    d
    st1
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'buffered_len));
  {
    local_write_resp = resp;
    local_write_written = written;
  }
}

noextract
let client_endpoint
  : BS.buffered_stream_endpoint
      endpoint
      endpoint_state
      unit
      CT.client_status
      buffered_network_result
  = {
  BS.bse_decide = decide;
  BS.bse_needs_more = needs_more;
  BS.bse_result_valid = result_valid;
  BS.bse_owns = owns;
  BS.bse_terminal = terminal;
  BS.bse_buffer_full = buffer_full;
  BS.bse_read_auth = read_auth;
  BS.bse_owns_wf = owns_wf;
  BS.bse_process = process;
  BS.bse_read = read;
}

let make_endpoint
  (d:top_buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  : endpoint =
  {
    endpoint_driver = d;
    endpoint_network_out_buffer = network_out;
    endpoint_network_out_capacity = network_out_capacity;
    endpoint_app_out_buffer = app_out;
    endpoint_app_out_capacity = app_out_capacity;
  }

noextract
let make_endpoint_state
  (st:CS.connection_state)
  (network_out app_out:B.bytes)
  : endpoint_state =
  {
    endpoint_connection = st;
    endpoint_network_out = network_out;
    endpoint_app_out = app_out;
  }

noextract
let public_drive_post
  (d:top_buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (initial_state:CS.connection_state)
  (initial_network_out initial_app_out:B.bytes)
  (outcome:BS.drive_outcome unit CT.client_status buffered_network_result)
  : slprop =
  BS.drive_post
    client_endpoint
    (make_endpoint
      d
      network_out
      network_out_capacity
      app_out
      app_out_capacity)
    (make_endpoint_state
      initial_state
      initial_network_out
      initial_app_out)
    outcome

inline_for_extraction
fn drive_until_conclusive
  (d:top_buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    top_buffered_driver_exactly d 'st0 'buffered buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns outcome:BS.drive_outcome unit CT.client_status buffered_network_result
  ensures
    public_drive_post
      d
      network_out
      network_out_capacity
      app_out
      app_out_capacity
      'st0
      'old_network_out
      'old_app_out
      outcome **
    pure (SZ.v (BS.drive_fuel_left outcome) <= SZ.v fuel)
{
  let e =
    make_endpoint
      d
      network_out
      network_out_capacity
      app_out
      app_out_capacity;
  let st : Ghost.erased endpoint_state =
    Ghost.hide (make_endpoint_state 'st0 'old_network_out 'old_app_out);
  unfold (top_buffered_driver_exactly d 'st0 'buffered buffered_len);
  unfold (buffered_driver_exactly
    d.top_buffered_driver_core
    'st0
    'buffered
    buffered_len);
  with model received committed sent.
    assert (buffered_driver_indexed
      d.top_buffered_driver_core
      'st0
      'buffered
      buffered_len
      model
      received
      committed
      sent);
  unfold (buffered_driver_indexed
    d.top_buffered_driver_core
    'st0
    'buffered
    buffered_len
    model
    received
    committed
    sent);
  assert (pure ((Ghost.reveal st).endpoint_connection == 'st0));
  Seq.lemma_eq_elim (BT.pending model) 'buffered;
  rewrite
    (C.connection_exactly
      d.top_buffered_driver_core.buffered_driver_client
      'st0)
    as
    (C.connection_exactly
      d.top_buffered_driver_core.buffered_driver_client
      (Ghost.reveal st).endpoint_connection);
  rewrite
    (buffered_driver_canonical_progress
      d.top_buffered_driver_core
      'st0)
    as
    (buffered_driver_canonical_progress
      d.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection);
  fold (buffered_driver_indexed
    d.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending model)
    buffered_len
    model
    received
    committed
    sent);
  assert (pure (e.endpoint_driver == d));
  assert (pure (e.endpoint_network_out_buffer == network_out));
  assert (pure (e.endpoint_app_out_buffer == app_out));
  assert (pure (
    (Ghost.reveal st).endpoint_network_out == 'old_network_out));
  assert (pure (
    (Ghost.reveal st).endpoint_app_out == 'old_app_out));
  rewrite
    (buffered_driver_indexed
      d.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending model)
      buffered_len
      model
      received
      committed
      sent)
    as
    (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending model)
      buffered_len
      model
      received
      committed
      sent);
  rewrite
    (O.is_auth_context d.top_buffered_driver_auth)
    as
    (O.is_auth_context e.endpoint_driver.top_buffered_driver_auth);
  rewrite
    (pts_to network_out 'old_network_out)
    as
    (pts_to
      e.endpoint_network_out_buffer
      (Ghost.reveal st).endpoint_network_out);
  rewrite
    (pts_to app_out 'old_app_out)
    as
    (pts_to
      e.endpoint_app_out_buffer
      (Ghost.reveal st).endpoint_app_out);
  fold (owns
    e
    (Ghost.reveal st)
    received
    committed
    model);
  rewrite
    (owns
      e
      (Ghost.reveal st)
      received
      committed
      model)
    as
    (client_endpoint.BS.bse_owns
      e
      (Ghost.reveal st)
      received
      committed
      model);
  let outcome =
    BS.drive_until_conclusive
      client_endpoint
      process
      read
      e
      st
      (Ghost.hide received)
      (Ghost.hide committed)
      (Ghost.hide model)
      fuel;
  rewrite
    (BS.drive_post
      client_endpoint
      e
      (Ghost.reveal st)
      outcome)
    as
    (BS.drive_post
      client_endpoint
      (make_endpoint
        d
        network_out
        network_out_capacity
        app_out
        app_out_capacity)
      (make_endpoint_state 'st0 'old_network_out 'old_app_out)
      outcome);
  fold (public_drive_post
    d
    network_out
    network_out_capacity
    app_out
    app_out_capacity
    'st0
    'old_network_out
    'old_app_out
    outcome);
  outcome
}

inline_for_extraction
fn finish_owns
  (e:endpoint)
  (#st:erased endpoint_state)
  (#received #committed:erased B.bytes)
  (#model:erased BT.phys_buffer)
  requires
    owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model)
  returns pending_len:SZ.t
  ensures
    top_buffered_driver_exactly
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (BT.pending (Ghost.reveal model))
      pending_len **
    pts_to
      e.endpoint_network_out_buffer
      (Ghost.reveal st).endpoint_network_out **
    pts_to
      e.endpoint_app_out_buffer
      (Ghost.reveal st).endpoint_app_out **
    pure (
      B.length (BT.pending (Ghost.reveal model)) == SZ.v pending_len /\
      B.length (Ghost.reveal st).endpoint_network_out ==
        SZ.v e.endpoint_network_out_capacity /\
      B.length (Ghost.reveal st).endpoint_app_out ==
        SZ.v e.endpoint_app_out_capacity)
{
  unfold (owns
    e
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    (Ghost.reveal model));
  with old_pending_len sent.
    assert (buffered_driver_indexed
      e.endpoint_driver.top_buffered_driver_core
      (Ghost.reveal st).endpoint_connection
      (BT.pending (Ghost.reveal model))
      old_pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    old_pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  let view =
    BT.borrow_pending
      e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel;
  let pending_len = BT.view_length view;
  BT.release_pending
    e.endpoint_driver.top_buffered_driver_core.buffered_driver_channel
    view;
  assert (pure (SZ.v pending_len ==
    B.length (BT.pending (Ghost.reveal model))));
  assert (pure (pending_len == old_pending_len));
  fold (buffered_driver_indexed
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  fold (buffered_driver_exactly
    e.endpoint_driver.top_buffered_driver_core
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len);
  fold (top_buffered_driver_exactly
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (BT.pending (Ghost.reveal model))
    pending_len);
  pending_len
}

inline_for_extraction
fn drive
  (d:top_buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    top_buffered_driver_exactly d 'st0 'buffered buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns result:completed_drive
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      top_buffered_driver_exactly
        d
        st1
        buffered_after
        result.completed_drive_pending_len **
      pts_to network_out network_out_bytes **
      pts_to app_out app_out_bytes **
      pure (
        B.length buffered_after == SZ.v result.completed_drive_pending_len /\
        B.length network_out_bytes == SZ.v network_out_capacity /\
        B.length app_out_bytes == SZ.v app_out_capacity /\
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config /\
        (CT.client_end_to_end_invariant 'st0 ==>
         CT.client_end_to_end_invariant st1) /\
        completed_drive_correct
          'st0
          st1
          'old_network_out
          network_out_bytes
          'old_app_out
          app_out_bytes
          result)
{
  let outcome =
    drive_until_conclusive
      d
      network_out
      network_out_capacity
      app_out
      app_out_capacity
      buffered_len
      fuel;
  unfold (public_drive_post
    d
    network_out
    network_out_capacity
    app_out
    app_out_capacity
    'st0
    'old_network_out
    'old_app_out
    outcome);
  unfold (BS.drive_post
    client_endpoint
    (make_endpoint
      d
      network_out
      network_out_capacity
      app_out
      app_out_capacity)
    (make_endpoint_state 'st0 'old_network_out 'old_app_out)
    outcome);
  match outcome {
    BS.DriveExhausted -> {
      with st1 received committed model.
        assert (
          client_endpoint.BS.bse_owns
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            st1 received committed model **
          pure (st1 ==
            make_endpoint_state 'st0 'old_network_out 'old_app_out));
      rewrite
        (client_endpoint.BS.bse_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model)
        as
        (owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model);
      let pending_len =
        finish_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity);
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveProgress network consumed fuel_left -> {
      with st1 received committed model.
        assert (
          client_endpoint.BS.bse_owns
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            st1 received committed model **
          pure (result_valid
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            (make_endpoint_state 'st0 'old_network_out 'old_app_out)
            network
            st1));
      lemma_result_valid_preserves
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        (make_endpoint_state 'st0 'old_network_out 'old_app_out)
        network
        st1;
      rewrite
        (client_endpoint.BS.bse_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model)
        as
        (owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model);
      let pending_len =
        finish_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity);
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveYield network consumed output fuel_left -> {
      with st1 received committed model.
        assert (
          client_endpoint.BS.bse_owns
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            st1 received committed model **
          pure (result_valid
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            (make_endpoint_state 'st0 'old_network_out 'old_app_out)
            network
            st1));
      lemma_result_valid_preserves
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        (make_endpoint_state 'st0 'old_network_out 'old_app_out)
        network
        st1;
      rewrite
        (client_endpoint.BS.bse_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model)
        as
        (owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model);
      let pending_len =
        finish_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity);
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveReject network error fuel_left -> {
      with st1 received.
        assert (
          client_endpoint.BS.bse_terminal
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            st1 received **
          pure (result_valid
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            (make_endpoint_state 'st0 'old_network_out 'old_app_out)
            network
            st1));
      lemma_result_valid_preserves
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        (make_endpoint_state 'st0 'old_network_out 'old_app_out)
        network
        st1;
      rewrite
        (client_endpoint.BS.bse_terminal
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received)
        as
        (terminal
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received);
      unfold (terminal
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        st1 received);
      with committed model.
        assert (owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model);
      let pending_len =
        finish_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity);
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveBufferFull network fuel_left -> {
      with st1 received.
        assert (
          client_endpoint.BS.bse_buffer_full
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            st1 received **
          pure (result_valid
            (make_endpoint
              d network_out network_out_capacity app_out app_out_capacity)
            (make_endpoint_state 'st0 'old_network_out 'old_app_out)
            network
            st1));
      lemma_result_valid_preserves
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        (make_endpoint_state 'st0 'old_network_out 'old_app_out)
        network
        st1;
      rewrite
        (client_endpoint.BS.bse_buffer_full
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received)
        as
        (buffer_full
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received);
      unfold (buffer_full
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        st1 received);
      unfold (terminal
        (make_endpoint
          d network_out network_out_capacity app_out app_out_capacity)
        st1 received);
      with committed model.
        assert (owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity)
          st1 received committed model);
      let pending_len =
        finish_owns
          (make_endpoint
            d network_out network_out_capacity app_out app_out_capacity);
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
  }
}
