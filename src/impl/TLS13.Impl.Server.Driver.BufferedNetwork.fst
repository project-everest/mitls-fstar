module TLS13.Impl.Server.Driver.BufferedNetwork

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BS = Common.BufferedStream
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module CryptoSpec = TLS13.Crypto.Spec
module DN = TLS13.Impl.Server.Driver.Network
module DL = TLS13.Impl.Server.Driver.Local
module DS = TLS13.Impl.Server.Driver.State
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec

noeq type endpoint_state = {
  endpoint_connection: CS.connection_state;
  endpoint_network_out: B.bytes;
  endpoint_app_out: B.bytes;
}

noeq type endpoint = {
  endpoint_driver: DS.buffered_driver;
  endpoint_certificate_chain: Ghost.erased B.bytes;
  endpoint_credential_identity: Ghost.erased CS.server_credential_identity;
  endpoint_network_out_buffer: array U8.t;
  endpoint_network_out_capacity: SZ.t;
  endpoint_app_out_buffer: array U8.t;
  endpoint_app_out_capacity: SZ.t;
}

let decide
  (result:buffered_network_result)
  : BS.classification unit ST.server_status =
  let buffer_resp = result.buffered_network_read.network_read_buffer_resp in
  match buffer_resp.ST.response.ST.status with
  | ST.NeedMoreInput ->
    BS.NeedMore
  | ST.StepOk ->
    BS.Yield buffer_resp.ST.consumed_len ()
  | status ->
    BS.Reject status

let needs_more
  (_:endpoint_state)
  (pending:B.bytes)
  : prop =
  W.record_prefix_incomplete pending

let result_valid
  (_:endpoint)
  (before:endpoint_state)
  (result:buffered_network_result)
  (after:endpoint_state)
  : prop =
  let buffer_resp =
    result.buffered_network_read.network_read_buffer_resp in
  ST.server_network_bytes_end_to_end_correct
    before.endpoint_connection
    after.endpoint_connection
    buffer_resp
    (Ghost.reveal result.buffered_network_read.network_read_prefix)
    after.endpoint_network_out
    after.endpoint_app_out /\
  ST.server_network_consumed_input_projection
    before.endpoint_connection
    after.endpoint_connection
    buffer_resp
    (Ghost.reveal result.buffered_network_read.network_read_prefix)
    after.endpoint_network_out
    after.endpoint_app_out

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
        ST.server_end_to_end_invariant after.endpoint_connection)
=
  let response =
    result.buffered_network_read.network_read_buffer_resp in
  let prefix =
    Ghost.reveal result.buffered_network_read.network_read_prefix in
  ST.lemma_server_network_bytes_preserves_config
    before.endpoint_connection
    after.endpoint_connection
    response
    prefix
    after.endpoint_network_out
    after.endpoint_app_out

let lemma_needmore_transition
  (decision:BS.classification unit ST.server_status)
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

noextract
let owns
  (e:endpoint)
  (st:endpoint_state)
  (received committed:B.bytes)
  (model:BT.phys_buffer)
  : slprop =
  exists* pending_len sent.
    DS.buffered_driver_indexed
      e.endpoint_driver
      st.endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending model)
      pending_len
      model
      received
      committed
      sent **
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
fn tcp_history_note_write
  (hist:MR.mref CI.io_history_preorder)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (chunk:Ghost.erased B.bytes)
  requires
    MR.pts_to hist #1.0R
      (DS.server_driver_history
        (Ghost.reveal received)
        (Ghost.reveal sent))
  ensures
    MR.pts_to hist #1.0R
      (DS.server_driver_history
        (Ghost.reveal received)
        (Seq.append (Ghost.reveal sent) (Ghost.reveal chunk)))
{
  CPI.lemma_bytes_extends_refl (Ghost.reveal received);
  CPI.lemma_bytes_extends_append
    (Ghost.reveal sent)
    (Ghost.reveal chunk);
  CI.lemma_io_history_preorder_of_extends
    (DS.server_driver_history
      (Ghost.reveal received)
      (Ghost.reveal sent))
    (DS.server_driver_history
      (Ghost.reveal received)
      (Seq.append (Ghost.reveal sent) (Ghost.reveal chunk)));
  MR.update hist
    (DS.server_driver_history
      (Ghost.reveal received)
      (Seq.append (Ghost.reveal sent) (Ghost.reveal chunk)))
}

ghost
fn tcp_history_note_read
  (hist:MR.mref CI.io_history_preorder)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (chunk:Ghost.erased B.bytes)
  requires
    MR.pts_to hist #1.0R
      (DS.server_driver_history
        (Ghost.reveal received)
        (Ghost.reveal sent))
  ensures
    MR.pts_to hist #1.0R
      (DS.server_driver_history
        (Seq.append (Ghost.reveal received) (Ghost.reveal chunk))
        (Ghost.reveal sent))
{
  CPI.lemma_bytes_extends_append
    (Ghost.reveal received)
    (Ghost.reveal chunk);
  CPI.lemma_bytes_extends_refl (Ghost.reveal sent);
  CI.lemma_io_history_preorder_of_extends
    (DS.server_driver_history
      (Ghost.reveal received)
      (Ghost.reveal sent))
    (DS.server_driver_history
      (Seq.append (Ghost.reveal received) (Ghost.reveal chunk))
      (Ghost.reveal sent));
  MR.update hist
    (DS.server_driver_history
      (Seq.append (Ghost.reveal received) (Ghost.reveal chunk))
      (Ghost.reveal sent))
}

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
    assert (DS.buffered_driver_indexed
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending (Ghost.reveal model))
      pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (DS.buffered_driver_indexed
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (Ghost.reveal e.endpoint_certificate_chain)
    (Ghost.reveal e.endpoint_credential_identity)
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  BT.recall_model e.endpoint_driver.DS.buffered_driver_channel;
  fold (DS.buffered_driver_indexed
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (Ghost.reveal e.endpoint_certificate_chain)
    (Ghost.reveal e.endpoint_credential_identity)
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

let lemma_yield_transition
  (k:SZ.t)
  (committed committed':B.bytes)
  (model model':BT.phys_buffer)
  : Lemma
      (requires
        0 < SZ.v k /\
        SZ.v k <= Seq.length (BT.pending model) /\
        Seq.equal committed'
          (BT.committed_after committed model (SZ.v k)) /\
        model' == BT.compact model (SZ.v k))
      (ensures
        BS.process_transition
          (BS.Yield k () <: BS.classification unit ST.server_status)
          committed
          committed'
          model
          model')
=
  ()

#push-options "--z3refresh --z3rlimit 30 --split_queries always --z3seed 17"
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
  returns
    outcome:BS.process_outcome
      unit ST.server_status buffered_network_result
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
    assert (DS.buffered_driver_indexed
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending (Ghost.reveal model))
      pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (DS.buffered_driver_indexed
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (Ghost.reveal e.endpoint_certificate_chain)
    (Ghost.reveal e.endpoint_credential_identity)
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  BT.recall_model e.endpoint_driver.buffered_driver_channel;
  let view =
    BT.borrow_pending e.endpoint_driver.buffered_driver_channel;
  let buffer_resp =
    S.process_network_bytes
      e.endpoint_driver.buffered_driver_server
      (BT.view_data view)
      (BT.view_length view)
      e.endpoint_network_out_buffer
      e.endpoint_network_out_capacity
      e.endpoint_app_out_buffer
      e.endpoint_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly e.endpoint_driver.buffered_driver_server st1 **
      pts_to (BT.view_data view) (BT.pending (Ghost.reveal model)) **
      pts_to e.endpoint_network_out_buffer network_out_bytes **
      pts_to e.endpoint_app_out_buffer app_out_bytes);
  assert (pure (ST.server_network_bytes_end_to_end_correct
    (Ghost.reveal st).endpoint_connection
    st1
    buffer_resp
    (BT.pending (Ghost.reveal model))
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_network_consumed_input_projection
    (Ghost.reveal st).endpoint_connection
    st1
    buffer_resp
    (BT.pending (Ghost.reveal model))
    network_out_bytes
    app_out_bytes));
  let read_result = {
    network_read_len = BT.view_length view;
    network_read_buffer_resp = buffer_resp;
    network_read_written = buffer_resp.ST.response.ST.network_out_len;
    network_read_prefix = Ghost.hide (BT.pending (Ghost.reveal model));
  };
  BT.release_pending e.endpoint_driver.buffered_driver_channel view;
  let need_more =
    buffer_resp.ST.response.ST.status = ST.NeedMoreInput;
  if need_more {
    assert (pure (st1 == (Ghost.reveal st).endpoint_connection));
    assert (pure (buffer_resp.ST.consumed_len == 0sz));
    assert (pure (
      Seq.equal network_out_bytes
        (Ghost.reveal st).endpoint_network_out));
    assert (pure (
      Seq.equal app_out_bytes
        (Ghost.reveal st).endpoint_app_out));
    rewrite
      (S.connection_exactly
        e.endpoint_driver.buffered_driver_server
        st1)
      as
      (S.connection_exactly
        e.endpoint_driver.buffered_driver_server
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
    W.lemma_record_prefix_incomplete_bound
      (BT.pending (Ghost.reveal model));
    assert (pure (BT.can_read (Ghost.reveal model)));
    let result = {
      buffered_network_read = read_result;
      buffered_network_new_len = read_result.network_read_len;
    };
    fold (DS.buffered_driver_indexed
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
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
    DN.lemma_server_network_wire_accounting
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      network_out_bytes
      app_out_bytes
      (Ghost.reveal committed);
    let remaining =
      BT.commit_prefix
        e.endpoint_driver.buffered_driver_channel
        buffer_resp.ST.consumed_len;
    with model'.
      assert (
        BT.is_buffered
          e.endpoint_driver.buffered_driver_channel
          model'
          (Ghost.reveal received)
          (BT.committed_after
            (Ghost.reveal committed)
            (Ghost.reveal model)
            (SZ.v buffer_resp.ST.consumed_len))
          sent);
    let written =
      BT.write
        e.endpoint_driver.buffered_driver_channel
        e.endpoint_network_out_buffer
        buffer_resp.ST.response.ST.network_out_len;
    assert (pure (
      written == buffer_resp.ST.response.ST.network_out_len));
    let sent_delta =
      Ghost.hide
        (ST.response_network_out
          buffer_resp.ST.response
          network_out_bytes);
    assert (pure (SZ.v written <= B.length network_out_bytes));
    assert (pure (Seq.equal
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty)
      (Ghost.reveal sent_delta)));
    Seq.lemma_eq_elim
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty)
      (Ghost.reveal sent_delta);
    rewrite
      (BT.is_buffered
        e.endpoint_driver.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.ST.consumed_len))
        (B.append sent
          (if SZ.v written <= B.length network_out_bytes
           then Seq.slice network_out_bytes 0 (SZ.v written)
           else B.empty)))
      as
      (BT.is_buffered
        e.endpoint_driver.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.ST.consumed_len))
        (B.append sent (Ghost.reveal sent_delta)));
    tcp_history_note_write
      e.endpoint_driver.buffered_driver_tcp_history
      received
      (Ghost.hide sent)
      sent_delta;
    let sent' = Ghost.hide (B.append sent (Ghost.reveal sent_delta));
    rewrite
      (BT.is_buffered
        e.endpoint_driver.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.ST.consumed_len))
        (B.append sent (Ghost.reveal sent_delta)))
      as
      (BT.is_buffered
        e.endpoint_driver.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.ST.consumed_len))
        (Ghost.reveal sent'));
    rewrite
      (MR.pts_to
        e.endpoint_driver.buffered_driver_tcp_history
        #1.0R
        (DS.server_driver_history
          (Ghost.reveal received)
          (B.append sent (Ghost.reveal sent_delta))))
      as
      (MR.pts_to
        e.endpoint_driver.buffered_driver_tcp_history
        #1.0R
        (DS.server_driver_history
          (Ghost.reveal received)
          (Ghost.reveal sent')));
    DN.lemma_server_network_logged_received_exact_when_nonfailed
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      network_out_bytes
      app_out_bytes
      (Ghost.reveal received)
      sent
      (Ghost.reveal committed)
      (BT.pending (Ghost.reveal model))
      pending_len;
    let new_committed =
      Ghost.hide
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.ST.consumed_len));
    assert (pure (Seq.equal
      (ST.server_network_consumed_prefix
        buffer_resp
        (BT.pending (Ghost.reveal model)))
      (BT.take
        (BT.pending (Ghost.reveal model))
        (SZ.v buffer_resp.ST.consumed_len))));
    assert (pure (Seq.equal
      (Ghost.reveal new_committed)
      (B.append
        (Ghost.reveal committed)
        (ST.server_network_consumed_prefix
          buffer_resp
          (BT.pending (Ghost.reveal model))))));
    rewrite
      (BT.is_buffered
        e.endpoint_driver.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (BT.committed_after
          (Ghost.reveal committed)
          (Ghost.reveal model)
          (SZ.v buffer_resp.ST.consumed_len))
        (Ghost.reveal sent'))
      as
      (BT.is_buffered
        e.endpoint_driver.buffered_driver_channel
        model'
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        (Ghost.reveal sent'));
    assert (pure (Seq.equal
      (Ghost.reveal sent')
      st1.CS.cs_wire_log.CL.raw_sent));
    BT.recall_model e.endpoint_driver.buffered_driver_channel;
    assert (pure (DS.server_driver_wire_logs_match_witness
      st1
      (Ghost.reveal received)
      (Ghost.reveal sent')
      (Ghost.reveal new_committed)
      (BT.pending model')
      remaining));
    DN.lemma_server_driver_network_process_correct_intro
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      network_out_bytes
      app_out_bytes
      sent
      (Ghost.reveal sent');
    DN.lemma_server_driver_network_process_correct_preserves_supported_profile_selection
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      sent
      (Ghost.reveal sent')
      (Ghost.reveal e.endpoint_credential_identity);
    ST.lemma_server_network_bytes_preserves_config
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      network_out_bytes
      app_out_bytes;
    unfold (DS.buffered_driver_canonical_progress
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection);
    assert (pure (CPI.buffers_wf
      (BT.pending (Ghost.reveal model))
      read_result.network_read_len
      (Ghost.reveal st).endpoint_network_out
      e.endpoint_network_out_capacity));
    SP.lemma_server_network_event_progress
      (Ghost.reveal e.endpoint_driver.buffered_driver_initial)
      (Ghost.reveal st).endpoint_connection
      st1
      buffer_resp
      (BT.pending (Ghost.reveal model))
      read_result.network_read_len
      (Ghost.reveal st).endpoint_network_out
      network_out_bytes
      e.endpoint_network_out_capacity
      app_out_bytes;
    MR.update e.endpoint_driver.buffered_driver_progress st1;
    fold (DS.buffered_driver_canonical_progress
      e.endpoint_driver
      st1);
    assert (pure (DS.server_driver_config_matches_credentials
      st1
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)));
    fold (DS.buffered_driver_indexed
      e.endpoint_driver
      st1
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending model')
      remaining
      model'
      (Ghost.reveal received)
      (Ghost.reveal new_committed)
      (Ghost.reveal sent'));
    let st' : Ghost.erased endpoint_state = Ghost.hide {
      endpoint_connection = st1;
      endpoint_network_out = network_out_bytes;
      endpoint_app_out = app_out_bytes;
    };
    rewrite
      (DS.buffered_driver_indexed
        e.endpoint_driver
        st1
        (Ghost.reveal e.endpoint_certificate_chain)
        (Ghost.reveal e.endpoint_credential_identity)
        (BT.pending model')
        remaining
        model'
        (Ghost.reveal received)
        (Ghost.reveal new_committed)
        (Ghost.reveal sent'))
      as
      (DS.buffered_driver_indexed
        e.endpoint_driver
        (Ghost.reveal st').endpoint_connection
        (Ghost.reveal e.endpoint_certificate_chain)
        (Ghost.reveal e.endpoint_credential_identity)
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
      buffer_resp.ST.response.ST.status = ST.StepOk;
    if step_ok {
      let decision : BS.classification unit ST.server_status =
        BS.Yield buffer_resp.ST.consumed_len ();
      assert (pure (0 < SZ.v buffer_resp.ST.consumed_len));
      assert (pure (decide result == decision));
      assert (pure (
        result_valid e (Ghost.reveal st) result (Ghost.reveal st')));
      assert (pure (
        model' ==
          BT.compact
            (Ghost.reveal model)
            (SZ.v buffer_resp.ST.consumed_len)));
      lemma_yield_transition
        buffer_resp.ST.consumed_len
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
            (BS.Yield buffer_resp.ST.consumed_len ())));
      BS.Processed
        result
        (BS.Yield buffer_resp.ST.consumed_len ())
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
            (BS.Reject buffer_resp.ST.response.ST.status)));
      BS.Processed
        result
        (BS.Reject buffer_resp.ST.response.ST.status)
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
        assert (DS.buffered_driver_indexed
          e.endpoint_driver
          (Ghost.reveal st).endpoint_connection
          (Ghost.reveal e.endpoint_certificate_chain)
          (Ghost.reveal e.endpoint_credential_identity)
          (BT.pending (Ghost.reveal model))
          pending_len
          (Ghost.reveal model)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          sent);
      unfold (DS.buffered_driver_indexed
        e.endpoint_driver
        (Ghost.reveal st).endpoint_connection
        (Ghost.reveal e.endpoint_certificate_chain)
        (Ghost.reveal e.endpoint_credential_identity)
        (BT.pending (Ghost.reveal model))
        pending_len
        (Ghost.reveal model)
        (Ghost.reveal received)
        (Ghost.reveal committed)
        sent);
      let _ =
        BT.read_more e.endpoint_driver.buffered_driver_channel;
      with chunk model'.
        assert (
          BT.is_buffered
            e.endpoint_driver.buffered_driver_channel
            model'
            (Seq.append (Ghost.reveal received) chunk)
            (Ghost.reveal committed)
            sent **
          MR.pts_to
            e.endpoint_driver.buffered_driver_tcp_history
            #1.0R
            (DS.server_driver_history (Ghost.reveal received) sent));
      tcp_history_note_read
        e.endpoint_driver.buffered_driver_tcp_history
        received
        (Ghost.hide sent)
        (Ghost.hide chunk);
      let new_pending_len =
        BT.pending_length e.endpoint_driver.buffered_driver_channel;
      Seq.append_assoc
        (Ghost.reveal committed)
        (BT.pending (Ghost.reveal model))
        chunk;
      assert (pure (DS.server_driver_wire_logs_match_witness
        (Ghost.reveal st).endpoint_connection
        (Seq.append (Ghost.reveal received) chunk)
        sent
        (Ghost.reveal committed)
        (BT.pending model')
        new_pending_len));
      fold (DS.buffered_driver_indexed
        e.endpoint_driver
        (Ghost.reveal st).endpoint_connection
        (Ghost.reveal e.endpoint_certificate_chain)
        (Ghost.reveal e.endpoint_credential_identity)
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

    fn process_local_event_preserving_success
      (s:S.server)
      (creds:O.server_credentials)
      (kind:ST.local_event_kind)
      (payload:array U8.t)
      (payload_len:SZ.t)
      (network_out:array U8.t)
      (network_out_len:SZ.t)
      (app_out:array U8.t)
      (app_out_len:SZ.t)
      requires
        S.connection_exactly s 'st0 **
        O.is_server_credentials
          creds
          'certificate_chain
          'credential_identity **
        pts_to payload 'payload_bytes **
        pts_to network_out 'old_network_out **
        pts_to app_out 'old_app_out **
        pure (
          B.length 'payload_bytes == SZ.v payload_len /\
          B.length 'old_network_out == SZ.v network_out_len /\
          B.length 'old_app_out == SZ.v app_out_len /\
          ST.server_end_to_end_invariant 'st0 /\
          local_event_ready
            'st0
            kind
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity))
      returns resp:ST.server_response
      ensures
        exists* st1 network_out_bytes app_out_bytes.
          S.connection_exactly s st1 **
          O.is_server_credentials
            creds
            'certificate_chain
            'credential_identity **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (
            B.length network_out_bytes == SZ.v network_out_len /\
            B.length app_out_bytes == SZ.v app_out_len /\
            ST.server_local_event_end_to_end_correct
              'st0
              st1
              resp
              kind
              (Ghost.reveal 'payload_bytes)
              network_out_bytes
              app_out_bytes /\
            local_event_success_correct
              'st0
              st1
              resp
              kind
              (Ghost.reveal 'payload_bytes))
    {
      match kind {
        ST.LocalDeriveSharedSecret -> {
          assert (pure (ST.server_local_event_input_ready_with_credentials
            'st0
            kind
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity)));
          assert (pure (ST.server_local_event_input_ready
            'st0
            kind
            (Ghost.reveal 'payload_bytes)));
          let resp =
            S.process_derive_shared_secret_from_private_array
              s
              payload
              network_out
              network_out_len
              app_out
              app_out_len;
          with st1 network_out_bytes app_out_bytes.
            assert (
              S.connection_exactly s st1 **
              O.is_server_credentials
                creds
                'certificate_chain
                'credential_identity **
              pts_to payload 'payload_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
          assert (pure (local_event_success_correct
            'st0
            st1
            resp
            kind
            (Ghost.reveal 'payload_bytes)));
          resp
        }
        _ -> {
          let resp =
            S.process_local_event_with_credentials
              s
              creds
              kind
              payload
              payload_len
              network_out
              network_out_len
              app_out
              app_out_len;
          with st1 network_out_bytes app_out_bytes.
            assert (
              S.connection_exactly s st1 **
              O.is_server_credentials
                creds
                'certificate_chain
                'credential_identity **
              pts_to payload 'payload_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
          assert (pure (local_event_success_correct
            'st0
            st1
            resp
            kind
            (Ghost.reveal 'payload_bytes)));
          resp
        }
      }
    }

    fn process_local_event
      (d:DS.buffered_driver)
      (kind:ST.local_event_kind)
      (payload:array U8.t)
      (payload_len:SZ.t)
      (network_out:array U8.t)
      (network_out_len:SZ.t)
      (app_out:array U8.t)
      (app_out_len:SZ.t)
      requires
        DS.buffered_driver_exactly
          d
          'st0
          'certificate_chain
          'credential_identity
          'buffered
          'buffered_len **
        pts_to payload 'payload_bytes **
        pts_to network_out 'old_network_out **
        pts_to app_out 'old_app_out **
        pure (
          B.length 'payload_bytes == SZ.v payload_len /\
          B.length 'old_network_out == SZ.v network_out_len /\
          B.length 'old_app_out == SZ.v app_out_len /\
          local_event_ready
            'st0
            kind
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity))
      returns result:local_write_result
      ensures
        exists* st1 network_out_bytes app_out_bytes.
          DS.buffered_driver_exactly
            d
            st1
            'certificate_chain
            'credential_identity
            'buffered
            'buffered_len **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (
            B.length network_out_bytes == SZ.v network_out_len /\
            B.length app_out_bytes == SZ.v app_out_len /\
            ST.server_local_event_end_to_end_correct
              'st0
              st1
              result.local_write_resp
              kind
              (Ghost.reveal 'payload_bytes)
              network_out_bytes
              app_out_bytes /\
            local_event_success_correct
              'st0
              st1
              result.local_write_resp
              kind
              (Ghost.reveal 'payload_bytes) /\
            result.local_write_written ==
              result.local_write_resp.ST.network_out_len)
    {
      unfold (DS.buffered_driver_exactly
        d
        'st0
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len);
      with model received committed sent.
        assert (DS.buffered_driver_indexed
          d
          'st0
          'certificate_chain
          'credential_identity
          'buffered
          'buffered_len
          model
          received
          committed
          sent);
      unfold (DS.buffered_driver_indexed
        d
        'st0
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len
        model
        received
        committed
        sent);
      let resp =
        process_local_event_preserving_success
          d.buffered_driver_server
          d.buffered_driver_credentials
          kind
          payload
          payload_len
          network_out
          network_out_len
          app_out
          app_out_len;
      with st1 network_out_bytes app_out_bytes.
        assert (
          S.connection_exactly d.buffered_driver_server st1 **
          O.is_server_credentials
            d.buffered_driver_credentials
            'certificate_chain
            'credential_identity **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes);
      assert (pure (ST.server_local_event_end_to_end_correct
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        app_out_bytes));
      assert (pure (local_event_success_correct
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)));
      DS.lemma_local_event_wire_lengths
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        app_out_bytes;
      let written =
        BT.write
          d.buffered_driver_channel
          network_out
          resp.ST.network_out_len;
      assert (pure (written == resp.ST.network_out_len));
      assert (pure (SZ.v written <= B.length network_out_bytes));
      let sent_delta =
        Ghost.hide
          (ST.response_network_out resp network_out_bytes);
      assert (pure (Seq.equal
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)
        (Ghost.reveal sent_delta)));
      Seq.lemma_eq_elim
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)
        (Ghost.reveal sent_delta);
      rewrite
        (BT.is_buffered
          d.buffered_driver_channel
          model
          received
          committed
          (B.append sent
            (if SZ.v written <= B.length network_out_bytes
             then Seq.slice network_out_bytes 0 (SZ.v written)
             else B.empty)))
        as
        (BT.is_buffered
          d.buffered_driver_channel
          model
          received
          committed
          (B.append sent (Ghost.reveal sent_delta)));
      tcp_history_note_write
        d.buffered_driver_tcp_history
        (Ghost.hide received)
        (Ghost.hide sent)
        sent_delta;
      let sent' = Ghost.hide (B.append sent (Ghost.reveal sent_delta));
      rewrite
        (BT.is_buffered
          d.buffered_driver_channel
          model
          received
          committed
          (B.append sent (Ghost.reveal sent_delta)))
        as
        (BT.is_buffered
          d.buffered_driver_channel
          model
          received
          committed
          (Ghost.reveal sent'));
      rewrite
        (MR.pts_to
          d.buffered_driver_tcp_history
          #1.0R
          (DS.server_driver_history
            received
            (B.append sent (Ghost.reveal sent_delta))))
        as
        (MR.pts_to
          d.buffered_driver_tcp_history
          #1.0R
          (DS.server_driver_history received (Ghost.reveal sent')));
      assert (pure (Seq.equal sent 'st0.CS.cs_wire_log.CL.raw_sent));
      Seq.lemma_eq_elim sent 'st0.CS.cs_wire_log.CL.raw_sent;
      assert (pure (Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          'st0.CS.cs_wire_log.CL.raw_sent
          (Ghost.reveal sent_delta))));
      assert (pure (Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        'st0.CS.cs_wire_log.CL.raw_received));
      Seq.lemma_eq_elim
        st1.CS.cs_wire_log.CL.raw_received
        'st0.CS.cs_wire_log.CL.raw_received;
      DS.lemma_server_local_event_received_exact_when_nonfailed
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
        (BT.pending model)
        'buffered_len;
      assert (pure (DS.server_driver_wire_logs_match_witness
        st1
        received
        (Ghost.reveal sent')
        committed
        (BT.pending model)
        'buffered_len));
      unfold (DS.buffered_driver_canonical_progress d 'st0);
      SP.lemma_server_local_event_progress
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        app_out_bytes;
      MR.update d.buffered_driver_progress st1;
      fold (DS.buffered_driver_canonical_progress d st1);
      DL.lemma_server_driver_local_write_correct_intro
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)
        sent
        (Ghost.reveal sent')
        network_out_bytes
        app_out_bytes;
      DL.lemma_server_driver_local_write_correct_preserves_supported_profile_selection
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal 'certificate_chain)
        (Ghost.reveal 'credential_identity)
        sent
        (Ghost.reveal sent');
      ST.lemma_server_local_event_preserves_config
        'st0
        st1
        resp
        kind
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        app_out_bytes;
      assert (pure (DS.server_driver_config_matches_credentials
        st1
        (Ghost.reveal 'certificate_chain)
        (Ghost.reveal 'credential_identity)));
      fold (DS.buffered_driver_indexed
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len
        model
        received
        committed
        (Ghost.reveal sent'));
      fold (DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
        'buffered
        'buffered_len);
      {
        local_write_resp = resp;
        local_write_written = written;
      }
    }

    noextract
    let server_endpoint = {
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
#pop-options

private
fn rec server_drive
  (e:endpoint)
  (st:Ghost.erased endpoint_state)
  (received:Ghost.erased B.bytes)
  (committed:Ghost.erased B.bytes)
  (model:Ghost.erased BT.phys_buffer)
  (fuel:SZ.t)
  requires
    owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model)
  returns outcome:BS.drive_outcome unit ST.server_status buffered_network_result
  ensures
    BS.drive_post
      server_endpoint
      e
      (Ghost.reveal st)
      outcome **
    pure (SZ.v (BS.drive_fuel_left outcome) <= SZ.v fuel)
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    rewrite
      (owns
        e
        (Ghost.reveal st)
        (Ghost.reveal received)
        (Ghost.reveal committed)
        (Ghost.reveal model))
      as
      (server_endpoint.BS.bse_owns
        e
        (Ghost.reveal st)
        (Ghost.reveal received)
        (Ghost.reveal committed)
        (Ghost.reveal model));
    fold (BS.drive_post
      server_endpoint
      e
      (Ghost.reveal st)
      BS.DriveExhausted);
    BS.DriveExhausted
  } else {
    assert (pure (0 < SZ.v fuel));
    owns_wf e st received committed model;
    let processed = process e st received committed model;
    match processed {
      BS.ProcessBufferFull result -> {
        unfold (BS.process_post
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
          (BS.ProcessBufferFull result));
        with st'.
          assert (
            buffer_full e st' (Ghost.reveal received) **
            pure (result_valid e (Ghost.reveal st) result st'));
        rewrite
          (buffer_full e st' (Ghost.reveal received))
          as
          (server_endpoint.BS.bse_buffer_full
            e st' (Ghost.reveal received));
        fold (BS.drive_post
          server_endpoint
          e
          (Ghost.reveal st)
          (BS.DriveBufferFull result fuel));
        BS.DriveBufferFull result fuel
      }
      BS.Processed result decision -> {
        unfold (BS.process_post
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
          (BS.Processed result decision));
        match decision {
          BS.NeedMore -> {
            with st' committed' model'.
              assert (
                read_auth
                  e
                  st'
                  (Ghost.reveal received)
                  committed'
                  model' **
                pure (
                  needs_more
                    (Ghost.reveal st)
                    (BT.pending (Ghost.reveal model)) /\
                  decision == decide result /\
                  result_valid e (Ghost.reveal st) result st' /\
                  BS.process_transition
                    decision
                    (Ghost.reveal committed)
                    committed'
                    (Ghost.reveal model)
                    model' /\
                  st' == Ghost.reveal st /\
                  BT.can_read (Ghost.reveal model)));
            lemma_needmore_transition
              decision
              (Ghost.reveal committed)
              committed'
              (Ghost.reveal model)
              model';
            rewrite
              (read_auth
                e
                st'
                (Ghost.reveal received)
                committed'
                model')
              as
              (read_auth
                e
                (Ghost.reveal st)
                (Ghost.reveal received)
                (Ghost.reveal committed)
                (Ghost.reveal model));
            read e st received committed model;
            with received' model'.
              assert (
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
                    model'));
            let next_fuel = SZ.sub fuel 1sz;
            assert (pure (SZ.v next_fuel < SZ.v fuel));
            server_drive
              e
              st
              (Ghost.hide received')
              committed
              (Ghost.hide model')
              next_fuel
          }
          BS.Progress consumed -> {
            with st' committed' model'.
              assert (
                owns
                  e
                  st'
                  (Ghost.reveal received)
                  committed'
                  model' **
                pure (result_valid e (Ghost.reveal st) result st'));
            assert (pure (decide result == BS.Progress consumed));
            rewrite
              (owns
                e
                st'
                (Ghost.reveal received)
                committed'
                model')
              as
              (server_endpoint.BS.bse_owns
                e
                st'
                (Ghost.reveal received)
                committed'
                model');
            fold (BS.drive_post
              server_endpoint
              e
              (Ghost.reveal st)
              (BS.DriveProgress result consumed fuel));
            BS.DriveProgress result consumed fuel
          }
          BS.Yield consumed output -> {
            with st' committed' model'.
              assert (
                owns
                  e
                  st'
                  (Ghost.reveal received)
                  committed'
                  model' **
                pure (result_valid e (Ghost.reveal st) result st'));
            assert (pure (decide result == BS.Yield consumed output));
            rewrite
              (owns
                e
                st'
                (Ghost.reveal received)
                committed'
                model')
              as
              (server_endpoint.BS.bse_owns
                e
                st'
                (Ghost.reveal received)
                committed'
                model');
            fold (BS.drive_post
              server_endpoint
              e
              (Ghost.reveal st)
              (BS.DriveYield result consumed output fuel));
            BS.DriveYield result consumed output fuel
          }
          BS.Reject error -> {
            with st' received'.
              assert (
                terminal e st' received' **
                pure (result_valid e (Ghost.reveal st) result st'));
            rewrite
              (terminal e st' received')
              as
              (server_endpoint.BS.bse_terminal e st' received');
            assert (pure (decide result == BS.Reject error));
            fold (BS.drive_post
              server_endpoint
              e
              (Ghost.reveal st)
              (BS.DriveReject result error fuel));
            BS.DriveReject result error fuel
          }
        }
      }
    }
  }
}

let make_endpoint
  (d:DS.buffered_driver)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  : endpoint =
  {
    endpoint_driver = d;
    endpoint_certificate_chain = certificate_chain;
    endpoint_credential_identity = credential_identity;
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

inline_for_extraction
fn finish_owns
  (e:endpoint)
  (d:DS.buffered_driver)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (network_out app_out:array U8.t)
  (#st:erased endpoint_state)
  (#received #committed:erased B.bytes)
  (#model:erased BT.phys_buffer)
  requires
    owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal model) **
    pure (
      e.endpoint_driver == d /\
      Ghost.reveal e.endpoint_certificate_chain ==
        Ghost.reveal certificate_chain /\
      Ghost.reveal e.endpoint_credential_identity ==
        Ghost.reveal credential_identity /\
      e.endpoint_network_out_buffer == network_out /\
      e.endpoint_app_out_buffer == app_out)
  returns pending_len:SZ.t
  ensures
    DS.buffered_driver_exactly
      d
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (BT.pending (Ghost.reveal model))
      pending_len **
    pts_to
      network_out
      (Ghost.reveal st).endpoint_network_out **
    pts_to
      app_out
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
    assert (DS.buffered_driver_indexed
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending (Ghost.reveal model))
      old_pending_len
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      sent);
  unfold (DS.buffered_driver_indexed
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (Ghost.reveal e.endpoint_certificate_chain)
    (Ghost.reveal e.endpoint_credential_identity)
    (BT.pending (Ghost.reveal model))
    old_pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  let view =
    BT.borrow_pending e.endpoint_driver.buffered_driver_channel;
  let pending_len = BT.view_length view;
  BT.release_pending
    e.endpoint_driver.buffered_driver_channel
    view;
  assert (pure (SZ.v pending_len ==
    B.length (BT.pending (Ghost.reveal model))));
  assert (pure (pending_len == old_pending_len));
  fold (DS.buffered_driver_indexed
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (Ghost.reveal e.endpoint_certificate_chain)
    (Ghost.reveal e.endpoint_credential_identity)
    (BT.pending (Ghost.reveal model))
    pending_len
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal committed)
    sent);
  fold (DS.buffered_driver_exactly
    e.endpoint_driver
    (Ghost.reveal st).endpoint_connection
    (Ghost.reveal e.endpoint_certificate_chain)
    (Ghost.reveal e.endpoint_credential_identity)
    (BT.pending (Ghost.reveal model))
    pending_len);
  rewrite
    (DS.buffered_driver_exactly
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending (Ghost.reveal model))
      pending_len)
    as
    (DS.buffered_driver_exactly
      d
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (BT.pending (Ghost.reveal model))
      pending_len);
  rewrite
    (pts_to
      e.endpoint_network_out_buffer
      (Ghost.reveal st).endpoint_network_out)
    as
    (pts_to network_out (Ghost.reveal st).endpoint_network_out);
  rewrite
    (pts_to
      e.endpoint_app_out_buffer
      (Ghost.reveal st).endpoint_app_out)
    as
    (pts_to app_out (Ghost.reveal st).endpoint_app_out);
  pending_len
}

inline_for_extraction
fn drive
  (d:DS.buffered_driver)
  (network_out:array U8.t)
  (network_out_capacity:SZ.t)
  (app_out:array U8.t)
  (app_out_capacity:SZ.t)
  (buffered_len:SZ.t)
  (fuel:SZ.t)
  requires
    DS.buffered_driver_exactly
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len **
    pts_to network_out 'old_network_out **
    pts_to app_out 'old_app_out **
    pure (
      B.length 'old_network_out == SZ.v network_out_capacity /\
      B.length 'old_app_out == SZ.v app_out_capacity /\
      TLS13.Impl.Messages.max_record_fragment_len <= SZ.v app_out_capacity)
  returns result:completed_drive
  ensures
    exists* st1 buffered_after network_out_bytes app_out_bytes.
      DS.buffered_driver_exactly
        d
        st1
        'certificate_chain
        'credential_identity
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
        ST.server_end_to_end_invariant st1 /\
        completed_drive_correct
          'st0
          st1
          'old_network_out
          network_out_bytes
          'old_app_out
          app_out_bytes
          result)
{
  let e =
    make_endpoint
      d
      'certificate_chain
      'credential_identity
      network_out
      network_out_capacity
      app_out
      app_out_capacity;
  let st : Ghost.erased endpoint_state =
    Ghost.hide (make_endpoint_state 'st0 'old_network_out 'old_app_out);
  unfold (DS.buffered_driver_exactly
    d
    'st0
    'certificate_chain
    'credential_identity
    'buffered
    buffered_len);
  with model received committed sent.
    assert (DS.buffered_driver_indexed
      d
      'st0
      'certificate_chain
      'credential_identity
      'buffered
      buffered_len
      model
      received
      committed
      sent);
  unfold (DS.buffered_driver_indexed
    d
    'st0
    'certificate_chain
    'credential_identity
    'buffered
    buffered_len
    model
    received
    committed
    sent);
  assert (pure ((Ghost.reveal st).endpoint_connection == 'st0));
  Seq.lemma_eq_elim (BT.pending model) 'buffered;
  fold (DS.buffered_driver_indexed
    d
    'st0
    'certificate_chain
    'credential_identity
    (BT.pending model)
    buffered_len
    model
    received
    committed
    sent);
  assert (pure (e.endpoint_driver == d));
  assert (pure (
    Ghost.reveal e.endpoint_certificate_chain == 'certificate_chain));
  assert (pure (
    Ghost.reveal e.endpoint_credential_identity == 'credential_identity));
  assert (pure (
    (Ghost.reveal st).endpoint_connection == 'st0));
  rewrite
    (DS.buffered_driver_indexed
      d
      'st0
      'certificate_chain
      'credential_identity
      (BT.pending model)
      buffered_len
      model
      received
      committed
      sent)
    as
    (DS.buffered_driver_indexed
      e.endpoint_driver
      (Ghost.reveal st).endpoint_connection
      (Ghost.reveal e.endpoint_certificate_chain)
      (Ghost.reveal e.endpoint_credential_identity)
      (BT.pending model)
      buffered_len
      model
      received
      committed
      sent);
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
  fold (owns e (Ghost.reveal st) received committed model);
  let outcome =
    server_drive
      e
      st
      (Ghost.hide received)
      (Ghost.hide committed)
      (Ghost.hide model)
      fuel;
  unfold (BS.drive_post
    server_endpoint
    e
    (Ghost.reveal st)
    outcome);
  match outcome {
    BS.DriveExhausted -> {
      with st1 received' committed' model'.
        assert (
          server_endpoint.BS.bse_owns
            e st1 received' committed' model' **
          pure (st1 == Ghost.reveal st));
      rewrite
        (server_endpoint.BS.bse_owns
          e st1 received' committed' model')
        as
        (owns e st1 received' committed' model');
      let pending_len =
        finish_owns
          e d 'certificate_chain 'credential_identity network_out app_out;
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveProgress network consumed fuel_left -> {
      with st1 received' committed' model'.
        assert (
          server_endpoint.BS.bse_owns
            e st1 received' committed' model' **
          pure (result_valid
            e
            (Ghost.reveal st)
            network
            st1));
      lemma_result_valid_preserves
        e
        (Ghost.reveal st)
        network
        st1;
      rewrite
        (server_endpoint.BS.bse_owns
          e st1 received' committed' model')
        as
        (owns e st1 received' committed' model');
      let pending_len =
        finish_owns
          e d 'certificate_chain 'credential_identity network_out app_out;
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveYield network consumed output fuel_left -> {
      with st1 received' committed' model'.
        assert (
          server_endpoint.BS.bse_owns
            e st1 received' committed' model' **
          pure (result_valid
            e
            (Ghost.reveal st)
            network
            st1 /\
            decide network == BS.Yield consumed output));
      lemma_result_valid_preserves
        e
        (Ghost.reveal st)
        network
        st1;
      rewrite
        (server_endpoint.BS.bse_owns
          e st1 received' committed' model')
        as
        (owns e st1 received' committed' model');
      let pending_len =
        finish_owns
          e d 'certificate_chain 'credential_identity network_out app_out;
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveReject network error fuel_left -> {
      with st1 received'.
        assert (
          server_endpoint.BS.bse_terminal
            e st1 received' **
          pure (result_valid
            e
            (Ghost.reveal st)
            network
            st1 /\
            decide network == BS.Reject error));
      lemma_result_valid_preserves
        e
        (Ghost.reveal st)
        network
        st1;
      rewrite
        (server_endpoint.BS.bse_terminal e st1 received')
        as
        (terminal e st1 received');
      unfold (terminal e st1 received');
      with committed' model'.
        assert (owns e st1 received' committed' model');
      let pending_len =
        finish_owns
          e d 'certificate_chain 'credential_identity network_out app_out;
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
    BS.DriveBufferFull network fuel_left -> {
      with st1 received'.
        assert (
          server_endpoint.BS.bse_buffer_full
            e st1 received' **
          pure (result_valid
            e
            (Ghost.reveal st)
            network
            st1));
      lemma_result_valid_preserves
        e
        (Ghost.reveal st)
        network
        st1;
      rewrite
        (server_endpoint.BS.bse_buffer_full e st1 received')
        as
        (buffer_full e st1 received');
      unfold (buffer_full e st1 received');
      unfold (terminal e st1 received');
      with committed' model'.
        assert (owns e st1 received' committed' model');
      let pending_len =
        finish_owns
          e d 'certificate_chain 'credential_identity network_out app_out;
      {
        completed_drive_outcome = outcome;
        completed_drive_pending_len = pending_len;
      }
    }
  }
}
