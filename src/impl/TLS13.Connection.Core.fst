module TLS13.Connection.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module U8 = FStar.UInt8

noeq
type client_core = {
  state: ST.state_ref;
  log: ST.log_ref;
}

let is_client_core (c:client_core) (view:CL.connection_view) : slprop =
  ST.current c.state view.CL.state **
  ST.log_current c.log view **
  pure (CL.connection_view_consistent view)

let lemma_empty_prefix (buffer:B.bytes)
  : Lemma (buffer_prefix_matches buffer 0 B.empty)
  =
  Seq.lemma_len_slice buffer 0 0;
  assert (B.length B.empty == 0);
  assert (B.length (Seq.slice buffer 0 0) == 0);
  assert (forall (i:nat{i < B.length B.empty}).
            Seq.index B.empty i == Seq.index (Seq.slice buffer 0 0) i);
  Seq.lemma_eq_intro B.empty (Seq.slice buffer 0 0)

fn client_core_new ()
  returns c: client_core
  ensures is_client_core c CL.empty_connection_view
{
  let st = ST.alloc_initial ();
  let log = ST.alloc_initial_log ();
  let c = { state = st; log = log };
  rewrite (ST.current st S.initial) as (ST.current c.state CL.empty_connection_view.CL.state);
  rewrite (ST.log_current log CL.empty_connection_view) as (ST.log_current c.log CL.empty_connection_view);
  assert (pure (CL.connection_view_consistent CL.empty_connection_view));
  fold (is_client_core c CL.empty_connection_view);
  c
}

fn client_core_free (c: client_core)
  requires is_client_core c 'view
  ensures emp
{
  unfold (is_client_core c 'view);
  drop_ (ST.current c.state 'view.CL.state);
  drop_ (ST.log_current c.log 'view);
}

fn process_request
  (c: client_core)
  (kind: request_kind)
  (network_in: array U8.t)
  (network_in_len: SZ.t)
  (app_in: array U8.t)
  (app_in_len: SZ.t)
  (requested_app_len: SZ.t)
  (network_out: array U8.t)
  (network_out_cap: SZ.t)
  (app_out: array U8.t)
  (app_out_cap: SZ.t)
  (#view0: erased CL.connection_view)
  (#mreq: erased CL.client_request)
requires
  is_client_core c view0 **
  pts_to network_in 'network_in_bytes **
  pts_to app_in 'app_in_bytes **
  pts_to network_out 'network_out0 **
  pts_to app_out 'app_out0 **
  pure (
    B.length 'network_in_bytes == SZ.v network_in_len /\
    B.length 'app_in_bytes == SZ.v app_in_len /\
    B.length 'network_out0 == SZ.v network_out_cap /\
    B.length 'app_out0 == SZ.v app_out_cap /\
    view0.CL.state.S.phase == S.ApplicationData /\
    request_buffers_match
      kind
      (Ghost.reveal 'network_in_bytes)
      (Ghost.reveal 'app_in_bytes)
      (SZ.v requested_app_len)
      mreq)
returns result: core_result
ensures exists* view1 network_out1 app_out1.
  is_client_core c view1 **
  pts_to network_in 'network_in_bytes **
  pts_to app_in 'app_in_bytes **
  pts_to network_out network_out1 **
  pts_to app_out app_out1 **
  pure (
    B.length network_out1 == SZ.v network_out_cap /\
    B.length app_out1 == SZ.v app_out_cap /\
    (exists mresp.
      response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal app_out1) mresp /\
      CL.step view0 mreq view1 mresp))
{
  unfold (is_client_core c view0);
  if KSendApplicationData? kind {
    let app_bytes : erased B.bytes = Ghost.reveal 'app_in_bytes;
    assert (pure (mreq == CL.request_no_network_in (CL.OpSendApplicationData (Ghost.reveal app_bytes))));
    let view1 : erased CL.connection_view =
      CL.note_app_sent view0 (Ghost.reveal app_bytes) (S.advance_write_record view0.CL.state);
    ST.advance c.state (S.SendApplicationData (Ghost.reveal app_bytes)) (S.advance_write_record view0.CL.state);
    CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
    CL.lemma_step_send_application_data_success view0 view0 (Ghost.reveal app_bytes) (S.advance_write_record view0.CL.state);
    ST.advance_log c.log (Ghost.reveal view1);
    let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.ActionComplete };
    let resp = CL.response_no_network_out B.empty CL.ActionComplete;
    CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
    assert (pure (CL.step view0 mreq (Ghost.reveal view1) resp));
    lemma_empty_prefix (Ghost.reveal 'network_out0);
    lemma_empty_prefix (Ghost.reveal 'app_out0);
    assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
    assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                              CL.step view0 mreq (Ghost.reveal view1) mresp));
    fold (is_client_core c (Ghost.reveal view1));
    result
  } else if KReadApplicationData? kind {
    assert (pure (mreq == CL.request_with_network_in (CL.OpReadApplicationData (SZ.v requested_app_len)) B.empty));
    let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.NeedNetworkInput };
    let resp = CL.response_no_network_out B.empty CL.NeedNetworkInput;
    CL.lemma_append_empty_right view0.CL.raw_log.CL.raw_sent;
    CL.lemma_append_empty_right view0.CL.raw_log.CL.raw_received;
    CL.lemma_connection_view_single_step_for_core_step view0 mreq view0 resp;
    assert (pure (CL.step view0 mreq view0 resp));
    ST.advance_log c.log view0;
    lemma_empty_prefix (Ghost.reveal 'network_out0);
    lemma_empty_prefix (Ghost.reveal 'app_out0);
    assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
    assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                              CL.step view0 mreq view0 mresp));
    fold (is_client_core c view0);
    result
  } else {
    assert (pure (mreq == CL.request_no_network_in CL.OpClose));
    let view1 : erased CL.connection_view =
      CL.note_send_close_notify view0 (S.send_close_state view0.CL.state);
    ST.advance c.state S.SendCloseNotify (S.send_close_state view0.CL.state);
    CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
    CL.lemma_step_close_success view0 view0 (S.send_close_state view0.CL.state);
    ST.advance_log c.log (Ghost.reveal view1);
    let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Closed };
    let resp = CL.response_no_network_out B.empty CL.Closed;
    CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
    assert (pure (CL.step view0 mreq (Ghost.reveal view1) resp));
    lemma_empty_prefix (Ghost.reveal 'network_out0);
    lemma_empty_prefix (Ghost.reveal 'app_out0);
    assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
    assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                              CL.step view0 mreq (Ghost.reveal view1) mresp));
    fold (is_client_core c (Ghost.reveal view1));
    result
  }
}
