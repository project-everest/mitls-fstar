module TLS13.Connection.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module CL = TLS13.ConnectionLog
module Rec = TLS13.Record
module RF = TLS13.Record.Framing
module Seq = FStar.Seq
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8

noeq
type client_core = {
  state: ST.state_ref;
  log: ST.log_ref;
  client_application_record_state: Rec.record_state;
}

let is_client_core (c:client_core) (view:CL.connection_view) : slprop =
  exists* record_s.
    ST.current c.state view.CL.state **
    ST.log_current c.log view **
    Rec.is_record_state c.client_application_record_state record_s **
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

let lemma_prefix_slice (buffer:B.bytes) (len:nat)
  : Lemma
      (requires len <= B.length buffer)
      (ensures buffer_prefix_matches buffer len (Seq.slice buffer 0 len))
  =
  Seq.lemma_len_slice buffer 0 len;
  Seq.lemma_eq_refl (Seq.slice buffer 0 len) (Seq.slice buffer 0 len)

fn rec copy_payload_to_output_loop
  (payload: array U8.t)
  (payload_total_len: SZ.t)
  (out: array U8.t)
  (total_len: SZ.t)
  (src_index: SZ.t)
  (dst_index: SZ.t)
  (remaining: SZ.t)
  requires pts_to payload 'payload_bytes **
           pts_to out 'old **
           pure (B.length 'payload_bytes == SZ.v payload_total_len /\
                 B.length 'old == SZ.v total_len /\
                 SZ.v src_index + SZ.v remaining <= SZ.v payload_total_len /\
                 SZ.v dst_index + SZ.v remaining <= SZ.v total_len)
  ensures exists* bytes.
          pts_to payload 'payload_bytes **
          pts_to out bytes **
          pure (B.length bytes == SZ.v total_len)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    with bytes. assert (pts_to out bytes);
    assert (pure (B.length bytes == SZ.v total_len));
  } else {
    assert (pure (SZ.v src_index < SZ.v payload_total_len));
    assert (pure (SZ.v dst_index < SZ.v total_len));
    let b = payload.(src_index);
    out.(dst_index) <- b;
    let src_index' = SZ.(src_index +^ 1sz);
    let dst_index' = SZ.(dst_index +^ 1sz);
    let remaining' = SZ.(remaining -^ 1sz);
    with bytes. assert (pts_to out bytes);
    assert (pure (B.length bytes == SZ.v total_len));
    assert (pure (SZ.v remaining' < SZ.v remaining));
    assert (pure (SZ.v src_index' + SZ.v remaining' <= SZ.v payload_total_len));
    assert (pure (SZ.v dst_index' + SZ.v remaining' <= SZ.v total_len));
    copy_payload_to_output_loop payload payload_total_len out total_len src_index' dst_index' remaining'
  }
}

fn copy_payload_to_output
  (payload: array U8.t)
  (payload_total_len: SZ.t)
  (copy_len: SZ.t)
  (out: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  requires pts_to payload 'payload_bytes **
           pts_to out 'old **
           pure (B.length 'payload_bytes == SZ.v payload_total_len /\
                 B.length 'old == SZ.v total_len /\
                 SZ.v copy_len <= SZ.v payload_total_len /\
                 SZ.v offset + SZ.v copy_len <= SZ.v total_len)
  ensures exists* bytes.
          pts_to payload 'payload_bytes **
          pts_to out bytes **
          pure (B.length bytes == SZ.v total_len)
{
  copy_payload_to_output_loop payload payload_total_len out total_len 0sz offset copy_len
}

fn client_core_new ()
  returns c: client_core
  ensures is_client_core c CL.empty_connection_view
{
  let st = ST.alloc_initial ();
  let log = ST.alloc_initial_log ();
  let record_state = Rec.record_state_new ();
  let c = { state = st; log = log; client_application_record_state = record_state };
  rewrite (ST.current st S.initial) as (ST.current c.state CL.empty_connection_view.CL.state);
  rewrite (ST.log_current log CL.empty_connection_view) as (ST.log_current c.log CL.empty_connection_view);
  with record_s. rewrite (Rec.is_record_state record_state record_s) as (Rec.is_record_state c.client_application_record_state record_s);
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
  Rec.record_state_free c.client_application_record_state;
}

fn client_core_install_application_keys_runtime
  (c: client_core)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_client_core c 'view **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\ B.length 'iv_bytes == 12)
  ensures is_client_core c 'view **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_client_core c 'view);
  Rec.install_application_keys_runtime c.client_application_record_state key iv;
  assert (pure (CL.connection_view_consistent 'view));
  fold (is_client_core c 'view);
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
    if SZ.(app_in_len <=^ 4096sz) {
      let inner_len = SZ.(app_in_len +^ 1sz);
      let cipher_len = SZ.(inner_len +^ 16sz);
      let wire_len = SZ.(5sz +^ cipher_len);
      assert (pure (SZ.v cipher_len == SZ.v app_in_len + 17));
      assert (pure (SZ.v wire_len == SZ.v app_in_len + 22));
      assert (pure (SZ.v wire_len <= 4118));
      if SZ.(wire_len <=^ network_out_cap) {
        let mut header = [| 0uy; 5sz |];
        let mut inner_plaintext = [| 0uy; inner_len |];
        let mut cipher = [| 0uy; cipher_len |];
        RF.serialize_application_data_header
          (Cast.uint32_to_uint16 (SZ.sizet_to_uint32 cipher_len))
          header
          5sz;
        RF.encode_inner_plaintext_no_padding
          app_in
          app_in_len
          23uy
          inner_plaintext
          inner_len;
        with inner_bytes. assert (pts_to inner_plaintext inner_bytes);
        with cipher_old. assert (pts_to cipher cipher_old);
        RF.lemma_inner_plaintext_no_padding_result_len
          (Ghost.reveal 'app_in_bytes)
          (Seq.create (SZ.v inner_len) 0uy)
          (SZ.v app_in_len)
          (SZ.v inner_len)
          23uy;
        assert (pure (B.length inner_bytes == SZ.v inner_len));
        assert (pure (B.length cipher_old == SZ.v cipher_len));
        assert (pure (B.length cipher_old == SZ.v inner_len + 16));
        let sealed = Rec.seal_application_runtime
          c.client_application_record_state
          header
          5sz
          inner_plaintext
          inner_len
          cipher;
        with header_bytes. assert (pts_to header header_bytes);
        with cipher_bytes. assert (pts_to cipher cipher_bytes);
        assert (pure (B.length header_bytes == 5));
        assert (pure (B.length cipher_bytes == SZ.v cipher_len));
        if sealed {
          copy_payload_to_output header 5sz 5sz network_out network_out_cap 0sz;
          with network_after_header. assert (pts_to network_out network_after_header);
          assert (pure (B.length network_after_header == SZ.v network_out_cap));
          assert (pure (5 + SZ.v cipher_len == SZ.v wire_len));
          copy_payload_to_output cipher cipher_len cipher_len network_out network_out_cap 5sz;
          with network_out1. assert (pts_to network_out network_out1);
          assert (pure (B.length network_out1 == SZ.v network_out_cap));
          let raw : erased CL.raw_io_log =
            CL.append_raw_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v wire_len);
          CL.lemma_raw_io_log_extends_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v wire_len);
          CL.lemma_raw_io_log_same_received_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v wire_len);
          let raw_view : erased CL.connection_view = CL.sync_raw_state view0 (Ghost.reveal raw) view0.CL.state;
          CL.lemma_connection_view_consistent_sync_raw_same_state view0 (Ghost.reveal raw);
          assert (pure ((Ghost.reveal raw_view).CL.state == view0.CL.state));
          assert (pure ((Ghost.reveal raw_view).CL.app_view == view0.CL.app_view));
          assert (pure (CL.raw_io_log_extends view0.CL.raw_log (Ghost.reveal raw_view).CL.raw_log));
          assert (pure (CL.raw_io_log_same_received view0.CL.raw_log (Ghost.reveal raw_view).CL.raw_log));
          ST.advance c.state (S.SendApplicationData (Ghost.reveal app_bytes)) (S.advance_write_record view0.CL.state);
          let view1 : erased CL.connection_view =
            CL.note_app_sent (Ghost.reveal raw_view) (Ghost.reveal app_bytes) (S.advance_write_record view0.CL.state);
          CL.lemma_step_send_application_data_success
            view0
            (Ghost.reveal raw_view)
            (Ghost.reveal app_bytes)
            (S.advance_write_record view0.CL.state);
          ST.advance_log c.log (Ghost.reveal view1);
          let result = { network_out_len = wire_len; app_out_len = 0sz; status = CL.ActionComplete };
          let resp : erased CL.client_response =
            CL.response_with_sent_raw_delta view0.CL.raw_log (Ghost.reveal view1).CL.raw_log B.empty CL.ActionComplete;
          CL.lemma_raw_sent_delta_append_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v wire_len);
          assert (pure ((Ghost.reveal resp).CL.network_out == CL.raw_slice (Ghost.reveal network_out1) 0 (SZ.v wire_len)));
          assert (pure (CL.raw_slice (Ghost.reveal network_out1) 0 (SZ.v wire_len) ==
                        Seq.slice (Ghost.reveal network_out1) 0 (SZ.v wire_len)));
          lemma_prefix_slice (Ghost.reveal network_out1) (SZ.v wire_len);
          lemma_empty_prefix (Ghost.reveal 'app_out0);
          assert (pure (response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
          assert (pure (exists mresp. response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal 'app_out0) mresp /\
                                    CL.step view0 mreq (Ghost.reveal view1) mresp));
          fold (is_client_core c (Ghost.reveal view1));
          result
        } else {
          ST.advance_fail c.state T.IoError;
          let view1 : erased CL.connection_view =
            CL.note_local_fail view0 T.IoError (S.fail view0.CL.state T.IoError);
          CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
          assert (pure (CL.raw_io_log_same_received view0.CL.raw_log view0.CL.raw_log));
          CL.lemma_step_send_application_data_failed
            view0
            view0
            (Ghost.reveal app_bytes)
            T.IoError
            (S.fail view0.CL.state T.IoError);
          ST.advance_log c.log (Ghost.reveal view1);
          let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
          let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
          CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
          assert (pure (resp.CL.network_out == B.empty));
          lemma_empty_prefix (Ghost.reveal 'network_out0);
          lemma_empty_prefix (Ghost.reveal 'app_out0);
          assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
          assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                    CL.step view0 mreq (Ghost.reveal view1) mresp));
          fold (is_client_core c (Ghost.reveal view1));
          result
        }
      } else {
        ST.advance_fail c.state T.IoError;
        let view1 : erased CL.connection_view =
          CL.note_local_fail view0 T.IoError (S.fail view0.CL.state T.IoError);
        CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
        assert (pure (CL.raw_io_log_same_received view0.CL.raw_log view0.CL.raw_log));
        CL.lemma_step_send_application_data_failed
          view0
          view0
          (Ghost.reveal app_bytes)
          T.IoError
          (S.fail view0.CL.state T.IoError);
        ST.advance_log c.log (Ghost.reveal view1);
        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
        let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
        CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
        assert (pure (resp.CL.network_out == B.empty));
        lemma_empty_prefix (Ghost.reveal 'network_out0);
        lemma_empty_prefix (Ghost.reveal 'app_out0);
        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                  CL.step view0 mreq (Ghost.reveal view1) mresp));
        fold (is_client_core c (Ghost.reveal view1));
        result
      }
    } else {
      ST.advance_fail c.state T.IoError;
      let view1 : erased CL.connection_view =
        CL.note_local_fail view0 T.IoError (S.fail view0.CL.state T.IoError);
      CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
      assert (pure (CL.raw_io_log_same_received view0.CL.raw_log view0.CL.raw_log));
      CL.lemma_step_send_application_data_failed
        view0
        view0
        (Ghost.reveal app_bytes)
        T.IoError
        (S.fail view0.CL.state T.IoError);
      ST.advance_log c.log (Ghost.reveal view1);
      let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
      let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
      CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
      assert (pure (resp.CL.network_out == B.empty));
      lemma_empty_prefix (Ghost.reveal 'network_out0);
      lemma_empty_prefix (Ghost.reveal 'app_out0);
      assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                CL.step view0 mreq (Ghost.reveal view1) mresp));
      fold (is_client_core c (Ghost.reveal view1));
      result
    }
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
    if SZ.(24sz <=^ network_out_cap) {
      let mut header = [| 0uy; 5sz |];
      let mut inner_plaintext = [| 0uy; 3sz |];
      let mut cipher = [| 0uy; 19sz |];
      RF.serialize_application_data_header
        (Cast.uint32_to_uint16 (SZ.sizet_to_uint32 19sz))
        header
        5sz;
      inner_plaintext.(0sz) <- 1uy;
      inner_plaintext.(1sz) <- 0uy;
      inner_plaintext.(2sz) <- 21uy;
      with inner_bytes. assert (pts_to inner_plaintext inner_bytes);
      with cipher_old. assert (pts_to cipher cipher_old);
      assert (pure (B.length inner_bytes == 3));
      assert (pure (B.length cipher_old == 19));
      assert (pure (B.length cipher_old == 3 + 16));
      let sealed = Rec.seal_application_runtime
        c.client_application_record_state
        header
        5sz
        inner_plaintext
        3sz
        cipher;
      with header_bytes. assert (pts_to header header_bytes);
      with cipher_bytes. assert (pts_to cipher cipher_bytes);
      assert (pure (B.length header_bytes == 5));
      assert (pure (B.length cipher_bytes == 19));
      if sealed {
        copy_payload_to_output header 5sz 5sz network_out network_out_cap 0sz;
        with network_after_header. assert (pts_to network_out network_after_header);
        assert (pure (B.length network_after_header == SZ.v network_out_cap));
        copy_payload_to_output cipher 19sz 19sz network_out network_out_cap 5sz;
        with network_out1. assert (pts_to network_out network_out1);
        assert (pure (B.length network_out1 == SZ.v network_out_cap));
        let raw : erased CL.raw_io_log =
          CL.append_raw_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 24;
        CL.lemma_raw_io_log_extends_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 24;
        CL.lemma_raw_io_log_same_received_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 24;
        let raw_view : erased CL.connection_view = CL.sync_raw_state view0 (Ghost.reveal raw) view0.CL.state;
        CL.lemma_connection_view_consistent_sync_raw_same_state view0 (Ghost.reveal raw);
        assert (pure ((Ghost.reveal raw_view).CL.state == view0.CL.state));
        assert (pure ((Ghost.reveal raw_view).CL.app_view == view0.CL.app_view));
        assert (pure (CL.raw_io_log_extends view0.CL.raw_log (Ghost.reveal raw_view).CL.raw_log));
        assert (pure (CL.raw_io_log_same_received view0.CL.raw_log (Ghost.reveal raw_view).CL.raw_log));
        ST.advance c.state S.SendCloseNotify (S.send_close_state view0.CL.state);
        let view1 : erased CL.connection_view =
          CL.note_send_close_notify (Ghost.reveal raw_view) (S.send_close_state view0.CL.state);
        CL.lemma_step_close_success view0 (Ghost.reveal raw_view) (S.send_close_state view0.CL.state);
        ST.advance_log c.log (Ghost.reveal view1);
        let result = { network_out_len = 24sz; app_out_len = 0sz; status = CL.Closed };
        let resp : erased CL.client_response =
          CL.response_with_sent_raw_delta view0.CL.raw_log (Ghost.reveal view1).CL.raw_log B.empty CL.Closed;
        CL.lemma_raw_sent_delta_append_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 24;
        assert (pure ((Ghost.reveal resp).CL.network_out == CL.raw_slice (Ghost.reveal network_out1) 0 24));
        assert (pure (CL.raw_slice (Ghost.reveal network_out1) 0 24 ==
                      Seq.slice (Ghost.reveal network_out1) 0 24));
        lemma_prefix_slice (Ghost.reveal network_out1) 24;
        lemma_empty_prefix (Ghost.reveal 'app_out0);
        assert (pure (response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal 'app_out0) mresp /\
                                  CL.step view0 mreq (Ghost.reveal view1) mresp));
        fold (is_client_core c (Ghost.reveal view1));
        result
      } else {
        ST.advance_fail c.state T.IoError;
        let view1 : erased CL.connection_view =
          CL.note_local_fail view0 T.IoError (S.fail view0.CL.state T.IoError);
        CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
        assert (pure (CL.raw_io_log_same_received view0.CL.raw_log view0.CL.raw_log));
        CL.lemma_step_close_failed
          view0
          view0
          T.IoError
          (S.fail view0.CL.state T.IoError);
        ST.advance_log c.log (Ghost.reveal view1);
        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
        let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
        CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
        assert (pure (resp.CL.network_out == B.empty));
        lemma_empty_prefix (Ghost.reveal 'network_out0);
        lemma_empty_prefix (Ghost.reveal 'app_out0);
        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                  CL.step view0 mreq (Ghost.reveal view1) mresp));
        fold (is_client_core c (Ghost.reveal view1));
        result
      }
    } else {
      ST.advance_fail c.state T.IoError;
      let view1 : erased CL.connection_view =
        CL.note_local_fail view0 T.IoError (S.fail view0.CL.state T.IoError);
      CL.lemma_raw_io_log_extends_refl view0.CL.raw_log;
      assert (pure (CL.raw_io_log_same_received view0.CL.raw_log view0.CL.raw_log));
      CL.lemma_step_close_failed
        view0
        view0
        T.IoError
        (S.fail view0.CL.state T.IoError);
      ST.advance_log c.log (Ghost.reveal view1);
      let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
      let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
      CL.lemma_raw_sent_delta_refl view0.CL.raw_log;
      assert (pure (resp.CL.network_out == B.empty));
      lemma_empty_prefix (Ghost.reveal 'network_out0);
      lemma_empty_prefix (Ghost.reveal 'app_out0);
      assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                CL.step view0 mreq (Ghost.reveal view1) mresp));
      fold (is_client_core c (Ghost.reveal view1));
      result
    }
  }
}
