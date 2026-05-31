module TLS13.Connection.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module Cast = FStar.Int.Cast
module CL = TLS13.ConnectionLog
module Rec = TLS13.Record
module R = TLS13.Record.Spec
module RF = TLS13.Record.Framing
module Seq = FStar.Seq
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

let tls_application_plaintext_max : SZ.t = 16384sz
let tls_ciphertext_fragment_max : SZ.t = 16640sz
let tls_application_record_wire_max : SZ.t = 16645sz
let max_self_emitted_application_record_wire_len : SZ.t = 16406sz

let pending_read_buffer_capacity : SZ.t = tls_application_plaintext_max
let pending_network_buffer_capacity : SZ.t =
  SZ.(tls_application_record_wire_max +^ tls_application_record_wire_max)

let record_states_match_view
  (client_s:R.direction_state)
  (server_s:R.direction_state)
  (view:CL.connection_view)
  : prop =
  // Error paths can consume a concrete record before transitioning to Failed.
  view.CL.state.S.phase == S.Failed \/
  (client_s.R.seq == view.CL.state.S.write_state.R.seq /\
   server_s.R.seq == view.CL.state.S.read_state.R.seq)

let lemma_nat_add_sub_cancel
  (a:nat)
  (b:nat)
  (c:nat{b <= c})
  : Lemma (a + b + (c - b) == a + c)
=
  ()

noeq
type client_core = {
  state: ST.state_ref;
  log: ST.log_ref;
  client_application_record_state: Rec.record_state;
  server_application_record_state: Rec.record_state;
  pending_read_buffer: V.vec U8.t;
  pending_read_offset: box SZ.t;
  pending_read_len: box SZ.t;
  pending_network_buffer: V.vec U8.t;
  pending_network_len: box SZ.t;
}

let is_client_core (c:client_core) (view:CL.connection_view) : slprop =
  exists* client_record_s server_record_s
          pending_read_buffer pending_read_offset pending_read_len
          pending_network_buffer pending_network_len.
    ST.current c.state view.CL.state **
    ST.log_current c.log view **
    Rec.is_record_state c.client_application_record_state client_record_s **
    Rec.is_record_state c.server_application_record_state server_record_s **
    V.pts_to c.pending_read_buffer pending_read_buffer **
    Box.pts_to c.pending_read_offset pending_read_offset **
    Box.pts_to c.pending_read_len pending_read_len **
    V.pts_to c.pending_network_buffer pending_network_buffer **
    Box.pts_to c.pending_network_len pending_network_len **
    pure (CL.connection_view_consistent view /\
          V.is_full_vec c.pending_read_buffer /\
          V.length c.pending_read_buffer == SZ.v pending_read_buffer_capacity /\
          SZ.v pending_read_offset <= SZ.v pending_read_len /\
          SZ.v pending_read_len <= SZ.v pending_read_buffer_capacity /\
          Seq.equal view.CL.pending_app
            (CL.raw_slice pending_read_buffer (SZ.v pending_read_offset) (SZ.v pending_read_len)) /\
          V.is_full_vec c.pending_network_buffer /\
          V.length c.pending_network_buffer == SZ.v pending_network_buffer_capacity /\
          SZ.v pending_network_len <= SZ.v pending_network_buffer_capacity /\
          Seq.equal view.CL.pending_received_raw
            (CL.raw_slice pending_network_buffer 0 (SZ.v pending_network_len)) /\
          record_states_match_view client_record_s server_record_s view)

let received_alert_event (alert:T.alert_description) : CL.host_event =
  CL.NetworkEvent { CL.message_direction = CL.Received; CL.message_value = CL.TlsAlert alert }

let alert_description_of_u8 (b:U8.t) : T.alert_description =
  if b = 10uy then
    T.UnexpectedMessage
  else if b = 20uy then
    T.BadRecordMac
  else if b = 40uy then
    T.HandshakeFailure
  else if b = 51uy then
    T.DecryptError
  else if b = 70uy then
    T.ProtocolVersion
  else if b = 110uy then
    T.UnsupportedExtension
  else if b = 46uy then
    T.CertificateUnknown
  else if b = 47uy then
    T.IllegalParameter
  else
    T.DecodeError

let lemma_alert_description_of_u8_not_close (b:U8.t)
  : Lemma (alert_description_of_u8 b <> T.CloseNotify)
  =
  ()

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
  let client_record_state = Rec.record_state_new ();
  let server_record_state = Rec.record_state_new ();
  let pending_read_buffer = V.alloc 0uy pending_read_buffer_capacity;
  let pending_read_offset = Box.alloc 0sz;
  let pending_read_len = Box.alloc 0sz;
  let pending_network_buffer = V.alloc 0uy pending_network_buffer_capacity;
  let pending_network_len = Box.alloc 0sz;
  let c = {
    state = st;
    log = log;
    client_application_record_state = client_record_state;
    server_application_record_state = server_record_state;
    pending_read_buffer = pending_read_buffer;
    pending_read_offset = pending_read_offset;
    pending_read_len = pending_read_len;
    pending_network_buffer = pending_network_buffer;
    pending_network_len = pending_network_len;
  };
  rewrite (ST.current st S.initial) as (ST.current c.state CL.empty_connection_view.CL.state);
  rewrite (ST.log_current log CL.empty_connection_view) as (ST.log_current c.log CL.empty_connection_view);
  with client_record_s. rewrite (Rec.is_record_state client_record_state client_record_s) as (Rec.is_record_state c.client_application_record_state client_record_s);
  with server_record_s. rewrite (Rec.is_record_state server_record_state server_record_s) as (Rec.is_record_state c.server_application_record_state server_record_s);
  with pending_s. assert (V.pts_to pending_read_buffer pending_s);
  rewrite (V.pts_to pending_read_buffer pending_s) as (V.pts_to c.pending_read_buffer pending_s);
  lemma_empty_prefix pending_s;
  with pending_offset_s. rewrite (Box.pts_to pending_read_offset pending_offset_s) as (Box.pts_to c.pending_read_offset pending_offset_s);
  with pending_len_s. rewrite (Box.pts_to pending_read_len pending_len_s) as (Box.pts_to c.pending_read_len pending_len_s);
  with pending_network_s. assert (V.pts_to pending_network_buffer pending_network_s);
  rewrite (V.pts_to pending_network_buffer pending_network_s) as (V.pts_to c.pending_network_buffer pending_network_s);
  lemma_empty_prefix pending_network_s;
  with pending_network_len_s. rewrite (Box.pts_to pending_network_len pending_network_len_s) as (Box.pts_to c.pending_network_len pending_network_len_s);
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
  Rec.record_state_free c.server_application_record_state;
  V.free c.pending_read_buffer;
  Box.free c.pending_read_offset;
  Box.free c.pending_read_len;
  V.free c.pending_network_buffer;
  Box.free c.pending_network_len;
}

fn client_core_install_application_keys_runtime
  (c: client_core)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_client_core c 'view **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'iv_bytes == 12 /\
                 'view.CL.state.S.write_state.R.seq == 0)
  ensures is_client_core c 'view **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_client_core c 'view);
  Rec.install_application_keys_runtime c.client_application_record_state key iv;
  assert (pure (CL.connection_view_consistent 'view));
  fold (is_client_core c 'view);
}

fn client_core_install_peer_application_keys_runtime
  (c: client_core)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_client_core c 'view **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'iv_bytes == 12 /\
                 'view.CL.state.S.read_state.R.seq == 0)
  ensures is_client_core c 'view **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_client_core c 'view);
  Rec.install_application_keys_runtime c.server_application_record_state key iv;
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
    request_record_sequence_fits kind view0 (Ghost.reveal 'app_in_bytes) /\
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
    if SZ.(app_in_len <=^ tls_application_plaintext_max) {
      let inner_len = SZ.(app_in_len +^ 1sz);
      let cipher_len = SZ.(inner_len +^ 16sz);
      let wire_len = SZ.(5sz +^ cipher_len);
      assert (pure (SZ.v cipher_len == SZ.v app_in_len + 17));
      assert (pure (SZ.v wire_len == SZ.v app_in_len + 22));
      assert (pure (SZ.v wire_len <= SZ.v max_self_emitted_application_record_wire_len));
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
          assert (pure (S.max_application_data_fragment_len == SZ.v tls_application_plaintext_max));
          assert (pure (B.length (Ghost.reveal app_bytes) <= S.max_application_data_fragment_len));
          S.lemma_application_data_record_count_len_small (B.length (Ghost.reveal app_bytes));
          S.lemma_advance_write_records_one view0.CL.state;
          assert (pure (S.advance_write_records view0.CL.state (S.application_data_record_count (Ghost.reveal app_bytes)) ==
                        S.advance_write_record view0.CL.state));
          let send_state : erased S.conn_state =
            S.advance_write_records view0.CL.state (S.application_data_record_count (Ghost.reveal app_bytes));
          ST.advance c.state (S.SendApplicationData (Ghost.reveal app_bytes)) (Ghost.reveal send_state);
          let view1 : erased CL.connection_view =
            CL.note_app_sent (Ghost.reveal raw_view) (Ghost.reveal app_bytes) (Ghost.reveal send_state);
          CL.lemma_step_send_application_data_success
            view0
            (Ghost.reveal raw_view)
            (Ghost.reveal app_bytes)
            (Ghost.reveal send_state);
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
    let network_bytes : erased B.bytes = Ghost.reveal 'network_in_bytes;
    assert (pure (mreq == CL.request_with_network_in (CL.OpReadApplicationData (SZ.v requested_app_len)) (Ghost.reveal network_bytes)));
    let raw : erased CL.raw_io_log =
      CL.append_raw_received view0.CL.raw_log (Ghost.reveal network_bytes);
    CL.lemma_raw_io_log_extends_received view0.CL.raw_log (Ghost.reveal network_bytes);
    assert (pure (CL.raw_io_log_same_sent view0.CL.raw_log (Ghost.reveal raw)));
    let view1 : erased CL.connection_view =
      CL.sync_raw_state view0 (Ghost.reveal raw) view0.CL.state;
    CL.lemma_connection_view_consistent_sync_raw_same_state view0 (Ghost.reveal raw);
    assert (pure ((Ghost.reveal view1).CL.state == view0.CL.state));
    assert (pure ((Ghost.reveal view1).CL.app_view == view0.CL.app_view));
    assert (pure (CL.raw_io_log_extends view0.CL.raw_log (Ghost.reveal view1).CL.raw_log));
    assert (pure (CL.raw_io_log_same_sent view0.CL.raw_log (Ghost.reveal view1).CL.raw_log));
    let pending_read_offset = !c.pending_read_offset;
    let pending_read_len = !c.pending_read_len;
    assert (pure (SZ.v pending_read_offset <= SZ.v pending_read_len));
    if SZ.(pending_read_offset <^ pending_read_len) {
      let pending_available_refined = SZ.(pending_read_len -^ pending_read_offset);
      let pending_available : SZ.t = pending_available_refined;
      let output_limit : SZ.t =
        if SZ.(requested_app_len <^ app_out_cap) {
          requested_app_len
        } else {
          app_out_cap
        };
      let copy_len =
        if SZ.(output_limit <^ pending_available) {
          output_limit
        } else {
          pending_available
        };
      if (copy_len = 0sz) {
        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.NeedNetworkInput };
        let resp = CL.response_no_network_out B.empty CL.NeedNetworkInput;
        CL.lemma_append_empty_right view0.CL.raw_log.CL.raw_sent;
        assert (pure ((Ghost.reveal view1).CL.raw_log == CL.step_raw_log view0.CL.raw_log mreq resp));
        assert (pure ((Ghost.reveal view1).CL.app_view == CL.step_app_log view0.CL.app_view mreq resp));
        CL.lemma_connection_view_single_step_for_core_step view0 mreq (Ghost.reveal view1) resp;
        assert (pure (CL.step view0 mreq (Ghost.reveal view1) resp));
        ST.advance_log c.log (Ghost.reveal view1);
        lemma_empty_prefix (Ghost.reveal 'network_out0);
        lemma_empty_prefix (Ghost.reveal 'app_out0);
        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                  CL.step view0 mreq (Ghost.reveal view1) mresp));
        fold (is_client_core c (Ghost.reveal view1));
        result
      } else {
        assert (pure (SZ.v copy_len > 0));
        assert (pure (SZ.v copy_len <= SZ.v pending_available));
        assert (pure (SZ.v pending_read_offset + SZ.v copy_len <= SZ.v pending_read_len));
        assert (pure (SZ.v pending_read_offset + SZ.v copy_len <= SZ.v pending_read_buffer_capacity));
        assert (pure (SZ.v copy_len <= SZ.v app_out_cap));
        V.pts_to_len c.pending_read_buffer;
        V.to_array_pts_to c.pending_read_buffer;
        copy_payload_to_output_loop
          (V.vec_to_array c.pending_read_buffer)
          pending_read_buffer_capacity
          app_out
          app_out_cap
          pending_read_offset
          0sz
          copy_len;
        V.to_vec_pts_to c.pending_read_buffer;
        with pending_buffer1. assert (V.pts_to c.pending_read_buffer pending_buffer1);
        let pending_read_offset' = SZ.(pending_read_offset +^ copy_len);
        assert (pure (SZ.v pending_read_offset' <= SZ.v pending_read_len));
        c.pending_read_offset := pending_read_offset';
        with app_out1. assert (pts_to app_out app_out1);
        assert (pure (B.length app_out1 == SZ.v app_out_cap));
        let app_payload : erased B.bytes =
          Seq.slice (Ghost.reveal app_out1) 0 (SZ.v copy_len);
        let pending_payload : erased B.bytes =
          CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset')
            (SZ.v pending_read_len);
        let view2 : erased CL.connection_view =
          CL.note_app_delivered_with_pending
            (Ghost.reveal view1)
            (Ghost.reveal app_payload)
            (Ghost.reveal pending_payload);
        CL.lemma_step_read_application_data_delivered_with_pending
          view0
          (Ghost.reveal view1)
          (SZ.v requested_app_len)
          (Ghost.reveal app_payload)
          (Ghost.reveal pending_payload);
        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
        ST.advance_log c.log (Ghost.reveal view2);
        let result = { network_out_len = 0sz; app_out_len = copy_len; status = CL.ApplicationDataReady };
        let resp : erased CL.client_response =
          CL.response_no_network_out (Ghost.reveal app_payload) CL.ApplicationDataReady;
        lemma_empty_prefix (Ghost.reveal 'network_out0);
        lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v copy_len);
        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp)));
        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
        fold (is_client_core c (Ghost.reveal view2));
        result
      }
    } else {
      let pending_network_len = !c.pending_network_len;
      assert (pure (SZ.v pending_network_len <= SZ.v pending_network_buffer_capacity));
      if SZ.(0sz <^ pending_network_len) {
        let remaining_pending_cap = SZ.(pending_network_buffer_capacity -^ pending_network_len);
        assert (pure (SZ.v pending_network_len + SZ.v remaining_pending_cap == SZ.v pending_network_buffer_capacity));
        if SZ.(network_in_len <=^ remaining_pending_cap) {
          V.pts_to_len c.pending_network_buffer;
          V.to_array_pts_to c.pending_network_buffer;
          copy_payload_to_output_loop
            network_in
            network_in_len
            (V.vec_to_array c.pending_network_buffer)
            pending_network_buffer_capacity
            0sz
            pending_network_len
            network_in_len;
          V.to_vec_pts_to c.pending_network_buffer;
          with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
          let pending_network_len' = SZ.(pending_network_len +^ network_in_len);
          assert (pure (SZ.v pending_network_len' <= SZ.v pending_network_buffer_capacity));
          c.pending_network_len := pending_network_len';
          if SZ.(5sz <=^ pending_network_len') {
            let mut header = [| 0uy; 5sz |];
            V.to_array_pts_to c.pending_network_buffer;
            copy_payload_to_output
              (V.vec_to_array c.pending_network_buffer)
              pending_network_buffer_capacity
              5sz
              header
              5sz
              0sz;
            with header_bytes. assert (pts_to header header_bytes);
            assert (pure (B.length header_bytes == 5));
            let mut content_type_out = [| 0uy; 1sz |];
            let mut fragment_len_out = [| 0uy; 2sz |];
            let header_parse_ok =
              RF.parse_record_header header 5sz content_type_out 1sz fragment_len_out 2sz;
            if header_parse_ok {
              let content_type = content_type_out.(0sz);
              let frag_hi = fragment_len_out.(0sz);
              let frag_lo = fragment_len_out.(1sz);
              let frag_hi16 = Cast.uint8_to_uint16 frag_hi;
              let frag_lo16 = Cast.uint8_to_uint16 frag_lo;
              let frag16 = U16.logor (U16.shift_left frag_hi16 8ul) frag_lo16;
              let fragment_len = SZ.uint16_to_sizet frag16;
              let remaining_pending_len = SZ.(pending_network_len' -^ 5sz);
              assert (pure (SZ.v remaining_pending_len == SZ.v pending_network_len' - 5));
              if not (SZ.(fragment_len <=^ remaining_pending_len)) {
                V.to_vec_pts_to c.pending_network_buffer;
                with pending_network_buffer2. assert (V.pts_to c.pending_network_buffer pending_network_buffer2);
                let pending_payload : erased B.bytes =
                  CL.raw_slice
                    (Ghost.reveal pending_network_buffer2)
                    0
                    (SZ.v pending_network_len');
                let view2 : erased CL.connection_view =
                  CL.with_pending_received_raw
                    (Ghost.reveal view1)
                    (Ghost.reveal pending_payload);
                CL.lemma_step_read_need_network_input_with_pending
                  view0
                  (Ghost.reveal view1)
                  (SZ.v requested_app_len)
                  (Ghost.reveal pending_payload);
                CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                ST.advance_log c.log (Ghost.reveal view2);
                let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.NeedNetworkInput };
                let resp = CL.response_no_network_out B.empty CL.NeedNetworkInput;
                lemma_empty_prefix (Ghost.reveal 'network_out0);
                lemma_empty_prefix (Ghost.reveal 'app_out0);
                assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
                assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                          CL.step view0 mreq (Ghost.reveal view2) mresp));
                fold (is_client_core c (Ghost.reveal view2));
                result
              } else {
                assert (pure (SZ.v fragment_len <= SZ.v remaining_pending_len));
                assert (pure (SZ.v remaining_pending_len == SZ.v pending_network_len' - 5));
                assert (pure (5 + SZ.v fragment_len <= SZ.v pending_network_len'));
                let record_wire_len = SZ.(5sz +^ fragment_len);
                assert (pure (SZ.v record_wire_len == 5 + SZ.v fragment_len));
                assert (pure (SZ.v record_wire_len <= SZ.v pending_network_len'));
                assert (pure (SZ.v record_wire_len <= SZ.v pending_network_buffer_capacity));
                let residual_len = SZ.(pending_network_len' -^ record_wire_len);
                assert (pure (SZ.v residual_len == SZ.v pending_network_len' - SZ.v record_wire_len));
                lemma_nat_add_sub_cancel 0 (SZ.v record_wire_len) (SZ.v pending_network_len');
                assert (pure (SZ.v record_wire_len + SZ.v residual_len == SZ.v pending_network_len'));
                assert (pure (SZ.v residual_len <= SZ.v pending_network_buffer_capacity));
                assert (pure (SZ.v record_wire_len + SZ.v residual_len <= SZ.v pending_network_buffer_capacity));
                let mut record_tmp = [| 0uy; record_wire_len |];
                copy_payload_to_output_loop
                  (V.vec_to_array c.pending_network_buffer)
                  pending_network_buffer_capacity
                  record_tmp
                  record_wire_len
                  0sz
                  0sz
                  record_wire_len;
                with record_tmp_bytes. assert (pts_to record_tmp record_tmp_bytes);
                assert (pure (B.length record_tmp_bytes == SZ.v record_wire_len));
                let mut residual_tmp = [| 0uy; residual_len |];
                copy_payload_to_output_loop
                  (V.vec_to_array c.pending_network_buffer)
                  pending_network_buffer_capacity
                  residual_tmp
                  residual_len
                  record_wire_len
                  0sz
                  residual_len;
                with residual_tmp_bytes. assert (pts_to residual_tmp residual_tmp_bytes);
                assert (pure (B.length residual_tmp_bytes == SZ.v residual_len));
                copy_payload_to_output_loop
                  residual_tmp
                  residual_len
                  (V.vec_to_array c.pending_network_buffer)
                  pending_network_buffer_capacity
                  0sz
                  0sz
                  residual_len;
                V.to_vec_pts_to c.pending_network_buffer;
                with pending_network_buffer2. assert (V.pts_to c.pending_network_buffer pending_network_buffer2);
                c.pending_network_len := residual_len;
                let pending_raw_payload : erased B.bytes =
                  CL.raw_slice
                    (Ghost.reveal pending_network_buffer2)
                    0
                    (SZ.v residual_len);
                if not (content_type = 23uy) {
                  ST.advance_fail c.state T.IoError;
                  let base_view2 : erased CL.connection_view =
                    CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw
                      (Ghost.reveal base_view2)
                      (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_read_failed
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    T.IoError
                    (S.fail view0.CL.state T.IoError);
                  let resp : erased CL.client_response =
                    CL.response_no_network_out B.empty (CL.Failed T.IoError);
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    (Ghost.reveal resp)
                    (Ghost.reveal pending_raw_payload);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_empty_prefix (Ghost.reveal 'app_out0);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
              } else if not (SZ.(16sz <^ fragment_len)) {
                ST.advance_fail c.state T.IoError;
                let base_view2 : erased CL.connection_view =
                  CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                let view2 : erased CL.connection_view =
                  CL.with_pending_received_raw
                    (Ghost.reveal base_view2)
                    (Ghost.reveal pending_raw_payload);
                CL.lemma_step_read_failed
                  view0
                  (Ghost.reveal view1)
                  (SZ.v requested_app_len)
                  T.IoError
                  (S.fail view0.CL.state T.IoError);
                let resp : erased CL.client_response =
                  CL.response_no_network_out B.empty (CL.Failed T.IoError);
                CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                CL.lemma_step_with_pending_received_raw
                  view0
                  mreq
                  (Ghost.reveal base_view2)
                  (Ghost.reveal resp)
                  (Ghost.reveal pending_raw_payload);
                assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                ST.advance_log c.log (Ghost.reveal view2);
                let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                lemma_empty_prefix (Ghost.reveal 'network_out0);
                lemma_empty_prefix (Ghost.reveal 'app_out0);
                assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                          CL.step view0 mreq (Ghost.reveal view2) mresp));
                fold (is_client_core c (Ghost.reveal view2));
                result
              } else {
                assert (pure (5 + SZ.v fragment_len <= SZ.v record_wire_len));
                let mut cipher = [| 0uy; fragment_len |];
                copy_payload_to_output_loop
                  record_tmp
                  record_wire_len
                  cipher
                  fragment_len
                  5sz
                  0sz
                  fragment_len;
                with cipher_bytes. assert (pts_to cipher cipher_bytes);
                assert (pure (B.length cipher_bytes == SZ.v fragment_len));
                assert (pure (not (not (SZ.(16sz <^ fragment_len)))));
                let fragment_len_has_tag = SZ.lt 16sz fragment_len;
                assert (pure (fragment_len_has_tag == SZ.(16sz <^ fragment_len)));
                assert (pure (fragment_len_has_tag == true));
                assert (pure (fragment_len_has_tag == (SZ.v 16sz < SZ.v fragment_len)));
                assert (pure (SZ.v 16sz == 16));
                assert (pure (16 < SZ.v fragment_len));
                assert (pure (16 <= SZ.v fragment_len));
                let inner_len = SZ.(fragment_len -^ 16sz);
                assert (pure (SZ.v inner_len > 0));
                let mut inner = [| 0uy; inner_len |];
                with inner_old. assert (pts_to inner inner_old);
                assert (pure (B.length inner_old == SZ.v inner_len));
                assert (pure (B.length inner_old + 16 == SZ.v fragment_len));
                let opened =
                  Rec.open_application_runtime
                    c.server_application_record_state
                    header
                    5sz
                    cipher
                    fragment_len
                    inner;
                if opened {
                  let mut inner_content_type_out = [| 0uy; 1sz |];
                  let payload_len =
                    RF.decode_inner_plaintext inner inner_len inner_content_type_out 1sz;
                  let inner_content_type = inner_content_type_out.(0sz);
                  if (inner_content_type = 23uy) {
                    if (SZ.(payload_len <=^ requested_app_len) && SZ.(payload_len <=^ app_out_cap)) {
                      copy_payload_to_output inner inner_len payload_len app_out app_out_cap 0sz;
                      with app_out1. assert (pts_to app_out app_out1);
                      assert (pure (B.length app_out1 == SZ.v app_out_cap));
                      let app_payload : erased B.bytes =
                        Seq.slice (Ghost.reveal app_out1) 0 (SZ.v payload_len);
                      ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                      let base_view2 : erased CL.connection_view =
                        CL.note_app_received_with_pending
                          (Ghost.reveal view1)
                          (Ghost.reveal app_payload)
                          B.empty
                          (S.advance_read_record view0.CL.state);
                      CL.lemma_step_read_application_data_success_with_pending
                        view0
                        (Ghost.reveal view1)
                        (SZ.v requested_app_len)
                        (Ghost.reveal app_payload)
                        B.empty
                        (S.advance_read_record view0.CL.state);
                      let resp : erased CL.client_response =
                        CL.response_no_network_out (Ghost.reveal app_payload) CL.ApplicationDataReady;
                      CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                      assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                      assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                      let view2 : erased CL.connection_view =
                        CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                      CL.lemma_step_with_pending_received_raw
                        view0
                        mreq
                        (Ghost.reveal base_view2)
                        (Ghost.reveal resp)
                        (Ghost.reveal pending_raw_payload);
                      assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                      ST.advance_log c.log (Ghost.reveal view2);
                      let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                      lemma_empty_prefix (Ghost.reveal 'network_out0);
                      lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                      assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp)));
                      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                CL.step view0 mreq (Ghost.reveal view2) mresp));
                      fold (is_client_core c (Ghost.reveal view2));
                      result
                    } else {
                      let output_limit : SZ.t =
                        if SZ.(requested_app_len <^ app_out_cap) {
                          requested_app_len
                        } else {
                          app_out_cap
                        };
                      if (SZ.(0sz <^ output_limit) &&
                          SZ.(output_limit <^ payload_len) &&
                          SZ.(payload_len <=^ pending_read_buffer_capacity)) {
                        assert (pure (SZ.v output_limit <= SZ.v app_out_cap));
                        assert (pure (SZ.v output_limit <= SZ.v payload_len));
                        copy_payload_to_output inner inner_len output_limit app_out app_out_cap 0sz;
                        with app_out1. assert (pts_to app_out app_out1);
                        assert (pure (B.length app_out1 == SZ.v app_out_cap));
                        let leftover_len = SZ.(payload_len -^ output_limit);
                        assert (pure (SZ.v leftover_len == SZ.v payload_len - SZ.v output_limit));
                        assert (pure (SZ.v leftover_len > 0));
                        assert (pure (SZ.v leftover_len <= SZ.v pending_read_buffer_capacity));
                        lemma_nat_add_sub_cancel
                          0
                          (SZ.v output_limit)
                          (SZ.v payload_len);
                        assert (pure (0 + SZ.v output_limit + (SZ.v payload_len - SZ.v output_limit) ==
                                      0 + SZ.v payload_len));
                        assert (pure (SZ.v output_limit + SZ.v leftover_len ==
                                      0 + SZ.v output_limit + (SZ.v payload_len - SZ.v output_limit)));
                        assert (pure (SZ.v output_limit + SZ.v leftover_len == 0 + SZ.v payload_len));
                        assert (pure (SZ.v payload_len <= SZ.v inner_len));
                        assert (pure (SZ.v output_limit + SZ.v leftover_len <= SZ.v inner_len));
                        pts_to_len inner;
                        with inner_bytes. assert (pts_to inner inner_bytes);
                        assert (pure (B.length inner_bytes == SZ.v inner_len));
                        V.pts_to_len c.pending_read_buffer;
                        V.to_array_pts_to c.pending_read_buffer;
                        copy_payload_to_output_loop
                          inner
                          inner_len
                          (V.vec_to_array c.pending_read_buffer)
                          pending_read_buffer_capacity
                          output_limit
                          0sz
                          leftover_len;
                        V.to_vec_pts_to c.pending_read_buffer;
                        with pending_buffer1. assert (V.pts_to c.pending_read_buffer pending_buffer1);
                        c.pending_read_offset := 0sz;
                        c.pending_read_len := leftover_len;
                        let app_payload : erased B.bytes =
                          Seq.slice (Ghost.reveal app_out1) 0 (SZ.v output_limit);
                        let pending_payload : erased B.bytes =
                          CL.raw_slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len);
                        ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                        let base_view2 : erased CL.connection_view =
                          CL.note_app_received_with_pending
                            (Ghost.reveal view1)
                            (Ghost.reveal app_payload)
                            (Ghost.reveal pending_payload)
                            (S.advance_read_record view0.CL.state);
                        CL.lemma_step_read_application_data_success_with_pending
                          view0
                          (Ghost.reveal view1)
                          (SZ.v requested_app_len)
                          (Ghost.reveal app_payload)
                          (Ghost.reveal pending_payload)
                          (S.advance_read_record view0.CL.state);
                        let resp : erased CL.client_response =
                          CL.response_no_network_out (Ghost.reveal app_payload) CL.ApplicationDataReady;
                        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                        assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                        let view2 : erased CL.connection_view =
                          CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                        CL.lemma_step_with_pending_received_raw
                          view0
                          mreq
                          (Ghost.reveal base_view2)
                          (Ghost.reveal resp)
                          (Ghost.reveal pending_raw_payload);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                        ST.advance_log c.log (Ghost.reveal view2);
                        let result = { network_out_len = 0sz; app_out_len = output_limit; status = CL.ApplicationDataReady };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v output_limit);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
                        fold (is_client_core c (Ghost.reveal view2));
                        result
                      } else {
                        ST.advance_fail c.state T.IoError;
                        let base_view2 : erased CL.connection_view =
                          CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                        CL.lemma_step_read_failed
                          view0
                          (Ghost.reveal view1)
                          (SZ.v requested_app_len)
                          T.IoError
                          (S.fail view0.CL.state T.IoError);
                        let resp : erased CL.client_response =
                          CL.response_no_network_out B.empty (CL.Failed T.IoError);
                        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                        assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                        let view2 : erased CL.connection_view =
                          CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                        CL.lemma_step_with_pending_received_raw
                          view0
                          mreq
                          (Ghost.reveal base_view2)
                          (Ghost.reveal resp)
                          (Ghost.reveal pending_raw_payload);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                        ST.advance_log c.log (Ghost.reveal view2);
                        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_empty_prefix (Ghost.reveal 'app_out0);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
                        fold (is_client_core c (Ghost.reveal view2));
                        result
                      }
                    }
                  } else if (inner_content_type = 21uy) {
                    if SZ.(1sz <^ payload_len) {
                      let alert_level = inner.(0sz);
                      let alert_description = inner.(1sz);
                      if ((alert_level = 1uy || alert_level = 2uy) && alert_description = 0uy) {
                        ST.advance c.state S.RecvCloseNotify (S.recv_close_state view0.CL.state);
                        let base_view2 : erased CL.connection_view =
                          CL.note_recv_close_notify (Ghost.reveal view1) (S.recv_close_state view0.CL.state);
                        CL.lemma_step_read_close_notify
                          view0
                          (Ghost.reveal view1)
                          (SZ.v requested_app_len)
                          (S.recv_close_state view0.CL.state);
                        let resp : erased CL.client_response =
                          CL.response_no_network_out B.empty CL.Closed;
                        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                        assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                        let view2 : erased CL.connection_view =
                          CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                        CL.lemma_step_with_pending_received_raw
                          view0
                          mreq
                          (Ghost.reveal base_view2)
                          (Ghost.reveal resp)
                          (Ghost.reveal pending_raw_payload);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                        ST.advance_log c.log (Ghost.reveal view2);
                        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Closed };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_empty_prefix (Ghost.reveal 'app_out0);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
                        fold (is_client_core c (Ghost.reveal view2));
                        result
                      } else if (alert_level = 1uy || alert_level = 2uy) {
                        let alert = alert_description_of_u8 alert_description;
                        lemma_alert_description_of_u8_not_close alert_description;
                        assert (pure (alert <> T.CloseNotify));
                        ST.advance_fail c.state (T.AlertError alert);
                        let base_view2 : erased CL.connection_view =
                          CL.note_host_event
                            (Ghost.reveal view1)
                            (received_alert_event alert)
                            (S.fail view0.CL.state (T.AlertError alert));
                        CL.lemma_step_read_alert_failed
                          view0
                          (Ghost.reveal view1)
                          (SZ.v requested_app_len)
                          alert
                          (S.fail view0.CL.state (T.AlertError alert));
                        let resp : erased CL.client_response =
                          CL.response_no_network_out B.empty (CL.Failed (T.AlertError alert));
                        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                        assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                        let view2 : erased CL.connection_view =
                          CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                        CL.lemma_step_with_pending_received_raw
                          view0
                          mreq
                          (Ghost.reveal base_view2)
                          (Ghost.reveal resp)
                          (Ghost.reveal pending_raw_payload);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                        ST.advance_log c.log (Ghost.reveal view2);
                        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed (T.AlertError alert) };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_empty_prefix (Ghost.reveal 'app_out0);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
                        fold (is_client_core c (Ghost.reveal view2));
                        result
                      } else {
                        ST.advance_fail c.state T.IoError;
                        let base_view2 : erased CL.connection_view =
                          CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                        CL.lemma_step_read_failed
                          view0
                          (Ghost.reveal view1)
                          (SZ.v requested_app_len)
                          T.IoError
                          (S.fail view0.CL.state T.IoError);
                        let resp : erased CL.client_response =
                          CL.response_no_network_out B.empty (CL.Failed T.IoError);
                        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                        assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                        let view2 : erased CL.connection_view =
                          CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                        CL.lemma_step_with_pending_received_raw
                          view0
                          mreq
                          (Ghost.reveal base_view2)
                          (Ghost.reveal resp)
                          (Ghost.reveal pending_raw_payload);
                        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                        ST.advance_log c.log (Ghost.reveal view2);
                        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_empty_prefix (Ghost.reveal 'app_out0);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
                        fold (is_client_core c (Ghost.reveal view2));
                        result
                      }
                    } else {
                      ST.advance_fail c.state T.IoError;
                      let base_view2 : erased CL.connection_view =
                        CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                      CL.lemma_step_read_failed
                        view0
                        (Ghost.reveal view1)
                        (SZ.v requested_app_len)
                        T.IoError
                        (S.fail view0.CL.state T.IoError);
                      let resp : erased CL.client_response =
                        CL.response_no_network_out B.empty (CL.Failed T.IoError);
                      CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                      assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                      assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                      let view2 : erased CL.connection_view =
                        CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                      CL.lemma_step_with_pending_received_raw
                        view0
                        mreq
                        (Ghost.reveal base_view2)
                        (Ghost.reveal resp)
                        (Ghost.reveal pending_raw_payload);
                      assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                      ST.advance_log c.log (Ghost.reveal view2);
                      let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                      lemma_empty_prefix (Ghost.reveal 'network_out0);
                      lemma_empty_prefix (Ghost.reveal 'app_out0);
                      assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                                CL.step view0 mreq (Ghost.reveal view2) mresp));
                      fold (is_client_core c (Ghost.reveal view2));
                      result
                    }
                  } else {
                    ST.advance_fail c.state T.IoError;
                    let base_view2 : erased CL.connection_view =
                      CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                    CL.lemma_step_read_failed
                      view0
                      (Ghost.reveal view1)
                      (SZ.v requested_app_len)
                      T.IoError
                      (S.fail view0.CL.state T.IoError);
                    let resp : erased CL.client_response =
                      CL.response_no_network_out B.empty (CL.Failed T.IoError);
                    CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                    assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                    assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                    let view2 : erased CL.connection_view =
                      CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                    CL.lemma_step_with_pending_received_raw
                      view0
                      mreq
                      (Ghost.reveal base_view2)
                      (Ghost.reveal resp)
                      (Ghost.reveal pending_raw_payload);
                    assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                    ST.advance_log c.log (Ghost.reveal view2);
                    let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                    lemma_empty_prefix (Ghost.reveal 'network_out0);
                    lemma_empty_prefix (Ghost.reveal 'app_out0);
                    assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                    assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                              CL.step view0 mreq (Ghost.reveal view2) mresp));
                    fold (is_client_core c (Ghost.reveal view2));
                    result
                  }
                } else {
                  ST.advance_fail c.state T.IoError;
                  let base_view2 : erased CL.connection_view =
                    CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                  CL.lemma_step_read_failed
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    T.IoError
                    (S.fail view0.CL.state T.IoError);
                  let resp : erased CL.client_response =
                    CL.response_no_network_out B.empty (CL.Failed T.IoError);
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
                  assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw (Ghost.reveal base_view2) (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    (Ghost.reveal resp)
                    (Ghost.reveal pending_raw_payload);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_empty_prefix (Ghost.reveal 'app_out0);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
                }
              }
              }
            } else {
              V.to_vec_pts_to c.pending_network_buffer;
              with pending_network_buffer2. assert (V.pts_to c.pending_network_buffer pending_network_buffer2);
              c.pending_network_len := 0sz;
              lemma_empty_prefix (Ghost.reveal pending_network_buffer2);
              ST.advance_fail c.state T.IoError;
              let base_view2 : erased CL.connection_view =
                CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
              CL.lemma_step_read_failed
                view0
                (Ghost.reveal view1)
                (SZ.v requested_app_len)
                T.IoError
                (S.fail view0.CL.state T.IoError);
              let resp : erased CL.client_response =
                CL.response_no_network_out B.empty (CL.Failed T.IoError);
              CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
              assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal base_view2).CL.raw_log));
              assert (pure (CL.step view0 mreq (Ghost.reveal base_view2) (Ghost.reveal resp)));
              let view2 : erased CL.connection_view =
                CL.with_pending_received_raw (Ghost.reveal base_view2) B.empty;
              CL.lemma_step_with_pending_received_raw
                view0
                mreq
                (Ghost.reveal base_view2)
                (Ghost.reveal resp)
                B.empty;
              assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
              ST.advance_log c.log (Ghost.reveal view2);
              let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
              lemma_empty_prefix (Ghost.reveal 'network_out0);
              lemma_empty_prefix (Ghost.reveal 'app_out0);
              assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) (Ghost.reveal resp)));
              assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                        CL.step view0 mreq (Ghost.reveal view2) mresp));
              fold (is_client_core c (Ghost.reveal view2));
              result
            }
          } else {
            let pending_payload : erased B.bytes =
              CL.raw_slice
                (Ghost.reveal pending_network_buffer1)
                0
                (SZ.v pending_network_len');
            let view2 : erased CL.connection_view =
              CL.with_pending_received_raw
                (Ghost.reveal view1)
                (Ghost.reveal pending_payload);
            CL.lemma_step_read_need_network_input_with_pending
              view0
              (Ghost.reveal view1)
              (SZ.v requested_app_len)
              (Ghost.reveal pending_payload);
            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
            ST.advance_log c.log (Ghost.reveal view2);
            let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.NeedNetworkInput };
            let resp = CL.response_no_network_out B.empty CL.NeedNetworkInput;
            lemma_empty_prefix (Ghost.reveal 'network_out0);
            lemma_empty_prefix (Ghost.reveal 'app_out0);
            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
            fold (is_client_core c (Ghost.reveal view2));
            result
          }
        } else {
          ST.advance_fail c.state T.IoError;
          let view2 : erased CL.connection_view =
            CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
          CL.lemma_step_read_failed
            view0
            (Ghost.reveal view1)
            (SZ.v requested_app_len)
            T.IoError
            (S.fail view0.CL.state T.IoError);
          CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
          assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
          ST.advance_log c.log (Ghost.reveal view2);
          let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
          let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
          lemma_empty_prefix (Ghost.reveal 'network_out0);
          lemma_empty_prefix (Ghost.reveal 'app_out0);
          assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
          assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                    CL.step view0 mreq (Ghost.reveal view2) mresp));
          fold (is_client_core c (Ghost.reveal view2));
          result
        }
      } else if SZ.(5sz <=^ network_in_len) {
      let mut header = [| 0uy; 5sz |];
      copy_payload_to_output network_in network_in_len 5sz header 5sz 0sz;
      with header_bytes. assert (pts_to header header_bytes);
      assert (pure (B.length header_bytes == 5));
      let mut content_type_out = [| 0uy; 1sz |];
      let mut fragment_len_out = [| 0uy; 2sz |];
      let header_parse_ok =
        RF.parse_record_header header 5sz content_type_out 1sz fragment_len_out 2sz;
      if header_parse_ok {
        let content_type = content_type_out.(0sz);
        let frag_hi = fragment_len_out.(0sz);
        let frag_lo = fragment_len_out.(1sz);
        let frag_hi16 = Cast.uint8_to_uint16 frag_hi;
        let frag_lo16 = Cast.uint8_to_uint16 frag_lo;
        let frag16 = U16.logor (U16.shift_left frag_hi16 8ul) frag_lo16;
        let fragment_len = SZ.uint16_to_sizet frag16;
        let remaining_network_len = SZ.(network_in_len -^ 5sz);
        if (not (content_type = 23uy) || not (SZ.(16sz <^ fragment_len))) {
          if SZ.(fragment_len <=^ remaining_network_len) {
            assert (pure (SZ.v fragment_len <= SZ.v remaining_network_len));
            assert (pure (SZ.v remaining_network_len == SZ.v network_in_len - 5));
            assert (pure (5 + SZ.v fragment_len <= SZ.v network_in_len));
            let record_wire_len = SZ.(5sz +^ fragment_len);
            assert (pure (SZ.v record_wire_len == 5 + SZ.v fragment_len));
            assert (pure (SZ.v record_wire_len <= SZ.v network_in_len));
            let residual_len = SZ.(network_in_len -^ record_wire_len);
            assert (pure (SZ.v residual_len == SZ.v network_in_len - SZ.v record_wire_len));
            lemma_nat_add_sub_cancel 0 (SZ.v record_wire_len) (SZ.v network_in_len);
            assert (pure (SZ.v record_wire_len + SZ.v residual_len == SZ.v network_in_len));
            if SZ.(pending_network_buffer_capacity <^ residual_len) {
              ST.advance_fail c.state T.IoError;
              let view2 : erased CL.connection_view =
                CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
              CL.lemma_step_read_failed
                view0
                (Ghost.reveal view1)
                (SZ.v requested_app_len)
                T.IoError
                (S.fail view0.CL.state T.IoError);
              CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
              assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
              ST.advance_log c.log (Ghost.reveal view2);
              let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
              let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
              lemma_empty_prefix (Ghost.reveal 'network_out0);
              lemma_empty_prefix (Ghost.reveal 'app_out0);
              assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
              assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                        CL.step view0 mreq (Ghost.reveal view2) mresp));
              fold (is_client_core c (Ghost.reveal view2));
              result
            } else {
              assert (pure (SZ.v residual_len <= SZ.v pending_network_buffer_capacity));
              assert (pure (SZ.v record_wire_len + SZ.v residual_len <= SZ.v network_in_len));
              V.pts_to_len c.pending_network_buffer;
              V.to_array_pts_to c.pending_network_buffer;
              copy_payload_to_output_loop
                network_in
                network_in_len
                (V.vec_to_array c.pending_network_buffer)
                pending_network_buffer_capacity
                record_wire_len
                0sz
                residual_len;
              V.to_vec_pts_to c.pending_network_buffer;
              c.pending_network_len := residual_len;
              with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
              let pending_raw_payload : erased B.bytes =
                CL.raw_slice
                  (Ghost.reveal pending_network_buffer1)
                  0
                  (SZ.v residual_len);
              ST.advance_fail c.state T.IoError;
              let base_view2 : erased CL.connection_view =
                CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
              let view2 : erased CL.connection_view =
                CL.with_pending_received_raw
                  (Ghost.reveal base_view2)
                  (Ghost.reveal pending_raw_payload);
              CL.lemma_step_read_failed
                view0
                (Ghost.reveal view1)
                (SZ.v requested_app_len)
                T.IoError
                (S.fail view0.CL.state T.IoError);
              CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
              assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
              let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
              CL.lemma_step_with_pending_received_raw
                view0
                mreq
                (Ghost.reveal base_view2)
                resp
                (Ghost.reveal pending_raw_payload);
              ST.advance_log c.log (Ghost.reveal view2);
              let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
              lemma_empty_prefix (Ghost.reveal 'network_out0);
              lemma_empty_prefix (Ghost.reveal 'app_out0);
              assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
              assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                        CL.step view0 mreq (Ghost.reveal view2) mresp));
              fold (is_client_core c (Ghost.reveal view2));
              result
            }
          } else {
            ST.advance_fail c.state T.IoError;
            let view2 : erased CL.connection_view =
              CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
            CL.lemma_step_read_failed
              view0
              (Ghost.reveal view1)
              (SZ.v requested_app_len)
              T.IoError
              (S.fail view0.CL.state T.IoError);
            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
            ST.advance_log c.log (Ghost.reveal view2);
            let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
            let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
            lemma_empty_prefix (Ghost.reveal 'network_out0);
            lemma_empty_prefix (Ghost.reveal 'app_out0);
            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
            fold (is_client_core c (Ghost.reveal view2));
            result
          }
        } else if not (SZ.(fragment_len <=^ remaining_network_len)) {
          if SZ.(network_in_len <=^ pending_network_buffer_capacity) {
            V.pts_to_len c.pending_network_buffer;
            V.to_array_pts_to c.pending_network_buffer;
            copy_payload_to_output_loop
              network_in
              network_in_len
              (V.vec_to_array c.pending_network_buffer)
              pending_network_buffer_capacity
              0sz
              0sz
              network_in_len;
            V.to_vec_pts_to c.pending_network_buffer;
            with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
            c.pending_network_len := network_in_len;
            let pending_payload : erased B.bytes =
              CL.raw_slice
                (Ghost.reveal pending_network_buffer1)
                0
                (SZ.v network_in_len);
            let view2 : erased CL.connection_view =
              CL.with_pending_received_raw
                (Ghost.reveal view1)
                (Ghost.reveal pending_payload);
            CL.lemma_step_read_need_network_input_with_pending
              view0
              (Ghost.reveal view1)
              (SZ.v requested_app_len)
              (Ghost.reveal pending_payload);
            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
            ST.advance_log c.log (Ghost.reveal view2);
            let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.NeedNetworkInput };
            let resp = CL.response_no_network_out B.empty CL.NeedNetworkInput;
            lemma_empty_prefix (Ghost.reveal 'network_out0);
            lemma_empty_prefix (Ghost.reveal 'app_out0);
            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
            fold (is_client_core c (Ghost.reveal view2));
            result
          } else {
            ST.advance_fail c.state T.IoError;
            let view2 : erased CL.connection_view =
              CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
            CL.lemma_step_read_failed
              view0
              (Ghost.reveal view1)
              (SZ.v requested_app_len)
              T.IoError
              (S.fail view0.CL.state T.IoError);
            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
            ST.advance_log c.log (Ghost.reveal view2);
            let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
            let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
            lemma_empty_prefix (Ghost.reveal 'network_out0);
            lemma_empty_prefix (Ghost.reveal 'app_out0);
            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
              fold (is_client_core c (Ghost.reveal view2));
              result
            }
        } else {
          assert (pure (SZ.v fragment_len <= SZ.v remaining_network_len));
          assert (pure (SZ.v remaining_network_len == SZ.v network_in_len - 5));
          assert (pure (5 + SZ.v fragment_len <= SZ.v network_in_len));
          let record_wire_len = SZ.(5sz +^ fragment_len);
          assert (pure (SZ.v record_wire_len == 5 + SZ.v fragment_len));
          assert (pure (SZ.v record_wire_len <= SZ.v network_in_len));
          let residual_len = SZ.(network_in_len -^ record_wire_len);
          assert (pure (SZ.v residual_len == SZ.v network_in_len - SZ.v record_wire_len));
          lemma_nat_add_sub_cancel 0 (SZ.v record_wire_len) (SZ.v network_in_len);
          assert (pure (SZ.v record_wire_len + SZ.v residual_len == SZ.v network_in_len));
          if SZ.(pending_network_buffer_capacity <^ residual_len) {
            ST.advance_fail c.state T.IoError;
            let view2 : erased CL.connection_view =
              CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
            CL.lemma_step_read_failed
              view0
              (Ghost.reveal view1)
              (SZ.v requested_app_len)
              T.IoError
              (S.fail view0.CL.state T.IoError);
            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
            ST.advance_log c.log (Ghost.reveal view2);
            let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
            let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
            lemma_empty_prefix (Ghost.reveal 'network_out0);
            lemma_empty_prefix (Ghost.reveal 'app_out0);
            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
            fold (is_client_core c (Ghost.reveal view2));
            result
          } else {
            assert (pure (SZ.v residual_len <= SZ.v pending_network_buffer_capacity));
            assert (pure (SZ.v record_wire_len + SZ.v residual_len <= SZ.v network_in_len));
            V.pts_to_len c.pending_network_buffer;
            V.to_array_pts_to c.pending_network_buffer;
            copy_payload_to_output_loop
              network_in
              network_in_len
              (V.vec_to_array c.pending_network_buffer)
              pending_network_buffer_capacity
              record_wire_len
              0sz
              residual_len;
            V.to_vec_pts_to c.pending_network_buffer;
            c.pending_network_len := residual_len;
            with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
            let pending_raw_payload : erased B.bytes =
              CL.raw_slice
                (Ghost.reveal pending_network_buffer1)
                0
                (SZ.v residual_len);
          let mut cipher = [| 0uy; fragment_len |];
          copy_payload_to_output_loop network_in network_in_len cipher fragment_len 5sz 0sz fragment_len;
          with cipher_bytes. assert (pts_to cipher cipher_bytes);
          assert (pure (B.length cipher_bytes == SZ.v fragment_len));
          assert (pure (not (not (SZ.(16sz <^ fragment_len)))));
          let fragment_len_has_tag = SZ.lt 16sz fragment_len;
          assert (pure (fragment_len_has_tag == SZ.(16sz <^ fragment_len)));
          assert (pure (fragment_len_has_tag == true));
          assert (pure (fragment_len_has_tag == (SZ.v 16sz < SZ.v fragment_len)));
          assert (pure (SZ.v 16sz == 16));
          assert (pure (16 < SZ.v fragment_len));
          assert (pure (16 <= SZ.v fragment_len));
          let inner_len = SZ.(fragment_len -^ 16sz);
          assert (pure (SZ.v inner_len > 0));
          let mut inner = [| 0uy; inner_len |];
          with inner_old. assert (pts_to inner inner_old);
          assert (pure (B.length inner_old == SZ.v inner_len));
          assert (pure (B.length inner_old + 16 == SZ.v fragment_len));
          let opened =
            Rec.open_application_runtime
              c.server_application_record_state
              header
              5sz
              cipher
              fragment_len
              inner;
          if opened {
            let mut inner_content_type_out = [| 0uy; 1sz |];
            let payload_len =
              RF.decode_inner_plaintext inner inner_len inner_content_type_out 1sz;
            let inner_content_type = inner_content_type_out.(0sz);
            if (inner_content_type = 23uy) {
              if (SZ.(payload_len <=^ requested_app_len) && SZ.(payload_len <=^ app_out_cap)) {
                copy_payload_to_output inner inner_len payload_len app_out app_out_cap 0sz;
                with app_out1. assert (pts_to app_out app_out1);
                assert (pure (B.length app_out1 == SZ.v app_out_cap));
                let app_payload : erased B.bytes =
                  Seq.slice (Ghost.reveal app_out1) 0 (SZ.v payload_len);
                ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                let base_view2 : erased CL.connection_view =
                  CL.note_app_received_with_pending
                    (Ghost.reveal view1)
                    (Ghost.reveal app_payload)
                    B.empty
                    (S.advance_read_record view0.CL.state);
                let view2 : erased CL.connection_view =
                  CL.with_pending_received_raw
                    (Ghost.reveal base_view2)
                    (Ghost.reveal pending_raw_payload);
                CL.lemma_step_read_application_data_success_with_pending
                  view0
                  (Ghost.reveal view1)
                  (SZ.v requested_app_len)
                  (Ghost.reveal app_payload)
                  B.empty
                  (S.advance_read_record view0.CL.state);
                CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                let resp : erased CL.client_response =
                  CL.response_no_network_out (Ghost.reveal app_payload) CL.ApplicationDataReady;
                CL.lemma_step_with_pending_received_raw
                  view0
                  mreq
                  (Ghost.reveal base_view2)
                  (Ghost.reveal resp)
                  (Ghost.reveal pending_raw_payload);
                ST.advance_log c.log (Ghost.reveal view2);
                let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                lemma_empty_prefix (Ghost.reveal 'network_out0);
                lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp)));
                assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                          CL.step view0 mreq (Ghost.reveal view2) mresp));
                fold (is_client_core c (Ghost.reveal view2));
                result
              } else {
                let output_limit : SZ.t =
                  if SZ.(requested_app_len <^ app_out_cap) {
                    requested_app_len
                  } else {
                    app_out_cap
                  };
                if (SZ.(0sz <^ output_limit) &&
                    SZ.(output_limit <^ payload_len) &&
                    SZ.(payload_len <=^ pending_read_buffer_capacity)) {
                  assert (pure (SZ.v output_limit <= SZ.v app_out_cap));
                  assert (pure (SZ.v output_limit <= SZ.v payload_len));
                  copy_payload_to_output inner inner_len output_limit app_out app_out_cap 0sz;
                  with app_out1. assert (pts_to app_out app_out1);
                  assert (pure (B.length app_out1 == SZ.v app_out_cap));
                  let leftover_len = SZ.(payload_len -^ output_limit);
                  assert (pure (SZ.v leftover_len == SZ.v payload_len - SZ.v output_limit));
                  assert (pure (SZ.v leftover_len > 0));
                  assert (pure (SZ.v leftover_len <= SZ.v pending_read_buffer_capacity));
                  lemma_nat_add_sub_cancel
                    0
                    (SZ.v output_limit)
                    (SZ.v payload_len);
                  assert (pure (0 + SZ.v output_limit + (SZ.v payload_len - SZ.v output_limit) ==
                                0 + SZ.v payload_len));
                  assert (pure (SZ.v output_limit + SZ.v leftover_len ==
                                0 + SZ.v output_limit + (SZ.v payload_len - SZ.v output_limit)));
                  assert (pure (SZ.v output_limit + SZ.v leftover_len == 0 + SZ.v payload_len));
                  assert (pure (SZ.v payload_len <= SZ.v inner_len));
                  assert (pure (SZ.v output_limit + SZ.v leftover_len <= SZ.v inner_len));
                  pts_to_len inner;
                  with inner_bytes. assert (pts_to inner inner_bytes);
                  assert (pure (B.length inner_bytes == SZ.v inner_len));
                  V.pts_to_len c.pending_read_buffer;
                  V.to_array_pts_to c.pending_read_buffer;
                  copy_payload_to_output_loop
                    inner
                    inner_len
                    (V.vec_to_array c.pending_read_buffer)
                    pending_read_buffer_capacity
                    output_limit
                    0sz
                    leftover_len;
                  V.to_vec_pts_to c.pending_read_buffer;
                  with pending_buffer1. assert (V.pts_to c.pending_read_buffer pending_buffer1);
                  c.pending_read_offset := 0sz;
                  c.pending_read_len := leftover_len;
                  let app_payload : erased B.bytes =
                    Seq.slice (Ghost.reveal app_out1) 0 (SZ.v output_limit);
                  let pending_payload : erased B.bytes =
                    CL.raw_slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len);
                  ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                  let base_view2 : erased CL.connection_view =
                    CL.note_app_received_with_pending
                      (Ghost.reveal view1)
                      (Ghost.reveal app_payload)
                      (Ghost.reveal pending_payload)
                      (S.advance_read_record view0.CL.state);
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw
                      (Ghost.reveal base_view2)
                      (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_read_application_data_success_with_pending
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    (Ghost.reveal app_payload)
                    (Ghost.reveal pending_payload)
                    (S.advance_read_record view0.CL.state);
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  let resp : erased CL.client_response =
                    CL.response_no_network_out (Ghost.reveal app_payload) CL.ApplicationDataReady;
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    (Ghost.reveal resp)
                    (Ghost.reveal pending_raw_payload);
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = output_limit; status = CL.ApplicationDataReady };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v output_limit);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp)));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
                } else {
                  ST.advance_fail c.state T.IoError;
                  let base_view2 : erased CL.connection_view =
                    CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw
                      (Ghost.reveal base_view2)
                      (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_read_failed
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    T.IoError
                    (S.fail view0.CL.state T.IoError);
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    resp
                    (Ghost.reveal pending_raw_payload);
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_empty_prefix (Ghost.reveal 'app_out0);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
                }
              }
            } else if (inner_content_type = 21uy) {
              if SZ.(1sz <^ payload_len) {
                let alert_level = inner.(0sz);
                let alert_description = inner.(1sz);
                if ((alert_level = 1uy || alert_level = 2uy) && alert_description = 0uy) {
                  ST.advance c.state S.RecvCloseNotify (S.recv_close_state view0.CL.state);
                  let base_view2 : erased CL.connection_view =
                    CL.note_recv_close_notify (Ghost.reveal view1) (S.recv_close_state view0.CL.state);
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw
                      (Ghost.reveal base_view2)
                      (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_read_close_notify
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    (S.recv_close_state view0.CL.state);
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  let resp = CL.response_no_network_out B.empty CL.Closed;
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    resp
                    (Ghost.reveal pending_raw_payload);
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Closed };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_empty_prefix (Ghost.reveal 'app_out0);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
                } else if (alert_level = 1uy || alert_level = 2uy) {
                  let alert = alert_description_of_u8 alert_description;
                  lemma_alert_description_of_u8_not_close alert_description;
                  assert (pure (alert <> T.CloseNotify));
                  ST.advance_fail c.state (T.AlertError alert);
                  let base_view2 : erased CL.connection_view =
                    CL.note_host_event
                      (Ghost.reveal view1)
                      (received_alert_event alert)
                      (S.fail view0.CL.state (T.AlertError alert));
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw
                      (Ghost.reveal base_view2)
                      (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_read_alert_failed
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    alert
                    (S.fail view0.CL.state (T.AlertError alert));
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  let resp = CL.response_no_network_out B.empty (CL.Failed (T.AlertError alert));
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    resp
                    (Ghost.reveal pending_raw_payload);
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed (T.AlertError alert) };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_empty_prefix (Ghost.reveal 'app_out0);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
                } else {
                  ST.advance_fail c.state T.IoError;
                  let base_view2 : erased CL.connection_view =
                    CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                  let view2 : erased CL.connection_view =
                    CL.with_pending_received_raw
                      (Ghost.reveal base_view2)
                      (Ghost.reveal pending_raw_payload);
                  CL.lemma_step_read_failed
                    view0
                    (Ghost.reveal view1)
                    (SZ.v requested_app_len)
                    T.IoError
                    (S.fail view0.CL.state T.IoError);
                  CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                  let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
                  CL.lemma_step_with_pending_received_raw
                    view0
                    mreq
                    (Ghost.reveal base_view2)
                    resp
                    (Ghost.reveal pending_raw_payload);
                  ST.advance_log c.log (Ghost.reveal view2);
                  let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_empty_prefix (Ghost.reveal 'app_out0);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                  fold (is_client_core c (Ghost.reveal view2));
                  result
                }
              } else {
                ST.advance_fail c.state T.IoError;
                let base_view2 : erased CL.connection_view =
                  CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
                let view2 : erased CL.connection_view =
                  CL.with_pending_received_raw
                    (Ghost.reveal base_view2)
                    (Ghost.reveal pending_raw_payload);
                CL.lemma_step_read_failed
                  view0
                  (Ghost.reveal view1)
                  (SZ.v requested_app_len)
                  T.IoError
                  (S.fail view0.CL.state T.IoError);
                CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
                CL.lemma_step_with_pending_received_raw
                  view0
                  mreq
                  (Ghost.reveal base_view2)
                  resp
                  (Ghost.reveal pending_raw_payload);
                ST.advance_log c.log (Ghost.reveal view2);
                let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
                lemma_empty_prefix (Ghost.reveal 'network_out0);
                lemma_empty_prefix (Ghost.reveal 'app_out0);
                assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
                assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                          CL.step view0 mreq (Ghost.reveal view2) mresp));
                fold (is_client_core c (Ghost.reveal view2));
                result
              }
            } else {
              ST.advance_fail c.state T.IoError;
              let base_view2 : erased CL.connection_view =
                CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
              let view2 : erased CL.connection_view =
                CL.with_pending_received_raw
                  (Ghost.reveal base_view2)
                  (Ghost.reveal pending_raw_payload);
              CL.lemma_step_read_failed
                view0
                (Ghost.reveal view1)
                (SZ.v requested_app_len)
                T.IoError
                (S.fail view0.CL.state T.IoError);
              CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
              assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
              let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
              CL.lemma_step_with_pending_received_raw
                view0
                mreq
                (Ghost.reveal base_view2)
                resp
                (Ghost.reveal pending_raw_payload);
              ST.advance_log c.log (Ghost.reveal view2);
              let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
              lemma_empty_prefix (Ghost.reveal 'network_out0);
              lemma_empty_prefix (Ghost.reveal 'app_out0);
              assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
              assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                        CL.step view0 mreq (Ghost.reveal view2) mresp));
              fold (is_client_core c (Ghost.reveal view2));
              result
            }
          } else {
            ST.advance_fail c.state T.IoError;
            let base_view2 : erased CL.connection_view =
              CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
            let view2 : erased CL.connection_view =
              CL.with_pending_received_raw
                (Ghost.reveal base_view2)
                (Ghost.reveal pending_raw_payload);
            CL.lemma_step_read_failed
              view0
              (Ghost.reveal view1)
              (SZ.v requested_app_len)
              T.IoError
              (S.fail view0.CL.state T.IoError);
            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
            let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
            CL.lemma_step_with_pending_received_raw
              view0
              mreq
              (Ghost.reveal base_view2)
              resp
              (Ghost.reveal pending_raw_payload);
            ST.advance_log c.log (Ghost.reveal view2);
            let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
            lemma_empty_prefix (Ghost.reveal 'network_out0);
            lemma_empty_prefix (Ghost.reveal 'app_out0);
            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
            fold (is_client_core c (Ghost.reveal view2));
            result
          }
          }
        }
      } else {
        ST.advance_fail c.state T.IoError;
        let view2 : erased CL.connection_view =
          CL.note_local_fail (Ghost.reveal view1) T.IoError (S.fail view0.CL.state T.IoError);
        CL.lemma_step_read_failed
          view0
          (Ghost.reveal view1)
          (SZ.v requested_app_len)
          T.IoError
          (S.fail view0.CL.state T.IoError);
        CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
        assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
        ST.advance_log c.log (Ghost.reveal view2);
        let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.Failed T.IoError };
        let resp = CL.response_no_network_out B.empty (CL.Failed T.IoError);
        lemma_empty_prefix (Ghost.reveal 'network_out0);
        lemma_empty_prefix (Ghost.reveal 'app_out0);
        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                  CL.step view0 mreq (Ghost.reveal view2) mresp));
        fold (is_client_core c (Ghost.reveal view2));
        result
      }
    } else {
      assert (pure (SZ.v network_in_len < 5));
      assert (pure (SZ.v network_in_len <= SZ.v pending_network_buffer_capacity));
      V.pts_to_len c.pending_network_buffer;
      V.to_array_pts_to c.pending_network_buffer;
      copy_payload_to_output_loop
        network_in
        network_in_len
        (V.vec_to_array c.pending_network_buffer)
        pending_network_buffer_capacity
        0sz
        0sz
        network_in_len;
      V.to_vec_pts_to c.pending_network_buffer;
      with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
      c.pending_network_len := network_in_len;
      let pending_payload : erased B.bytes =
        CL.raw_slice
          (Ghost.reveal pending_network_buffer1)
          0
          (SZ.v network_in_len);
      let view2 : erased CL.connection_view =
        CL.with_pending_received_raw
          (Ghost.reveal view1)
          (Ghost.reveal pending_payload);
      CL.lemma_step_read_need_network_input_with_pending
        view0
        (Ghost.reveal view1)
        (SZ.v requested_app_len)
        (Ghost.reveal pending_payload);
      CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
      assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
      ST.advance_log c.log (Ghost.reveal view2);
      let result = { network_out_len = 0sz; app_out_len = 0sz; status = CL.NeedNetworkInput };
      let resp = CL.response_no_network_out B.empty CL.NeedNetworkInput;
      lemma_empty_prefix (Ghost.reveal 'network_out0);
      lemma_empty_prefix (Ghost.reveal 'app_out0);
      assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) resp));
      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal 'app_out0) mresp /\
                                CL.step view0 mreq (Ghost.reveal view2) mresp));
      fold (is_client_core c (Ghost.reveal view2));
      result
    }
    }
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
