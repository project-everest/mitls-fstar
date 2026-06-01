module TLS13.Connection.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module Cast = FStar.Int.Cast
module CL = TLS13.ConnectionLog
module L = FStar.List.Tot
module Math = FStar.Math.Lemmas
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
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec

let tls_application_plaintext_max : SZ.t = 16384sz
let tls_ciphertext_fragment_max : SZ.t = 16640sz
let tls_application_record_wire_max : SZ.t = 16645sz

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

let lemma_u64_fits_add_le_of_count
  (seq:nat)
  (n:nat)
  (count:nat)
  : Lemma
      (requires n <= count /\ U64.fits (seq + count))
      (ensures U64.fits (seq + n))
  =
  ()

let lemma_u64_fits_add_one_of_count
  (seq:nat)
  (count:nat)
  : Lemma
      (requires 1 <= count /\ U64.fits (seq + count))
      (ensures U64.fits (seq + 1))
  =
  lemma_u64_fits_add_le_of_count seq 1 count

let lemma_u64_fits_add_two_of_count
  (seq:nat)
  (count:nat)
  : Lemma
      (requires 2 <= count /\ U64.fits (seq + count))
      (ensures U64.fits (seq + 2))
  =
  lemma_u64_fits_add_le_of_count seq 2 count

let lemma_u64_fits_next_after_consumed_of_budget
  (seq:nat)
  (consumed:nat)
  (budget:nat)
  : Lemma
      (requires consumed <= budget /\ U64.fits (seq + budget + 1))
      (ensures U64.fits (seq + consumed + 1))
  =
  assert (consumed + 1 <= budget + 1);
  assert (seq + (budget + 1) == seq + budget + 1);
  assert (seq + (consumed + 1) == seq + consumed + 1);
  lemma_u64_fits_add_le_of_count seq (consumed + 1) (budget + 1)

let lemma_step_recv_application_data
  (s:S.conn_state)
  (app:B.bytes)
  : Lemma
      (requires s.S.phase == S.ApplicationData)
      (ensures S.step s (S.RecvApplicationData app) == Some (S.advance_read_record s))
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
          CL.pending_app_source_consistent view /\
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

let lemma_copied_range_slice
  (payload:B.bytes)
  (bytes:B.bytes)
  (src:nat)
  (dst:nat)
  (len:nat)
  : Lemma
      (requires src + len <= B.length payload /\
                dst + len <= B.length bytes /\
                (forall (i:nat{i < len}).
                  Seq.index bytes (dst + i) == Seq.index payload (src + i)))
      (ensures Seq.equal
        (Seq.slice bytes dst (dst + len))
        (Seq.slice payload src (src + len)))
  =
  Seq.lemma_len_slice bytes dst (dst + len);
  Seq.lemma_len_slice payload src (src + len);
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index bytes (dst + i));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice payload src (src + len)) i ==
            Seq.index payload (src + i));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index (Seq.slice payload src (src + len)) i);
  Seq.lemma_eq_intro
    (Seq.slice bytes dst (dst + len))
    (Seq.slice payload src (src + len))

let lemma_slice_equal_range
  (payload:B.bytes)
  (bytes:B.bytes)
  (src:nat)
  (dst:nat)
  (len:nat)
  : Lemma
      (requires src + len <= B.length payload /\
                dst + len <= B.length bytes /\
                Seq.equal
                  (Seq.slice bytes dst (dst + len))
                  (Seq.slice payload src (src + len)))
      (ensures (forall (i:nat{i < len}).
        Seq.index bytes (dst + i) == Seq.index payload (src + i)))
  =
  Seq.lemma_eq_elim
    (Seq.slice bytes dst (dst + len))
    (Seq.slice payload src (src + len));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index (Seq.slice payload src (src + len)) i);
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index bytes (dst + i));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice payload src (src + len)) i ==
            Seq.index payload (src + i));
  assert (forall (i:nat{i < len}).
            Seq.index bytes (dst + i) == Seq.index payload (src + i))

let lemma_copy_step_range
  (payload:B.bytes)
  (mid:B.bytes)
  (final:B.bytes)
  (src:nat)
  (dst:nat)
  (remaining:nat)
  (src_next:nat)
  (dst_next:nat)
  (remaining_next:nat)
  : Lemma
      (requires remaining > 0 /\
                src_next == src + 1 /\
                dst_next == dst + 1 /\
                remaining_next == remaining - 1 /\
                src + remaining <= B.length payload /\
                dst + remaining <= B.length final /\
                B.length final == B.length mid /\
                Seq.index mid dst == Seq.index payload src /\
                (forall (i:nat{i < dst_next}).
                  Seq.index final i == Seq.index mid i) /\
                (forall (i:nat{i < remaining_next}).
                  Seq.index final (dst_next + i) ==
                  Seq.index payload (src_next + i)))
      (ensures (forall (i:nat{i < remaining}).
        Seq.index final (dst + i) == Seq.index payload (src + i)))
  =
  introduce forall (i:nat{i < remaining}).
    Seq.index final (dst + i) == Seq.index payload (src + i)
  with (
    if i = 0 then (
      assert (dst + i == dst);
      assert (src + i == src);
      assert (dst < dst_next);
      assert (Seq.index final dst == Seq.index mid dst)
    ) else (
      assert (i > 0);
      assert (i - 1 < remaining_next);
      assert (dst + i == dst_next + (i - 1));
      assert (src + i == src_next + (i - 1))
    )
  )

let lemma_copy_step_prefix
  (old:B.bytes)
  (mid:B.bytes)
  (final:B.bytes)
  (dst:nat)
  (dst_next:nat)
  : Lemma
      (requires dst <= B.length old /\
                dst_next == dst + 1 /\
                dst_next <= B.length old /\
                B.length mid == B.length old /\
                B.length final == B.length old /\
                (forall (i:nat{i < dst_next}).
                  Seq.index final i == Seq.index mid i) /\
                (forall (i:nat{i < dst}).
                  Seq.index mid i == Seq.index old i))
      (ensures (forall (i:nat{i < dst}).
        Seq.index final i == Seq.index old i))
  =
  ()

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
          pure (B.length 'payload_bytes == SZ.v payload_total_len /\
                B.length 'old == SZ.v total_len /\
                B.length bytes == SZ.v total_len /\
                SZ.v src_index + SZ.v remaining <= SZ.v payload_total_len /\
                SZ.v dst_index + SZ.v remaining <= SZ.v total_len /\
                Seq.equal
                  (Seq.slice bytes (SZ.v dst_index) (SZ.v dst_index + SZ.v remaining))
                  (Seq.slice 'payload_bytes (SZ.v src_index) (SZ.v src_index + SZ.v remaining)) /\
                Seq.equal
                  (Seq.slice bytes 0 (SZ.v dst_index))
                  (Seq.slice 'old 0 (SZ.v dst_index)))
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    with bytes. assert (pts_to out bytes);
    assert (pure (B.length 'payload_bytes == SZ.v payload_total_len));
    assert (pure (B.length 'old == SZ.v total_len));
    assert (pure (B.length bytes == SZ.v total_len));
    lemma_copied_range_slice
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal bytes)
      (SZ.v src_index)
      (SZ.v dst_index)
      (SZ.v remaining);
    assert (pure (Seq.equal
      (Seq.slice bytes (SZ.v dst_index) (SZ.v dst_index + SZ.v remaining))
      (Seq.slice 'payload_bytes (SZ.v src_index) (SZ.v src_index + SZ.v remaining))));
    assert (pure (forall (i:nat{i < SZ.v dst_index}).
      Seq.index bytes i == Seq.index 'old i));
    lemma_copied_range_slice
      (Ghost.reveal 'old)
      (Ghost.reveal bytes)
      0
      0
      (SZ.v dst_index);
    assert (pure (Seq.equal
      (Seq.slice bytes 0 (SZ.v dst_index))
      (Seq.slice 'old 0 (SZ.v dst_index))));
  } else {
    assert (pure (SZ.v src_index < SZ.v payload_total_len));
    assert (pure (SZ.v dst_index < SZ.v total_len));
    let b = payload.(src_index);
    out.(dst_index) <- b;
    let src_index' = SZ.(src_index +^ 1sz);
    let dst_index' = SZ.(dst_index +^ 1sz);
    let remaining' = SZ.(remaining -^ 1sz);
    with bytes. assert (pts_to out bytes);
    assert (pure (B.length 'payload_bytes == SZ.v payload_total_len));
    assert (pure (B.length 'old == SZ.v total_len));
    assert (pure (B.length bytes == SZ.v total_len));
    assert (pure (Seq.index bytes (SZ.v dst_index) == Seq.index 'payload_bytes (SZ.v src_index)));
    assert (pure (forall (i:nat{i < SZ.v dst_index}).
      Seq.index bytes i == Seq.index 'old i));
    assert (pure (SZ.v remaining' < SZ.v remaining));
    assert (pure (SZ.v src_index' + SZ.v remaining' <= SZ.v payload_total_len));
    assert (pure (SZ.v dst_index' + SZ.v remaining' <= SZ.v total_len));
    copy_payload_to_output_loop payload payload_total_len out total_len src_index' dst_index' remaining';
    with final_bytes. assert (pts_to out final_bytes);
    assert (pure (B.length final_bytes == SZ.v total_len));
    assert (pure (SZ.v src_index' == SZ.v src_index + 1));
    assert (pure (SZ.v dst_index' == SZ.v dst_index + 1));
    assert (pure (SZ.v remaining' == SZ.v remaining - 1));
    lemma_slice_equal_range
      (Ghost.reveal bytes)
      (Ghost.reveal final_bytes)
      0
      0
      (SZ.v dst_index');
    lemma_slice_equal_range
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal final_bytes)
      (SZ.v src_index')
      (SZ.v dst_index')
      (SZ.v remaining');
    lemma_copy_step_range
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal bytes)
      (Ghost.reveal final_bytes)
      (SZ.v src_index)
      (SZ.v dst_index)
      (SZ.v remaining)
      (SZ.v src_index')
      (SZ.v dst_index')
      (SZ.v remaining');
    assert (pure (forall (i:nat{i < SZ.v remaining}).
      Seq.index final_bytes (SZ.v dst_index + i) ==
      Seq.index 'payload_bytes (SZ.v src_index + i)));
    lemma_copied_range_slice
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal final_bytes)
      (SZ.v src_index)
      (SZ.v dst_index)
      (SZ.v remaining);
    lemma_copy_step_prefix
      (Ghost.reveal 'old)
      (Ghost.reveal bytes)
      (Ghost.reveal final_bytes)
      (SZ.v dst_index)
      (SZ.v dst_index');
    assert (pure (forall (i:nat{i < SZ.v dst_index}).
      Seq.index final_bytes i == Seq.index 'old i));
    lemma_copied_range_slice
      (Ghost.reveal 'old)
      (Ghost.reveal final_bytes)
      0
      0
      (SZ.v dst_index);
    assert (pure (Seq.equal
      (Seq.slice final_bytes 0 (SZ.v dst_index))
      (Seq.slice 'old 0 (SZ.v dst_index))))
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
          pure (B.length 'payload_bytes == SZ.v payload_total_len /\
                B.length 'old == SZ.v total_len /\
                B.length bytes == SZ.v total_len /\
                SZ.v copy_len <= SZ.v payload_total_len /\
                SZ.v offset + SZ.v copy_len <= SZ.v total_len /\
                Seq.equal
                  (Seq.slice bytes (SZ.v offset) (SZ.v offset + SZ.v copy_len))
                  (Seq.slice 'payload_bytes 0 (SZ.v copy_len)))
{
  copy_payload_to_output_loop payload payload_total_len out total_len 0sz offset copy_len
}

fn set_pending_network_from_slice
  (c: client_core)
  (source: array U8.t)
  (source_total_len: SZ.t)
  (source_offset: SZ.t)
  (copy_len: SZ.t)
  requires pts_to source 'source_bytes **
           V.pts_to c.pending_network_buffer 'pending0 **
           Box.pts_to c.pending_network_len 'old_pending_len **
           pure (B.length 'source_bytes == SZ.v source_total_len /\
                 V.is_full_vec c.pending_network_buffer /\
                 V.length c.pending_network_buffer == SZ.v pending_network_buffer_capacity /\
                 SZ.v source_offset + SZ.v copy_len <= SZ.v source_total_len /\
                 SZ.v copy_len <= SZ.v pending_network_buffer_capacity)
  ensures exists* pending1.
          pts_to source 'source_bytes **
          V.pts_to c.pending_network_buffer pending1 **
          Box.pts_to c.pending_network_len copy_len **
          pure (B.length 'source_bytes == SZ.v source_total_len /\
                V.is_full_vec c.pending_network_buffer /\
                V.length c.pending_network_buffer == SZ.v pending_network_buffer_capacity /\
                B.length pending1 == SZ.v pending_network_buffer_capacity /\
                SZ.v source_offset <= SZ.v source_offset + SZ.v copy_len /\
                SZ.v source_offset + SZ.v copy_len <= B.length 'source_bytes /\
                SZ.v copy_len <= B.length pending1 /\
                Seq.equal
                  (CL.raw_slice pending1 0 (SZ.v copy_len))
                  (Seq.slice 'source_bytes (SZ.v source_offset) (SZ.v source_offset + SZ.v copy_len)))
{
  V.pts_to_len c.pending_network_buffer;
  V.to_array_pts_to c.pending_network_buffer;
  copy_payload_to_output_loop
    source
    source_total_len
    (V.vec_to_array c.pending_network_buffer)
    pending_network_buffer_capacity
    source_offset
    0sz
    copy_len;
  V.to_vec_pts_to c.pending_network_buffer;
  c.pending_network_len := copy_len;
  with pending1. assert (V.pts_to c.pending_network_buffer pending1);
  assert (pure (B.length pending1 == SZ.v pending_network_buffer_capacity));
  assert (pure (CL.raw_slice pending1 0 (SZ.v copy_len) ==
                Seq.slice pending1 0 (SZ.v copy_len)));
  assert (pure (Seq.equal
    (Seq.slice pending1 0 (SZ.v copy_len))
    (Seq.slice 'source_bytes (SZ.v source_offset) (SZ.v source_offset + SZ.v copy_len))));
  assert (pure (Seq.equal
    (CL.raw_slice pending1 0 (SZ.v copy_len))
    (Seq.slice 'source_bytes (SZ.v source_offset) (SZ.v source_offset + SZ.v copy_len))))
}

type residual_frame_lengths = {
  residual_frame_wire_len: SZ.t;
  residual_frame_tail_len: SZ.t;
}

type residual_frame_lengths_at_result = {
  residual_frame_at_wire_len: SZ.t;
  residual_frame_at_end: SZ.t;
  residual_frame_at_tail_len: SZ.t;
}

let residual_frame_lengths_for
  (residual_len: SZ.t)
  (fragment_len: SZ.t)
  : Pure residual_frame_lengths
      (requires 5 + SZ.v fragment_len <= SZ.v residual_len)
      (ensures fun lens ->
        SZ.v lens.residual_frame_wire_len == 5 + SZ.v fragment_len /\
        SZ.v lens.residual_frame_wire_len <= SZ.v residual_len /\
        SZ.v lens.residual_frame_tail_len ==
          SZ.v residual_len - SZ.v lens.residual_frame_wire_len /\
        SZ.v lens.residual_frame_wire_len + SZ.v lens.residual_frame_tail_len ==
          SZ.v residual_len)
=
  let wire_len = SZ.(5sz +^ fragment_len) in
  assert (SZ.v wire_len == 5 + SZ.v fragment_len);
  assert (SZ.v wire_len <= SZ.v residual_len);
  let tail_len = SZ.(residual_len -^ wire_len) in
  assert (SZ.v tail_len == SZ.v residual_len - SZ.v wire_len);
  lemma_nat_add_sub_cancel 0 (SZ.v wire_len) (SZ.v residual_len);
  assert (SZ.v wire_len + SZ.v tail_len == SZ.v residual_len);
  {
    residual_frame_wire_len = wire_len;
    residual_frame_tail_len = tail_len
  }

let residual_frame_lengths_at
  (residual_len: SZ.t)
  (cursor: SZ.t)
  (fragment_len: SZ.t)
  : Pure residual_frame_lengths_at_result
      (requires SZ.v cursor + 5 + SZ.v fragment_len <= SZ.v residual_len)
      (ensures fun lens ->
        SZ.v lens.residual_frame_at_wire_len == 5 + SZ.v fragment_len /\
        SZ.v cursor + SZ.v lens.residual_frame_at_wire_len ==
          SZ.v lens.residual_frame_at_end /\
        SZ.v lens.residual_frame_at_end <= SZ.v residual_len /\
        SZ.v lens.residual_frame_at_tail_len ==
          SZ.v residual_len - SZ.v lens.residual_frame_at_end /\
        SZ.v lens.residual_frame_at_end + SZ.v lens.residual_frame_at_tail_len ==
          SZ.v residual_len)
=
  let wire_len = SZ.(5sz +^ fragment_len) in
  assert (SZ.v wire_len == 5 + SZ.v fragment_len);
  assert (SZ.v cursor + SZ.v wire_len <= SZ.v residual_len);
  let record_end = SZ.(cursor +^ wire_len) in
  assert (SZ.v record_end == SZ.v cursor + SZ.v wire_len);
  assert (SZ.v record_end <= SZ.v residual_len);
  let tail_len = SZ.(residual_len -^ record_end) in
  assert (SZ.v tail_len == SZ.v residual_len - SZ.v record_end);
  lemma_nat_add_sub_cancel 0 (SZ.v record_end) (SZ.v residual_len);
  assert (SZ.v record_end + SZ.v tail_len == SZ.v residual_len);
  {
    residual_frame_at_wire_len = wire_len;
    residual_frame_at_end = record_end;
    residual_frame_at_tail_len = tail_len
  }

fn seal_application_record_to_output
  (record_state: Rec.record_state)
  (app_in: array U8.t)
  (app_in_len: SZ.t)
  (plain_offset: SZ.t)
  (chunk_len: SZ.t)
  (network_out: array U8.t)
  (network_out_cap: SZ.t)
  (wire_offset: SZ.t)
  requires Rec.is_record_state record_state 's **
           pts_to app_in 'app_bytes **
           pts_to network_out 'network_out0 **
           pure (B.length 'app_bytes == SZ.v app_in_len /\
                 B.length 'network_out0 == SZ.v network_out_cap /\
                 SZ.v chunk_len <= SZ.v tls_application_plaintext_max /\
                 SZ.v plain_offset + SZ.v chunk_len <= SZ.v app_in_len /\
                 U64.fits ('s.R.seq + 1) /\
                 SZ.v wire_offset + 5 + (SZ.v chunk_len + 17) <= SZ.v network_out_cap)
  returns ok: bool
  ensures exists* s' network_out1.
          Rec.is_record_state record_state s' **
          pts_to app_in 'app_bytes **
          pts_to network_out network_out1 **
          pure (B.length network_out1 == SZ.v network_out_cap /\
                (ok ==> s'.R.seq == 's.R.seq + 1) /\
                (not ok ==> s' == 's))
{
  let inner_len = SZ.(chunk_len +^ 1sz);
  let cipher_len = SZ.(inner_len +^ 16sz);
  let wire_len = SZ.(5sz +^ cipher_len);
  let cipher_offset = SZ.(wire_offset +^ 5sz);
  assert (pure (SZ.v cipher_len == SZ.v chunk_len + 17));
  assert (pure (SZ.v wire_len == SZ.v chunk_len + 22));
  assert (pure (SZ.v wire_offset + SZ.v wire_len <= SZ.v network_out_cap));
  let mut header = [| 0uy; 5sz |];
  let mut inner_plaintext = [| 0uy; inner_len |];
  let mut cipher = [| 0uy; cipher_len |];
  RF.serialize_application_data_header
    (Cast.uint32_to_uint16 (SZ.sizet_to_uint32 cipher_len))
    header
    5sz;
  RF.encode_inner_plaintext_no_padding_slice
    app_in
    app_in_len
    plain_offset
    chunk_len
    23uy
    inner_plaintext
    inner_len;
  with inner_bytes. assert (pts_to inner_plaintext inner_bytes);
  with cipher_old. assert (pts_to cipher cipher_old);
  assert (pure (B.length inner_bytes == SZ.v inner_len));
  assert (pure (B.length cipher_old == SZ.v cipher_len));
  assert (pure (B.length cipher_old == SZ.v inner_len + 16));
  let sealed = Rec.seal_application_runtime
    record_state
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
    assert (pure (5 + SZ.v cipher_len == SZ.v wire_len));
    assert (pure (SZ.v wire_offset + 5 <= SZ.v network_out_cap));
    copy_payload_to_output header 5sz 5sz network_out network_out_cap wire_offset;
    with network_after_header. assert (pts_to network_out network_after_header);
    assert (pure (B.length network_after_header == SZ.v network_out_cap));
    assert (pure (SZ.v cipher_offset + SZ.v cipher_len <= SZ.v network_out_cap));
    copy_payload_to_output cipher cipher_len cipher_len network_out network_out_cap cipher_offset;
    with network_out1. assert (pts_to network_out network_out1);
    with s'. assert (Rec.is_record_state record_state s');
    assert (pure (B.length network_out1 == SZ.v network_out_cap));
    assert (pure (s'.R.seq == 's.R.seq + 1));
    sealed
  } else {
    with network_out1. assert (pts_to network_out network_out1);
    with s'. assert (Rec.is_record_state record_state s');
    assert (pure (B.length network_out1 == SZ.v network_out_cap));
    assert (pure (s' == 's));
    sealed
  }
}

type seal_records_result = {
  seal_records_ok: bool;
  seal_records_len: SZ.t;
}

fn rec seal_application_records_to_output
  (record_state: Rec.record_state)
  (app_in: array U8.t)
  (app_in_len: SZ.t)
  (plain_offset: SZ.t)
  (remaining: SZ.t)
  (network_out: array U8.t)
  (network_out_cap: SZ.t)
  (wire_offset: SZ.t)
  requires Rec.is_record_state record_state 's **
           pts_to app_in 'app_bytes **
           pts_to network_out 'network_out0 **
           pure (B.length 'app_bytes == SZ.v app_in_len /\
                 B.length 'network_out0 == SZ.v network_out_cap /\
                 SZ.v plain_offset + SZ.v remaining == SZ.v app_in_len /\
                 SZ.v wire_offset <= SZ.v network_out_cap /\
                 U64.fits ('s.R.seq + S.application_data_record_count_len (SZ.v remaining)))
  returns result: seal_records_result
  ensures exists* s' network_out1.
           Rec.is_record_state record_state s' **
           pts_to app_in 'app_bytes **
           pts_to network_out network_out1 **
           pure (B.length network_out1 == SZ.v network_out_cap /\
                 (result.seal_records_ok ==>
                   s'.R.seq == 's.R.seq + S.application_data_record_count_len (SZ.v remaining) /\
                   SZ.v wire_offset + SZ.v result.seal_records_len <= SZ.v network_out_cap) /\
                 (not result.seal_records_ok ==> result.seal_records_len == 0sz))
  decreases (SZ.v remaining)
{
  assert (pure (S.max_application_data_fragment_len == SZ.v tls_application_plaintext_max));
  let chunk_len =
    if SZ.(remaining <=^ tls_application_plaintext_max) {
      remaining
    } else {
      tls_application_plaintext_max
    };
  assert (pure (SZ.v chunk_len <= SZ.v tls_application_plaintext_max));
  assert (pure (SZ.v plain_offset + SZ.v chunk_len <= SZ.v app_in_len));
  let inner_len = SZ.(chunk_len +^ 1sz);
  let cipher_len = SZ.(inner_len +^ 16sz);
  let wire_len = SZ.(5sz +^ cipher_len);
  assert (pure (SZ.v cipher_len == SZ.v chunk_len + 17));
  assert (pure (SZ.v wire_len == 5 + (SZ.v chunk_len + 17)));
  let available = SZ.(network_out_cap -^ wire_offset);
  assert (pure (SZ.v available == SZ.v network_out_cap - SZ.v wire_offset));
  lemma_nat_add_sub_cancel 0 (SZ.v wire_offset) (SZ.v network_out_cap);
  assert (pure (SZ.v wire_offset + SZ.v available == SZ.v network_out_cap));
  if SZ.(wire_len <=^ available) {
    assert (pure (SZ.v wire_offset + SZ.v wire_len <= SZ.v network_out_cap));
    S.lemma_application_data_record_count_len_positive (SZ.v remaining);
    lemma_u64_fits_add_one_of_count 's.R.seq (S.application_data_record_count_len (SZ.v remaining));
    let sealed = seal_application_record_to_output
      record_state
      app_in
      app_in_len
      plain_offset
      chunk_len
      network_out
      network_out_cap
      wire_offset;
    with network_after_chunk. assert (pts_to network_out network_after_chunk);
    with s_after_chunk. assert (Rec.is_record_state record_state s_after_chunk);
    assert (pure (B.length network_after_chunk == SZ.v network_out_cap));
    if sealed {
      assert (pure (s_after_chunk.R.seq == 's.R.seq + 1));
      if SZ.(remaining <=^ tls_application_plaintext_max) {
        S.lemma_application_data_record_count_len_small (SZ.v remaining);
        assert (pure (s_after_chunk.R.seq == 's.R.seq + S.application_data_record_count_len (SZ.v remaining)));
        let result = { seal_records_ok = true; seal_records_len = wire_len };
        assert (pure (B.length network_after_chunk == SZ.v network_out_cap));
        assert (pure (SZ.v wire_offset + SZ.v result.seal_records_len <= SZ.v network_out_cap));
        result
      } else {
        assert (pure (SZ.v tls_application_plaintext_max < SZ.v remaining));
        assert (pure (chunk_len == tls_application_plaintext_max));
        let plain_offset' = SZ.(plain_offset +^ chunk_len);
        let remaining' = SZ.(remaining -^ chunk_len);
        let wire_offset' = SZ.(wire_offset +^ wire_len);
        assert (pure (SZ.v remaining' == SZ.v remaining - SZ.v tls_application_plaintext_max));
        assert (pure (SZ.v remaining' < SZ.v remaining));
        assert (pure (SZ.v plain_offset' + SZ.v remaining' == SZ.v app_in_len));
        assert (pure (SZ.v wire_offset' == SZ.v wire_offset + SZ.v wire_len));
        assert (pure (SZ.v wire_offset' <= SZ.v network_out_cap));
        S.lemma_application_data_record_count_len_step (SZ.v remaining);
        assert (pure (S.application_data_record_count_len (SZ.v remaining) ==
                      1 + S.application_data_record_count_len (SZ.v remaining')));
        assert (pure (s_after_chunk.R.seq + S.application_data_record_count_len (SZ.v remaining') ==
                      's.R.seq + S.application_data_record_count_len (SZ.v remaining)));
        assert (pure (U64.fits (s_after_chunk.R.seq + S.application_data_record_count_len (SZ.v remaining'))));
        let tail = seal_application_records_to_output
          record_state
          app_in
          app_in_len
          plain_offset'
          remaining'
          network_out
          network_out_cap
          wire_offset';
        with network_out1. assert (pts_to network_out network_out1);
        with s'. assert (Rec.is_record_state record_state s');
        assert (pure (B.length network_out1 == SZ.v network_out_cap));
        if tail.seal_records_ok {
          assert (pure (s'.R.seq == s_after_chunk.R.seq + S.application_data_record_count_len (SZ.v remaining')));
          assert (pure (s'.R.seq == 's.R.seq + S.application_data_record_count_len (SZ.v remaining)));
          assert (pure (SZ.v wire_offset' + SZ.v tail.seal_records_len <= SZ.v network_out_cap));
          assert (pure (SZ.v wire_offset + SZ.v wire_len + SZ.v tail.seal_records_len <= SZ.v network_out_cap));
          assert (pure (SZ.v wire_len + SZ.v tail.seal_records_len <= SZ.v network_out_cap));
          let total_len = SZ.(wire_len +^ tail.seal_records_len);
          assert (pure (SZ.v total_len == SZ.v wire_len + SZ.v tail.seal_records_len));
          assert (pure (SZ.v wire_offset + SZ.v total_len <= SZ.v network_out_cap));
          let result = { seal_records_ok = true; seal_records_len = total_len };
          result
        } else {
          let result = { seal_records_ok = false; seal_records_len = 0sz };
          result
        }
      }
    } else {
      let result = { seal_records_ok = false; seal_records_len = 0sz };
      result
    }
  } else {
    let result = { seal_records_ok = false; seal_records_len = 0sz };
    result
  }
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
    request_record_sequence_fits
      kind
      view0
      (Ghost.reveal 'network_in_bytes)
      (Ghost.reveal 'app_in_bytes) /\
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
    with client_record_s0. assert (Rec.is_record_state c.client_application_record_state client_record_s0);
    with server_record_s0. assert (Rec.is_record_state c.server_application_record_state server_record_s0);
    assert (pure (client_record_s0.R.seq == view0.CL.state.S.write_state.R.seq));
    assert (pure (server_record_s0.R.seq == view0.CL.state.S.read_state.R.seq));
    assert (pure (S.application_data_record_count (Ghost.reveal app_bytes) ==
                  S.application_data_record_count_len (SZ.v app_in_len)));
    assert (pure (U64.fits (client_record_s0.R.seq + S.application_data_record_count_len (SZ.v app_in_len))));
    let sealed = seal_application_records_to_output
      c.client_application_record_state
      app_in
      app_in_len
      0sz
      app_in_len
      network_out
      network_out_cap
      0sz;
    with network_out1. assert (pts_to network_out network_out1);
    with client_record_s1. assert (Rec.is_record_state c.client_application_record_state client_record_s1);
    assert (pure (B.length network_out1 == SZ.v network_out_cap));
    if sealed.seal_records_ok {
      let total_wire_len = sealed.seal_records_len;
      assert (pure (SZ.v total_wire_len <= SZ.v network_out_cap));
      assert (pure (client_record_s1.R.seq ==
                    client_record_s0.R.seq + S.application_data_record_count_len (SZ.v app_in_len)));
      let raw : erased CL.raw_io_log =
        CL.append_raw_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v total_wire_len);
      CL.lemma_raw_io_log_extends_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v total_wire_len);
      CL.lemma_raw_io_log_same_received_sent_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v total_wire_len);
      let raw_view : erased CL.connection_view = CL.sync_raw_state view0 (Ghost.reveal raw) view0.CL.state;
      CL.lemma_connection_view_consistent_sync_raw_same_state view0 (Ghost.reveal raw);
      assert (pure ((Ghost.reveal raw_view).CL.state == view0.CL.state));
      assert (pure ((Ghost.reveal raw_view).CL.app_view == view0.CL.app_view));
      assert (pure (CL.raw_io_log_extends view0.CL.raw_log (Ghost.reveal raw_view).CL.raw_log));
      assert (pure (CL.raw_io_log_same_received view0.CL.raw_log (Ghost.reveal raw_view).CL.raw_log));
      let send_state : erased S.conn_state =
        S.advance_write_records view0.CL.state (S.application_data_record_count (Ghost.reveal app_bytes));
      S.lemma_advance_write_records_write_seq view0.CL.state (S.application_data_record_count (Ghost.reveal app_bytes));
      S.lemma_advance_write_records_preserves_phase view0.CL.state (S.application_data_record_count (Ghost.reveal app_bytes));
      S.lemma_advance_write_records_preserves_read_state view0.CL.state (S.application_data_record_count (Ghost.reveal app_bytes));
      assert (pure ((Ghost.reveal send_state).S.write_state.R.seq ==
                    view0.CL.state.S.write_state.R.seq + S.application_data_record_count (Ghost.reveal app_bytes)));
      assert (pure ((Ghost.reveal send_state).S.phase == S.ApplicationData));
      assert (pure ((Ghost.reveal send_state).S.read_state == view0.CL.state.S.read_state));
      assert (pure (client_record_s1.R.seq == (Ghost.reveal send_state).S.write_state.R.seq));
      ST.advance c.state (S.SendApplicationData (Ghost.reveal app_bytes)) (Ghost.reveal send_state);
      let view1 : erased CL.connection_view =
        CL.note_app_sent (Ghost.reveal raw_view) (Ghost.reveal app_bytes) (Ghost.reveal send_state);
      CL.lemma_step_send_application_data_success
        view0
        (Ghost.reveal raw_view)
        (Ghost.reveal app_bytes)
        (Ghost.reveal send_state);
      assert (pure (CL.connection_view_consistent (Ghost.reveal view1)));
      assert (pure ((Ghost.reveal view1).CL.state == (Ghost.reveal send_state)));
      assert (pure ((Ghost.reveal view1).CL.pending_app == (Ghost.reveal raw_view).CL.pending_app));
      assert (pure ((Ghost.reveal view1).CL.pending_received_raw == (Ghost.reveal raw_view).CL.pending_received_raw));
      assert (pure ((Ghost.reveal raw_view).CL.pending_app == view0.CL.pending_app));
      assert (pure ((Ghost.reveal raw_view).CL.pending_received_raw == view0.CL.pending_received_raw));
      assert (pure (Seq.equal (Ghost.reveal view1).CL.pending_app view0.CL.pending_app));
      assert (pure (Seq.equal (Ghost.reveal view1).CL.pending_received_raw view0.CL.pending_received_raw));
      assert (pure (server_record_s0.R.seq == (Ghost.reveal view1).CL.state.S.read_state.R.seq));
      assert (pure (record_states_match_view client_record_s1 server_record_s0 (Ghost.reveal view1)));
      ST.advance_log c.log (Ghost.reveal view1);
      let result = { network_out_len = total_wire_len; app_out_len = 0sz; status = CL.ActionComplete };
      let resp : erased CL.client_response =
        CL.response_with_sent_raw_delta view0.CL.raw_log (Ghost.reveal view1).CL.raw_log B.empty CL.ActionComplete;
      CL.lemma_raw_sent_delta_append_slice view0.CL.raw_log (Ghost.reveal network_out1) 0 (SZ.v total_wire_len);
      assert (pure ((Ghost.reveal resp).CL.network_out == CL.raw_slice (Ghost.reveal network_out1) 0 (SZ.v total_wire_len)));
      assert (pure (CL.raw_slice (Ghost.reveal network_out1) 0 (SZ.v total_wire_len) ==
                    Seq.slice (Ghost.reveal network_out1) 0 (SZ.v total_wire_len)));
      lemma_prefix_slice (Ghost.reveal network_out1) (SZ.v total_wire_len);
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
      lemma_empty_prefix (Ghost.reveal network_out1);
      lemma_empty_prefix (Ghost.reveal 'app_out0);
      assert (pure (response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal 'app_out0) resp));
      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal network_out1) (Ghost.reveal 'app_out0) mresp /\
                                CL.step view0 mreq (Ghost.reveal view1) mresp));
      fold (is_client_core c (Ghost.reveal view1));
      result
    }
  } else if KReadApplicationData? kind {
    let network_bytes : erased B.bytes = Ghost.reveal 'network_in_bytes;
    assert (pure (mreq == CL.request_with_network_in (CL.OpReadApplicationData (SZ.v requested_app_len)) (Ghost.reveal network_bytes)));
    with client_record_s0. assert (Rec.is_record_state c.client_application_record_state client_record_s0);
    with server_record_s0. assert (Rec.is_record_state c.server_application_record_state server_record_s0);
    assert (pure (record_states_match_view client_record_s0 server_record_s0 view0));
    assert (pure (server_record_s0.R.seq == view0.CL.state.S.read_state.R.seq));
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
        assert (pure (SZ.v pending_read_offset' == SZ.v pending_read_offset + SZ.v copy_len));
        assert (pure (Seq.equal
          (Ghost.reveal app_payload)
          (Seq.slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset)
            (SZ.v pending_read_offset'))));
        assert (pure (CL.raw_slice
          (Ghost.reveal pending_buffer1)
          (SZ.v pending_read_offset)
          (SZ.v pending_read_offset') ==
          Seq.slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset)
            (SZ.v pending_read_offset')));
        assert (pure (Seq.equal
          (Ghost.reveal app_payload)
          (CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset)
            (SZ.v pending_read_offset'))));
        assert (pure (CL.raw_slice
          (Ghost.reveal pending_buffer1)
          (SZ.v pending_read_offset')
          (SZ.v pending_read_len) ==
          Seq.slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset')
            (SZ.v pending_read_len)));
        assert (pure (Seq.equal
          (Ghost.reveal pending_payload)
          (Seq.slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset')
            (SZ.v pending_read_len))));
        assert (pure (Seq.equal
          (Ghost.reveal pending_payload)
          (CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset')
            (SZ.v pending_read_len))));
        CL.lemma_raw_slice_split
          (Ghost.reveal pending_buffer1)
          (SZ.v pending_read_offset)
          (SZ.v pending_read_offset')
          (SZ.v pending_read_len);
        Seq.lemma_eq_elim
          (Ghost.reveal app_payload)
          (CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset)
            (SZ.v pending_read_offset'));
        Seq.lemma_eq_elim
          (Ghost.reveal pending_payload)
          (CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset')
            (SZ.v pending_read_len));
        assert (pure (Seq.equal
          (CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset)
            (SZ.v pending_read_len))
          (B.append
            (Ghost.reveal app_payload)
            (Ghost.reveal pending_payload))));
        assert (pure ((Ghost.reveal view1).CL.pending_app == view0.CL.pending_app));
        assert (pure (Seq.equal
          view0.CL.pending_app
          (CL.raw_slice
            (Ghost.reveal pending_buffer1)
            (SZ.v pending_read_offset)
            (SZ.v pending_read_len))));
        assert (pure (Seq.equal
          (Ghost.reveal view1).CL.pending_app
          (B.append (Ghost.reveal app_payload) (Ghost.reveal pending_payload))));
        CL.lemma_note_app_delivered_with_pending_source_consistent
          (Ghost.reveal view1)
          (Ghost.reveal app_payload)
          (Ghost.reveal pending_payload);
        let view2 : erased CL.connection_view =
          CL.note_app_delivered_with_pending
            (Ghost.reveal view1)
            (Ghost.reveal app_payload)
            (Ghost.reveal pending_payload);
        assert (pure (CL.pending_app_source_consistent (Ghost.reveal view2)));
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
      V.pts_to_len c.pending_network_buffer;
      with pending_network_buffer0. assert (V.pts_to c.pending_network_buffer pending_network_buffer0);
      assert (pure (B.length (Ghost.reveal pending_network_buffer0) == SZ.v pending_network_buffer_capacity));
      assert (pure (CL.raw_slice
        (Ghost.reveal pending_network_buffer0)
        0
        (SZ.v pending_network_len) ==
        Seq.slice
          (Ghost.reveal pending_network_buffer0)
          0
          (SZ.v pending_network_len)));
      Seq.lemma_len_slice
        (Ghost.reveal pending_network_buffer0)
        0
        (SZ.v pending_network_len);
      assert (pure (B.length view0.CL.pending_received_raw == SZ.v pending_network_len));
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
                V.to_vec_pts_to c.pending_network_buffer;
                set_pending_network_from_slice
                  c
                  residual_tmp
                  residual_len
                  0sz
                  residual_len;
                with pending_network_buffer2. assert (V.pts_to c.pending_network_buffer pending_network_buffer2);
                let pending_raw_payload : erased B.bytes =
                  CL.raw_slice
                    (Ghost.reveal residual_tmp_bytes)
                    0
                    (SZ.v residual_len);
                assert (pure (CL.raw_slice (Ghost.reveal residual_tmp_bytes) 0 (SZ.v residual_len) ==
                              Seq.slice (Ghost.reveal residual_tmp_bytes) 0 (SZ.v residual_len)));
                assert (pure (Seq.equal
                  (Ghost.reveal pending_raw_payload)
                  (CL.raw_slice (Ghost.reveal pending_network_buffer2) 0 (SZ.v residual_len))));
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
                      with inner_bytes. assert (pts_to inner inner_bytes);
                      assert (pure (B.length inner_bytes == SZ.v inner_len));
                      assert (pure (Seq.equal
                        (Ghost.reveal app_payload)
                        (Seq.slice (Ghost.reveal inner_bytes) 0 (SZ.v payload_len))));
                      assert (pure (view0.CL.state.S.phase == S.ApplicationData));
                      lemma_step_recv_application_data view0.CL.state (Ghost.reveal app_payload);
                      assert (pure (S.step view0.CL.state (S.RecvApplicationData (Ghost.reveal app_payload)) ==
                                    Some (S.advance_read_record view0.CL.state)));
                      ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                      let chunks_single : erased (list B.bytes) =
                        [Ghost.reveal app_payload];
                      assert (pure (U64.fits
                        (view0.CL.state.S.read_state.R.seq +
                         (B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes) + 1))));
                      assert (pure (CL.chunk_count [] == 0));
                      lemma_u64_fits_next_after_consumed_of_budget
                        view0.CL.state.S.read_state.R.seq
                        (CL.chunk_count [])
                        (B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes));
                      assert (pure (0 < B.length view0.CL.pending_received_raw));
                      assert (pure (1 <= B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes)));
                      assert (pure (CL.chunk_count (Ghost.reveal chunks_single) == 1));
                      lemma_u64_fits_next_after_consumed_of_budget
                        view0.CL.state.S.read_state.R.seq
                        (CL.chunk_count (Ghost.reveal chunks_single))
                        (B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes));
                      assert (pure (U64.fits (view0.CL.state.S.read_state.R.seq + 1)));
                      assert (pure (U64.fits (view0.CL.state.S.read_state.R.seq + 2)));
                      with server_record_s1. assert (Rec.is_record_state c.server_application_record_state server_record_s1);
                      assert (pure (U64.fits (server_record_s0.R.seq + 1)));
                      assert (pure (server_record_s1.R.seq == server_record_s0.R.seq + 1));
                      assert (pure (server_record_s1.R.seq == view0.CL.state.S.read_state.R.seq + 1));
                      assert (pure (server_record_s1.R.seq ==
                                    view0.CL.state.S.read_state.R.seq +
                                    CL.chunk_count (Ghost.reveal chunks_single)));
                      assert (pure (U64.fits (server_record_s1.R.seq + 1)));
                      CL.lemma_concat_bytes_singleton (Ghost.reveal app_payload);
                      assert (pure (Seq.equal
                        (Ghost.reveal app_payload)
                        (CL.concat_bytes (Ghost.reveal chunks_single))));
                      let resp_single : erased CL.client_response =
                        CL.read_application_data_chunks_success_response
                          (Ghost.reveal app_payload)
                          (Ghost.reveal chunks_single);
                      CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                      let view_single : erased CL.connection_view =
                        CL.read_application_data_chunks_success_view
                          (Ghost.reveal view1)
                          (Ghost.reveal chunks_single)
                          (Ghost.reveal pending_raw_payload);
                      CL.lemma_step_read_application_data_chunks_success_exit
                        view0
                        (Ghost.reveal view1)
                        (SZ.v requested_app_len)
                        (Ghost.reveal app_payload)
                        (Ghost.reveal chunks_single)
                        (Ghost.reveal pending_raw_payload);
                      assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view_single).CL.raw_log));
                      assert (pure (CL.step view0 mreq (Ghost.reveal view_single) (Ghost.reveal resp_single)));
                      if SZ.(5sz <=^ residual_len) {
                        let record2_cursor = 0sz;
                        assert (pure (SZ.v record2_cursor == 0));
                        let record2_header_end = SZ.(record2_cursor +^ 5sz);
                        assert (pure (SZ.v record2_header_end == SZ.v record2_cursor + 5));
                        assert (pure (SZ.v record2_header_end == 5));
                        assert (pure (SZ.v record2_header_end <= SZ.v residual_len));
                        let mut header2 = [| 0uy; 5sz |];
                        copy_payload_to_output_loop
                          residual_tmp
                          residual_len
                          header2
                          5sz
                          record2_cursor
                          0sz
                          5sz;
                        with header2_bytes. assert (pts_to header2 header2_bytes);
                        assert (pure (B.length header2_bytes == 5));
                        let mut content_type2_out = [| 0uy; 1sz |];
                        let mut fragment_len2_out = [| 0uy; 2sz |];
                        let header2_parse_ok =
                          RF.parse_record_header header2 5sz content_type2_out 1sz fragment_len2_out 2sz;
                        if header2_parse_ok {
                          let content_type2 = content_type2_out.(0sz);
                          let frag2_hi = fragment_len2_out.(0sz);
                          let frag2_lo = fragment_len2_out.(1sz);
                          let frag2_hi16 = Cast.uint8_to_uint16 frag2_hi;
                          let frag2_lo16 = Cast.uint8_to_uint16 frag2_lo;
                          let frag2_16 = U16.logor (U16.shift_left frag2_hi16 8ul) frag2_lo16;
                          let fragment2_len = SZ.uint16_to_sizet frag2_16;
                          let remaining2_len = SZ.(residual_len -^ record2_header_end);
                          assert (pure (SZ.v remaining2_len == SZ.v residual_len - SZ.v record2_header_end));
                          assert (pure (SZ.v remaining2_len == SZ.v residual_len - 5));
                          if (content_type2 = 23uy &&
                              SZ.(16sz <^ fragment2_len) &&
                              SZ.(fragment2_len <=^ remaining2_len)) {
                            assert (pure (SZ.v fragment2_len <= SZ.v remaining2_len));
                            assert (pure (5 + SZ.v fragment2_len <= SZ.v residual_len));
                            assert (pure (SZ.v record2_cursor + 5 + SZ.v fragment2_len <= SZ.v residual_len));
                            let record2_lengths =
                              residual_frame_lengths_at residual_len record2_cursor fragment2_len;
                            let record2_wire_len = record2_lengths.residual_frame_at_wire_len;
                            assert (pure (SZ.v record2_wire_len == 5 + SZ.v fragment2_len));
                            assert (pure (SZ.v record2_wire_len <= SZ.v residual_len));
                            let record2_end = record2_lengths.residual_frame_at_end;
                            assert (pure (SZ.v record2_end == SZ.v record2_wire_len));
                            let residual_after_two_len = record2_lengths.residual_frame_at_tail_len;
                            assert (pure (SZ.v residual_after_two_len == SZ.v residual_len - SZ.v record2_end));
                            assert (pure (SZ.v record2_end + SZ.v residual_after_two_len == SZ.v residual_len));
                            assert (pure (SZ.v residual_after_two_len <= SZ.v pending_network_buffer_capacity));
                            let record2_cipher_offset = record2_header_end;
                            assert (pure (SZ.v record2_cipher_offset == SZ.v record2_cursor + 5));
                            assert (pure (SZ.v record2_cipher_offset == 5));
                            assert (pure (SZ.v record2_cipher_offset + SZ.v fragment2_len ==
                                          5 + SZ.v fragment2_len));
                            assert (pure (SZ.v record2_cipher_offset + SZ.v fragment2_len ==
                                          SZ.v record2_wire_len));
                            assert (pure (SZ.v record2_cipher_offset + SZ.v fragment2_len ==
                                          SZ.v record2_end));
                            assert (pure (SZ.v record2_end + SZ.v residual_after_two_len ==
                                          SZ.v residual_len));
                            let mut cipher2 = [| 0uy; fragment2_len |];
                            copy_payload_to_output_loop
                              residual_tmp
                              residual_len
                              cipher2
                              fragment2_len
                              record2_cipher_offset
                              0sz
                              fragment2_len;
                            with cipher2_bytes. assert (pts_to cipher2 cipher2_bytes);
                            assert (pure (B.length cipher2_bytes == SZ.v fragment2_len));
                            assert (pure (SZ.v 16sz == 16));
                            assert (pure (16 < SZ.v fragment2_len));
                            assert (pure (16 <= SZ.v fragment2_len));
                            let inner2_len = SZ.(fragment2_len -^ 16sz);
                            assert (pure (SZ.v inner2_len > 0));
                            let mut inner2 = [| 0uy; inner2_len |];
                            with inner2_old. assert (pts_to inner2 inner2_old);
                            assert (pure (B.length inner2_old == SZ.v inner2_len));
                            assert (pure (B.length inner2_old + 16 == SZ.v fragment2_len));
                            let opened2_peek =
                              Rec.peek_open_application
                                c.server_application_record_state
                                header2
                                5sz
                                cipher2
                                fragment2_len
                                inner2;
                            if opened2_peek {
                              let mut inner_content_type2_out = [| 0uy; 1sz |];
                              let payload2_len =
                                RF.decode_inner_plaintext inner2 inner2_len inner_content_type2_out 1sz;
                              let inner_content_type2 = inner_content_type2_out.(0sz);
                              let remaining_requested = SZ.(requested_app_len -^ payload_len);
                              let remaining_app_cap = SZ.(app_out_cap -^ payload_len);
                              assert (pure (SZ.v remaining_requested == SZ.v requested_app_len - SZ.v payload_len));
                              assert (pure (SZ.v remaining_app_cap == SZ.v app_out_cap - SZ.v payload_len));
                              if (inner_content_type2 = 23uy &&
                                  SZ.(payload2_len <=^ remaining_requested) &&
                                  SZ.(payload2_len <=^ remaining_app_cap)) {
                                assert (pure (SZ.v payload_len + SZ.v payload2_len <= SZ.v requested_app_len));
                                assert (pure (SZ.v payload_len + SZ.v payload2_len <= SZ.v app_out_cap));
                                let total_payload_len = SZ.(payload_len +^ payload2_len);
                                assert (pure (SZ.v total_payload_len == SZ.v payload_len + SZ.v payload2_len));
                                assert (pure (SZ.v total_payload_len <= SZ.v app_out_cap));
                                assert (pure (SZ.v total_payload_len <= SZ.v requested_app_len));
                                with inner2_bytes_peek. assert (pts_to inner2 inner2_bytes_peek);
                                assert (pure (B.length inner2_bytes_peek == SZ.v inner2_len));
                                let mut payload2_tmp = [| 0uy; payload2_len |];
                                copy_payload_to_output
                                  inner2
                                  inner2_len
                                  payload2_len
                                  payload2_tmp
                                  payload2_len
                                  0sz;
                                with payload2_tmp_bytes. assert (pts_to payload2_tmp payload2_tmp_bytes);
                                assert (pure (B.length payload2_tmp_bytes == SZ.v payload2_len));
                                assert (pure (Seq.equal
                                  (Seq.slice payload2_tmp_bytes 0 (SZ.v payload2_len))
                                  (Seq.slice inner2_bytes_peek 0 (SZ.v payload2_len))));
                                let opened2 =
                                  Rec.open_application_runtime
                                    c.server_application_record_state
                                    header2
                                    5sz
                                    cipher2
                                    fragment2_len
                                    inner2;
                                if opened2 {
                                  with server_record_s2. assert (Rec.is_record_state c.server_application_record_state server_record_s2);
                                  assert (pure (server_record_s2.R.seq == server_record_s1.R.seq + 1));
                                  assert (pure (server_record_s2.R.seq == view0.CL.state.S.read_state.R.seq + 2));
                                  copy_payload_to_output_loop
                                    payload2_tmp
                                    payload2_len
                                    app_out
                                    app_out_cap
                                    0sz
                                    payload_len
                                    payload2_len;
                                  with app_out2. assert (pts_to app_out app_out2);
                                  assert (pure (B.length app_out2 == SZ.v app_out_cap));
                                  assert (pure (Seq.equal
                                    (Seq.slice app_out2 (SZ.v payload_len) (SZ.v total_payload_len))
                                    (Seq.slice payload2_tmp_bytes 0 (SZ.v payload2_len))));
                                  assert (pure (Seq.equal
                                    (Seq.slice app_out2 0 (SZ.v payload_len))
                                    (Seq.slice app_out1 0 (SZ.v payload_len))));
                                  let app_payload2 : erased B.bytes =
                                    Seq.slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len);
                                  let app_payload_total : erased B.bytes =
                                    Seq.slice (Ghost.reveal app_out2) 0 (SZ.v total_payload_len);
                                  assert (pure (Seq.equal
                                    (Ghost.reveal app_payload2)
                                    (Seq.slice (Ghost.reveal payload2_tmp_bytes) 0 (SZ.v payload2_len))));
                                  assert (pure (Seq.equal
                                    (Ghost.reveal app_payload)
                                    (Seq.slice (Ghost.reveal app_out2) 0 (SZ.v payload_len))));
                                  assert (pure (CL.raw_slice (Ghost.reveal app_out2) 0 (SZ.v total_payload_len) ==
                                                Seq.slice (Ghost.reveal app_out2) 0 (SZ.v total_payload_len)));
                                  assert (pure (CL.raw_slice (Ghost.reveal app_out2) 0 (SZ.v payload_len) ==
                                                Seq.slice (Ghost.reveal app_out2) 0 (SZ.v payload_len)));
                                  assert (pure (CL.raw_slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len) ==
                                                Seq.slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len)));
                                  assert (pure (Seq.equal
                                    (Ghost.reveal app_payload)
                                    (CL.raw_slice (Ghost.reveal app_out2) 0 (SZ.v payload_len))));
                                  assert (pure (Seq.equal
                                    (Ghost.reveal app_payload2)
                                    (CL.raw_slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len))));
                                  assert (pure (CL.connection_view_consistent (Ghost.reveal view1)));
                                  assert (pure ((Ghost.reveal view1).CL.state.S.phase == S.ApplicationData));
                                  let chunks_after_second : erased (list B.bytes) =
                                    L.append (Ghost.reveal chunks_single) [Ghost.reveal app_payload2];
                                  CL.lemma_chunk_count_snoc
                                    (Ghost.reveal chunks_single)
                                    (Ghost.reveal app_payload2);
                                  assert (pure (CL.chunk_count (Ghost.reveal chunks_after_second) ==
                                                CL.chunk_count (Ghost.reveal chunks_single) + 1));
                                  assert (pure (server_record_s2.R.seq ==
                                                view0.CL.state.S.read_state.R.seq +
                                                CL.chunk_count (Ghost.reveal chunks_after_second)));
                                  CL.lemma_note_app_received_chunks_loop_accept_output
                                    (Ghost.reveal view1)
                                    (Ghost.reveal chunks_single)
                                    (Ghost.reveal app_payload2)
                                    (Ghost.reveal app_out2)
                                    (SZ.v payload_len)
                                    (SZ.v total_payload_len)
                                    (Ghost.reveal app_payload)
                                    (Ghost.reveal app_payload_total);
                                  assert (pure (Seq.equal
                                    (Ghost.reveal app_payload_total)
                                    (CL.concat_bytes (Ghost.reveal chunks_after_second))));
                                  set_pending_network_from_slice
                                    c
                                    residual_tmp
                                    residual_len
                                    record2_end
                                    residual_after_two_len;
                                  with pending_network_buffer3. assert (V.pts_to c.pending_network_buffer pending_network_buffer3);
                                  let pending_raw_payload2 : erased B.bytes =
                                    CL.raw_slice
                                      (Ghost.reveal residual_tmp_bytes)
                                      (SZ.v record2_end)
                                      (SZ.v residual_len);
                                  assert (pure (CL.raw_slice
                                    (Ghost.reveal residual_tmp_bytes)
                                    (SZ.v record2_end)
                                    (SZ.v residual_len) ==
                                    Seq.slice
                                      (Ghost.reveal residual_tmp_bytes)
                                      (SZ.v record2_end)
                                      (SZ.v residual_len)));
                                  assert (pure (Seq.equal
                                    (Ghost.reveal pending_raw_payload2)
                                    (CL.raw_slice (Ghost.reveal pending_network_buffer3) 0 (SZ.v residual_after_two_len))));
                                  assert (pure ((S.advance_read_record view0.CL.state).S.phase == S.ApplicationData));
                                  lemma_step_recv_application_data
                                    (S.advance_read_record view0.CL.state)
                                    (Ghost.reveal app_payload2);
                                  assert (pure (S.step
                                    (S.advance_read_record view0.CL.state)
                                    (S.RecvApplicationData (Ghost.reveal app_payload2)) ==
                                    Some (S.advance_read_record (S.advance_read_record view0.CL.state))));
                                  ST.advance
                                    c.state
                                    (S.RecvApplicationData (Ghost.reveal app_payload2))
                                    (S.advance_read_record (S.advance_read_record view0.CL.state));
                                  let view2 : erased CL.connection_view =
                                    CL.read_application_data_chunks_success_view
                                      (Ghost.reveal view1)
                                      (Ghost.reveal chunks_after_second)
                                      (Ghost.reveal pending_raw_payload2);
                                  let resp : erased CL.client_response =
                                    CL.read_application_data_chunks_success_response
                                      (Ghost.reveal app_payload_total)
                                      (Ghost.reveal chunks_after_second);
                                  CL.lemma_step_read_application_data_chunks_success_exit
                                    view0
                                    (Ghost.reveal view1)
                                    (SZ.v requested_app_len)
                                    (Ghost.reveal app_payload_total)
                                    (Ghost.reveal chunks_after_second)
                                    (Ghost.reveal pending_raw_payload2);
                                  assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                                  ST.advance_log c.log (Ghost.reveal view2);
                                  let result = { network_out_len = 0sz; app_out_len = total_payload_len; status = CL.ApplicationDataReady };
                                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                                  lemma_prefix_slice (Ghost.reveal app_out2) (SZ.v total_payload_len);
                                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out2) (Ghost.reveal resp)));
                                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out2) mresp /\
                                                            CL.step view0 mreq (Ghost.reveal view2) mresp));
                                  fold (is_client_core c (Ghost.reveal view2));
                                  result
                                } else {
                                  ST.advance_log c.log (Ghost.reveal view_single);
                                  let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                                  lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                            CL.step view0 mreq (Ghost.reveal view_single) mresp));
                                  fold (is_client_core c (Ghost.reveal view_single));
                                  result
                                }
                              } else {
                                ST.advance_log c.log (Ghost.reveal view_single);
                                let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                                lemma_empty_prefix (Ghost.reveal 'network_out0);
                                lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                                assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                                assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                          CL.step view0 mreq (Ghost.reveal view_single) mresp));
                                fold (is_client_core c (Ghost.reveal view_single));
                                result
                              }
                            } else {
                              ST.advance_log c.log (Ghost.reveal view_single);
                              let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                              lemma_empty_prefix (Ghost.reveal 'network_out0);
                              lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                              assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                              assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                        CL.step view0 mreq (Ghost.reveal view_single) mresp));
                              fold (is_client_core c (Ghost.reveal view_single));
                              result
                            }
                          } else {
                            ST.advance_log c.log (Ghost.reveal view_single);
                            let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                            lemma_empty_prefix (Ghost.reveal 'network_out0);
                            lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                      CL.step view0 mreq (Ghost.reveal view_single) mresp));
                            fold (is_client_core c (Ghost.reveal view_single));
                            result
                          }
                        } else {
                          ST.advance_log c.log (Ghost.reveal view_single);
                          let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                          lemma_empty_prefix (Ghost.reveal 'network_out0);
                          lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                          assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                          assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                    CL.step view0 mreq (Ghost.reveal view_single) mresp));
                          fold (is_client_core c (Ghost.reveal view_single));
                          result
                        }
                      } else {
                        ST.advance_log c.log (Ghost.reveal view_single);
                        let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view_single) mresp));
                        fold (is_client_core c (Ghost.reveal view_single));
                        result
                      }
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
                        assert (pure (Seq.equal
                          (Ghost.reveal app_payload)
                          (Seq.slice (Ghost.reveal inner_bytes) 0 (SZ.v output_limit))));
                        assert (pure (CL.raw_slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len) ==
                                      Seq.slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len)));
                        assert (pure (Seq.equal
                          (Seq.slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len))
                          (Seq.slice (Ghost.reveal inner_bytes) (SZ.v output_limit) (SZ.v payload_len))));
                        assert (pure (Seq.equal
                          (Ghost.reveal pending_payload)
                          (Seq.slice (Ghost.reveal inner_bytes) (SZ.v output_limit) (SZ.v payload_len))));
                        CL.lemma_raw_slice_append_suffix
                          (Ghost.reveal app_payload)
                          (Ghost.reveal pending_payload);
                        assert (pure (view0.CL.state.S.phase == S.ApplicationData));
                        lemma_step_recv_application_data view0.CL.state (Ghost.reveal app_payload);
                        assert (pure (S.step view0.CL.state (S.RecvApplicationData (Ghost.reveal app_payload)) ==
                                      Some (S.advance_read_record view0.CL.state)));
                        ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                        let base_view2 : erased CL.connection_view =
                          CL.note_app_received_with_pending
                            (Ghost.reveal view1)
                            (Ghost.reveal app_payload)
                            (Ghost.reveal pending_payload)
                            (S.advance_read_record view0.CL.state);
                        assert (pure (CL.pending_app_source_consistent (Ghost.reveal base_view2)));
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
              set_pending_network_from_slice
                c
                network_in
                network_in_len
                record_wire_len
                residual_len;
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
            set_pending_network_from_slice
              c
              network_in
              network_in_len
              0sz
              network_in_len;
            with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
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
            let mut residual_tmp = [| 0uy; residual_len |];
            copy_payload_to_output_loop
              network_in
              network_in_len
              residual_tmp
              residual_len
              record_wire_len
              0sz
              residual_len;
            with residual_tmp_bytes. assert (pts_to residual_tmp residual_tmp_bytes);
            assert (pure (B.length residual_tmp_bytes == SZ.v residual_len));
            set_pending_network_from_slice
              c
              residual_tmp
              residual_len
              0sz
              residual_len;
            with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
            let pending_raw_payload : erased B.bytes =
              CL.raw_slice
                (Ghost.reveal residual_tmp_bytes)
                0
                (SZ.v residual_len);
            assert (pure (CL.raw_slice (Ghost.reveal residual_tmp_bytes) 0 (SZ.v residual_len) ==
                          Seq.slice (Ghost.reveal residual_tmp_bytes) 0 (SZ.v residual_len)));
            assert (pure (Seq.equal
              (Ghost.reveal pending_raw_payload)
              (CL.raw_slice (Ghost.reveal pending_network_buffer1) 0 (SZ.v residual_len))));
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
                with inner_bytes. assert (pts_to inner inner_bytes);
                assert (pure (B.length inner_bytes == SZ.v inner_len));
                assert (pure (Seq.equal
                  (Ghost.reveal app_payload)
                  (Seq.slice (Ghost.reveal inner_bytes) 0 (SZ.v payload_len))));
                assert (pure (view0.CL.state.S.phase == S.ApplicationData));
                lemma_step_recv_application_data view0.CL.state (Ghost.reveal app_payload);
                assert (pure (S.step view0.CL.state (S.RecvApplicationData (Ghost.reveal app_payload)) ==
                              Some (S.advance_read_record view0.CL.state)));
                ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                let chunks_single : erased (list B.bytes) =
                  [Ghost.reveal app_payload];
                assert (pure (5 <= B.length (Ghost.reveal network_bytes)));
                assert (pure (U64.fits
                  (view0.CL.state.S.read_state.R.seq +
                   (B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes) + 1))));
                assert (pure (CL.chunk_count [] == 0));
                lemma_u64_fits_next_after_consumed_of_budget
                  view0.CL.state.S.read_state.R.seq
                  (CL.chunk_count [])
                  (B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes));
                assert (pure (1 <= B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes)));
                assert (pure (CL.chunk_count (Ghost.reveal chunks_single) == 1));
                lemma_u64_fits_next_after_consumed_of_budget
                  view0.CL.state.S.read_state.R.seq
                  (CL.chunk_count (Ghost.reveal chunks_single))
                  (B.length view0.CL.pending_received_raw + B.length (Ghost.reveal network_bytes));
                assert (pure (U64.fits (view0.CL.state.S.read_state.R.seq + 1)));
                assert (pure (U64.fits (view0.CL.state.S.read_state.R.seq + 2)));
                with server_record_s1. assert (Rec.is_record_state c.server_application_record_state server_record_s1);
                assert (pure (U64.fits (server_record_s0.R.seq + 1)));
                assert (pure (server_record_s1.R.seq == server_record_s0.R.seq + 1));
                assert (pure (server_record_s1.R.seq == view0.CL.state.S.read_state.R.seq + 1));
                assert (pure (U64.fits (server_record_s1.R.seq + 1)));
                CL.lemma_concat_bytes_singleton (Ghost.reveal app_payload);
                assert (pure (Seq.equal
                  (Ghost.reveal app_payload)
                  (CL.concat_bytes (Ghost.reveal chunks_single))));
                let view_single : erased CL.connection_view =
                  CL.read_application_data_chunks_success_view
                    (Ghost.reveal view1)
                    (Ghost.reveal chunks_single)
                    (Ghost.reveal pending_raw_payload);
                let resp_single : erased CL.client_response =
                  CL.read_application_data_chunks_success_response
                    (Ghost.reveal app_payload)
                    (Ghost.reveal chunks_single);
                CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                CL.lemma_step_read_application_data_chunks_success_exit
                  view0
                  (Ghost.reveal view1)
                  (SZ.v requested_app_len)
                  (Ghost.reveal app_payload)
                  (Ghost.reveal chunks_single)
                  (Ghost.reveal pending_raw_payload);
                assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view_single).CL.raw_log));
                assert (pure (CL.step view0 mreq (Ghost.reveal view_single) (Ghost.reveal resp_single)));
                if SZ.(5sz <=^ residual_len) {
                  let record2_cursor = 0sz;
                  assert (pure (SZ.v record2_cursor == 0));
                  let record2_header_end = SZ.(record2_cursor +^ 5sz);
                  assert (pure (SZ.v record2_header_end == SZ.v record2_cursor + 5));
                  assert (pure (SZ.v record2_header_end == 5));
                  assert (pure (SZ.v record2_header_end <= SZ.v residual_len));
                  let mut header2 = [| 0uy; 5sz |];
                  copy_payload_to_output_loop
                    residual_tmp
                    residual_len
                    header2
                    5sz
                    record2_cursor
                    0sz
                    5sz;
                  with header2_bytes. assert (pts_to header2 header2_bytes);
                  assert (pure (B.length header2_bytes == 5));
                  let mut content_type2_out = [| 0uy; 1sz |];
                  let mut fragment_len2_out = [| 0uy; 2sz |];
                  let header2_parse_ok =
                    RF.parse_record_header header2 5sz content_type2_out 1sz fragment_len2_out 2sz;
                  if header2_parse_ok {
                    let content_type2 = content_type2_out.(0sz);
                    let frag2_hi = fragment_len2_out.(0sz);
                    let frag2_lo = fragment_len2_out.(1sz);
                    let frag2_hi16 = Cast.uint8_to_uint16 frag2_hi;
                    let frag2_lo16 = Cast.uint8_to_uint16 frag2_lo;
                    let frag2_16 = U16.logor (U16.shift_left frag2_hi16 8ul) frag2_lo16;
                    let fragment2_len = SZ.uint16_to_sizet frag2_16;
                    let remaining2_len = SZ.(residual_len -^ record2_header_end);
                    assert (pure (SZ.v remaining2_len == SZ.v residual_len - SZ.v record2_header_end));
                    assert (pure (SZ.v remaining2_len == SZ.v residual_len - 5));
                    if (content_type2 = 23uy &&
                        SZ.(16sz <^ fragment2_len) &&
                        SZ.(fragment2_len <=^ remaining2_len)) {
                      assert (pure (SZ.v fragment2_len <= SZ.v remaining2_len));
                      assert (pure (5 + SZ.v fragment2_len <= SZ.v residual_len));
                      assert (pure (SZ.v record2_cursor + 5 + SZ.v fragment2_len <= SZ.v residual_len));
                      let record2_lengths =
                        residual_frame_lengths_at residual_len record2_cursor fragment2_len;
                      let record2_wire_len = record2_lengths.residual_frame_at_wire_len;
                      assert (pure (SZ.v record2_wire_len == 5 + SZ.v fragment2_len));
                      assert (pure (SZ.v record2_wire_len <= SZ.v residual_len));
                      let record2_end = record2_lengths.residual_frame_at_end;
                      assert (pure (SZ.v record2_end == SZ.v record2_wire_len));
                      let residual_after_two_len = record2_lengths.residual_frame_at_tail_len;
                      assert (pure (SZ.v residual_after_two_len == SZ.v residual_len - SZ.v record2_end));
                      assert (pure (SZ.v record2_end + SZ.v residual_after_two_len == SZ.v residual_len));
                      assert (pure (SZ.v residual_after_two_len <= SZ.v pending_network_buffer_capacity));
                      let record2_cipher_offset = record2_header_end;
                      assert (pure (SZ.v record2_cipher_offset == SZ.v record2_cursor + 5));
                      assert (pure (SZ.v record2_cipher_offset == 5));
                      assert (pure (SZ.v record2_cipher_offset + SZ.v fragment2_len ==
                                    5 + SZ.v fragment2_len));
                      assert (pure (SZ.v record2_cipher_offset + SZ.v fragment2_len ==
                                    SZ.v record2_wire_len));
                      assert (pure (SZ.v record2_cipher_offset + SZ.v fragment2_len == SZ.v record2_end));
                      assert (pure (SZ.v record2_end + SZ.v residual_after_two_len ==
                                    SZ.v residual_len));
                      let mut cipher2 = [| 0uy; fragment2_len |];
                      copy_payload_to_output_loop
                        residual_tmp
                        residual_len
                        cipher2
                        fragment2_len
                        record2_cipher_offset
                        0sz
                        fragment2_len;
                      with cipher2_bytes. assert (pts_to cipher2 cipher2_bytes);
                      assert (pure (B.length cipher2_bytes == SZ.v fragment2_len));
                      assert (pure (SZ.v 16sz == 16));
                      assert (pure (16 < SZ.v fragment2_len));
                      assert (pure (16 <= SZ.v fragment2_len));
                      let inner2_len = SZ.(fragment2_len -^ 16sz);
                      assert (pure (SZ.v inner2_len > 0));
                      let mut inner2 = [| 0uy; inner2_len |];
                      with inner2_old. assert (pts_to inner2 inner2_old);
                      assert (pure (B.length inner2_old == SZ.v inner2_len));
                      assert (pure (B.length inner2_old + 16 == SZ.v fragment2_len));
                      let opened2_peek =
                        Rec.peek_open_application
                          c.server_application_record_state
                          header2
                          5sz
                          cipher2
                          fragment2_len
                          inner2;
                      if opened2_peek {
                        let mut inner_content_type2_out = [| 0uy; 1sz |];
                        let payload2_len =
                          RF.decode_inner_plaintext inner2 inner2_len inner_content_type2_out 1sz;
                        let inner_content_type2 = inner_content_type2_out.(0sz);
                        let remaining_requested = SZ.(requested_app_len -^ payload_len);
                        let remaining_app_cap = SZ.(app_out_cap -^ payload_len);
                        assert (pure (SZ.v remaining_requested == SZ.v requested_app_len - SZ.v payload_len));
                        assert (pure (SZ.v remaining_app_cap == SZ.v app_out_cap - SZ.v payload_len));
                        if (inner_content_type2 = 23uy &&
                            SZ.(payload2_len <=^ remaining_requested) &&
                            SZ.(payload2_len <=^ remaining_app_cap)) {
                          assert (pure (SZ.v payload_len + SZ.v payload2_len <= SZ.v requested_app_len));
                          assert (pure (SZ.v payload_len + SZ.v payload2_len <= SZ.v app_out_cap));
                          let total_payload_len = SZ.(payload_len +^ payload2_len);
                          assert (pure (SZ.v total_payload_len == SZ.v payload_len + SZ.v payload2_len));
                          assert (pure (SZ.v total_payload_len <= SZ.v app_out_cap));
                          assert (pure (SZ.v total_payload_len <= SZ.v requested_app_len));
                          with inner2_bytes_peek. assert (pts_to inner2 inner2_bytes_peek);
                          assert (pure (B.length inner2_bytes_peek == SZ.v inner2_len));
                          let mut payload2_tmp = [| 0uy; payload2_len |];
                          copy_payload_to_output
                            inner2
                            inner2_len
                            payload2_len
                            payload2_tmp
                            payload2_len
                            0sz;
                          with payload2_tmp_bytes. assert (pts_to payload2_tmp payload2_tmp_bytes);
                          assert (pure (B.length payload2_tmp_bytes == SZ.v payload2_len));
                          assert (pure (Seq.equal
                            (Seq.slice payload2_tmp_bytes 0 (SZ.v payload2_len))
                            (Seq.slice inner2_bytes_peek 0 (SZ.v payload2_len))));
                          assert (pure (server_record_s1.R.seq == view0.CL.state.S.read_state.R.seq + 1));
                          assert (pure (U64.fits (server_record_s1.R.seq + 1)));
                          let opened2 =
                            Rec.open_application_runtime
                              c.server_application_record_state
                              header2
                              5sz
                              cipher2
                              fragment2_len
                              inner2;
                          if opened2 {
                            with server_record_s2. assert (Rec.is_record_state c.server_application_record_state server_record_s2);
                            assert (pure (server_record_s2.R.seq == server_record_s1.R.seq + 1));
                            assert (pure (server_record_s2.R.seq == view0.CL.state.S.read_state.R.seq + 2));
                            copy_payload_to_output_loop
                              payload2_tmp
                              payload2_len
                              app_out
                              app_out_cap
                              0sz
                              payload_len
                              payload2_len;
                            with app_out2. assert (pts_to app_out app_out2);
                            assert (pure (B.length app_out2 == SZ.v app_out_cap));
                            assert (pure (Seq.equal
                              (Seq.slice app_out2 (SZ.v payload_len) (SZ.v total_payload_len))
                              (Seq.slice payload2_tmp_bytes 0 (SZ.v payload2_len))));
                            assert (pure (Seq.equal
                              (Seq.slice app_out2 0 (SZ.v payload_len))
                              (Seq.slice app_out1 0 (SZ.v payload_len))));
                            let app_payload2 : erased B.bytes =
                              Seq.slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len);
                            let app_payload_total : erased B.bytes =
                              Seq.slice (Ghost.reveal app_out2) 0 (SZ.v total_payload_len);
                            assert (pure (Seq.equal
                              (Ghost.reveal app_payload2)
                              (Seq.slice (Ghost.reveal payload2_tmp_bytes) 0 (SZ.v payload2_len))));
                            assert (pure (Seq.equal
                              (Ghost.reveal app_payload)
                              (Seq.slice (Ghost.reveal app_out2) 0 (SZ.v payload_len))));
                            assert (pure (CL.raw_slice (Ghost.reveal app_out2) 0 (SZ.v total_payload_len) ==
                                          Seq.slice (Ghost.reveal app_out2) 0 (SZ.v total_payload_len)));
                            assert (pure (CL.raw_slice (Ghost.reveal app_out2) 0 (SZ.v payload_len) ==
                                          Seq.slice (Ghost.reveal app_out2) 0 (SZ.v payload_len)));
                            assert (pure (CL.raw_slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len) ==
                                          Seq.slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len)));
                            assert (pure (Seq.equal
                              (Ghost.reveal app_payload)
                              (CL.raw_slice (Ghost.reveal app_out2) 0 (SZ.v payload_len))));
                            assert (pure (Seq.equal
                              (Ghost.reveal app_payload2)
                              (CL.raw_slice (Ghost.reveal app_out2) (SZ.v payload_len) (SZ.v total_payload_len))));
                            assert (pure (CL.connection_view_consistent (Ghost.reveal view1)));
                            assert (pure ((Ghost.reveal view1).CL.state.S.phase == S.ApplicationData));
                            let chunks_after_second : erased (list B.bytes) =
                              L.append (Ghost.reveal chunks_single) [Ghost.reveal app_payload2];
                            CL.lemma_note_app_received_chunks_loop_accept_output
                              (Ghost.reveal view1)
                              (Ghost.reveal chunks_single)
                              (Ghost.reveal app_payload2)
                              (Ghost.reveal app_out2)
                              (SZ.v payload_len)
                              (SZ.v total_payload_len)
                              (Ghost.reveal app_payload)
                              (Ghost.reveal app_payload_total);
                            assert (pure (Seq.equal
                              (Ghost.reveal app_payload_total)
                              (CL.concat_bytes (Ghost.reveal chunks_after_second))));
                            assert (pure (SZ.v record2_end + SZ.v residual_after_two_len == SZ.v residual_len));
                            set_pending_network_from_slice
                              c
                              residual_tmp
                              residual_len
                              record2_end
                              residual_after_two_len;
                            with pending_network_buffer2. assert (V.pts_to c.pending_network_buffer pending_network_buffer2);
                            let pending_raw_payload2 : erased B.bytes =
                              CL.raw_slice
                                (Ghost.reveal residual_tmp_bytes)
                                (SZ.v record2_end)
                                (SZ.v residual_len);
                            assert (pure (CL.raw_slice
                              (Ghost.reveal residual_tmp_bytes)
                              (SZ.v record2_end)
                              (SZ.v residual_len) ==
                              Seq.slice
                                (Ghost.reveal residual_tmp_bytes)
                                (SZ.v record2_end)
                                (SZ.v residual_len)));
                            assert (pure (Seq.equal
                              (Ghost.reveal pending_raw_payload2)
                              (CL.raw_slice (Ghost.reveal pending_network_buffer2) 0 (SZ.v residual_after_two_len))));
                            assert (pure ((S.advance_read_record view0.CL.state).S.phase == S.ApplicationData));
                            lemma_step_recv_application_data
                              (S.advance_read_record view0.CL.state)
                              (Ghost.reveal app_payload2);
                            assert (pure (S.step
                              (S.advance_read_record view0.CL.state)
                              (S.RecvApplicationData (Ghost.reveal app_payload2)) ==
                              Some (S.advance_read_record (S.advance_read_record view0.CL.state))));
                            ST.advance
                              c.state
                              (S.RecvApplicationData (Ghost.reveal app_payload2))
                              (S.advance_read_record (S.advance_read_record view0.CL.state));
                            let view2 : erased CL.connection_view =
                              CL.read_application_data_chunks_success_view
                                (Ghost.reveal view1)
                                (Ghost.reveal chunks_after_second)
                                (Ghost.reveal pending_raw_payload2);
                            CL.lemma_raw_received_delta_append view0.CL.raw_log (Ghost.reveal network_bytes);
                            let resp : erased CL.client_response =
                              CL.read_application_data_chunks_success_response
                                (Ghost.reveal app_payload_total)
                                (Ghost.reveal chunks_after_second);
                            CL.lemma_step_read_application_data_chunks_success_exit
                              view0
                              (Ghost.reveal view1)
                              (SZ.v requested_app_len)
                              (Ghost.reveal app_payload_total)
                              (Ghost.reveal chunks_after_second)
                              (Ghost.reveal pending_raw_payload2);
                            assert (pure (mreq == CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v requested_app_len)) view0.CL.raw_log (Ghost.reveal view2).CL.raw_log));
                            ST.advance_log c.log (Ghost.reveal view2);
                            let result = { network_out_len = 0sz; app_out_len = total_payload_len; status = CL.ApplicationDataReady };
                            lemma_empty_prefix (Ghost.reveal 'network_out0);
                            lemma_prefix_slice (Ghost.reveal app_out2) (SZ.v total_payload_len);
                            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out2) (Ghost.reveal resp)));
                            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out2) mresp /\
                                                      CL.step view0 mreq (Ghost.reveal view2) mresp));
                            fold (is_client_core c (Ghost.reveal view2));
                            result
                          } else {
                            ST.advance_log c.log (Ghost.reveal view_single);
                            let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                            lemma_empty_prefix (Ghost.reveal 'network_out0);
                            lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                            assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                            assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                      CL.step view0 mreq (Ghost.reveal view_single) mresp));
                            fold (is_client_core c (Ghost.reveal view_single));
                            result
                          }
                        } else {
                          ST.advance_log c.log (Ghost.reveal view_single);
                          let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                          lemma_empty_prefix (Ghost.reveal 'network_out0);
                          lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                          assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                          assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                    CL.step view0 mreq (Ghost.reveal view_single) mresp));
                          fold (is_client_core c (Ghost.reveal view_single));
                          result
                        }
                      } else {
                        ST.advance_log c.log (Ghost.reveal view_single);
                        let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                        lemma_empty_prefix (Ghost.reveal 'network_out0);
                        lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                        assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                        assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                  CL.step view0 mreq (Ghost.reveal view_single) mresp));
                        fold (is_client_core c (Ghost.reveal view_single));
                        result
                      }
                    } else {
                      ST.advance_log c.log (Ghost.reveal view_single);
                      let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                      lemma_empty_prefix (Ghost.reveal 'network_out0);
                      lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                      assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                      assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                                CL.step view0 mreq (Ghost.reveal view_single) mresp));
                      fold (is_client_core c (Ghost.reveal view_single));
                      result
                    }
                  } else {
                    ST.advance_log c.log (Ghost.reveal view_single);
                    let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                    lemma_empty_prefix (Ghost.reveal 'network_out0);
                    lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                    assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                    assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                              CL.step view0 mreq (Ghost.reveal view_single) mresp));
                    fold (is_client_core c (Ghost.reveal view_single));
                    result
                  }
                } else {
                  ST.advance_log c.log (Ghost.reveal view_single);
                  let result = { network_out_len = 0sz; app_out_len = payload_len; status = CL.ApplicationDataReady };
                  lemma_empty_prefix (Ghost.reveal 'network_out0);
                  lemma_prefix_slice (Ghost.reveal app_out1) (SZ.v payload_len);
                  assert (pure (response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) (Ghost.reveal resp_single)));
                  assert (pure (exists mresp. response_buffers_match result (Ghost.reveal 'network_out0) (Ghost.reveal app_out1) mresp /\
                                            CL.step view0 mreq (Ghost.reveal view_single) mresp));
                  fold (is_client_core c (Ghost.reveal view_single));
                  result
                }
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
                  assert (pure (Seq.equal
                    (Ghost.reveal app_payload)
                    (Seq.slice (Ghost.reveal inner_bytes) 0 (SZ.v output_limit))));
                  assert (pure (CL.raw_slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len) ==
                                Seq.slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len)));
                  assert (pure (Seq.equal
                    (Seq.slice (Ghost.reveal pending_buffer1) 0 (SZ.v leftover_len))
                    (Seq.slice (Ghost.reveal inner_bytes) (SZ.v output_limit) (SZ.v payload_len))));
                  assert (pure (Seq.equal
                    (Ghost.reveal pending_payload)
                    (Seq.slice (Ghost.reveal inner_bytes) (SZ.v output_limit) (SZ.v payload_len))));
                  CL.lemma_raw_slice_append_suffix
                    (Ghost.reveal app_payload)
                    (Ghost.reveal pending_payload);
                  assert (pure (view0.CL.state.S.phase == S.ApplicationData));
                  lemma_step_recv_application_data view0.CL.state (Ghost.reveal app_payload);
                  assert (pure (S.step view0.CL.state (S.RecvApplicationData (Ghost.reveal app_payload)) ==
                                Some (S.advance_read_record view0.CL.state)));
                  ST.advance c.state (S.RecvApplicationData (Ghost.reveal app_payload)) (S.advance_read_record view0.CL.state);
                  let base_view2 : erased CL.connection_view =
                    CL.note_app_received_with_pending
                      (Ghost.reveal view1)
                      (Ghost.reveal app_payload)
                      (Ghost.reveal pending_payload)
                      (S.advance_read_record view0.CL.state);
                  assert (pure (CL.pending_app_source_consistent (Ghost.reveal base_view2)));
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
      set_pending_network_from_slice
        c
        network_in
        network_in_len
        0sz
        network_in_len;
      with pending_network_buffer1. assert (V.pts_to c.pending_network_buffer pending_network_buffer1);
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
