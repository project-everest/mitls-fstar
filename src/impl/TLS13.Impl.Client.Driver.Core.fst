module TLS13.Impl.Client.Driver.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module CChannel = TLS13.Impl.Client.ChannelImplementation
module CP = TLS13.Impl.Client.CanonicalProtocol
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module Memmove = TLS13.Lib.Memmove
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CI = Common.ChannelImplementation
module EC = TLS13.Spec.Endpoint.Client
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Sem = TLS13.Wire.Semantics
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module DS = TLS13.Impl.Client.Driver.State
open TLS13.Impl.Client.Driver.State
fn driver_control_snapshot
  (d:driver)
  requires driver_exactly d 'st0 'buffered 'pending_len
  returns snapshot:CR.control_snapshot
  ensures driver_exactly d 'st0 'buffered 'pending_len **
          pure (CR.control_snapshot_matches snapshot 'st0)
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot = C.control_snapshot d.driver_client;
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  snapshot
}

fn driver_copy_certificate_leaf_der
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                 | Some leaf ->
                   SZ.v copied_len == B.length leaf /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                 | None -> False))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let copied_len =
    C.copy_certificate_leaf_der
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  copied_len
}

fn driver_copy_certificate_verify_input
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                 | Some input ->
                   SZ.v copied_len == B.length input /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                 | None -> False))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let copied_len =
    C.copy_certificate_verify_input
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  copied_len
}

fn driver_copy_certificate_verify_signature
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:CR.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.CR.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                 | Some cv ->
                   L.signature_scheme_matches snapshot.CR.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                   SZ.v snapshot.CR.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv) /\
                   Seq.equal
                     (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                     (Sem.certificateVerify_signature_bytes cv)
                 | None -> False))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot =
    C.copy_certificate_verify_signature
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  snapshot
}

fn process_local_event_and_write_once
  (c:C.client)
  (ch:IO.channel)
  (hist:MR.mref CI.io_history_preorder)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           channel_open hist ch 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           channel_open hist ch st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   kind
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  rewrite (C.connection_exactly c 'st0) as (CR.connection_exactly c 'st0);
  let resp =
    C.process_local_event
      c
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (CR.connection_exactly c st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (CR.connection_exactly c st1) as (C.connection_exactly c st1);
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
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (CT.response_wf resp network_out_bytes app_out_bytes));
  assert (pure (SZ.v resp.CT.network_out_len <= B.length network_out_bytes));
  unfold (channel_open hist ch 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  with received sent.
    assert (IO.is_channel ch received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len)));
  let old_consumed =
    choose_wire_logs_match_witness
    'st0
    received
    sent
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len);
  let written = IO.write ch network_out resp.CT.network_out_len;
  tcp_history_note_write
    hist
    received
    sent
    (Ghost.hide (if SZ.v written <= B.length network_out_bytes
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
  lemma_local_event_received_exact_when_nonfailed
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len);
  assert (pure (client_driver_wire_logs_match_witness
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len)));
  FStar.Classical.exists_intro
    (fun consumed ->
      client_driver_wire_logs_match_witness
        st1
        received
        (B.append sent
          (if SZ.v written <= B.length network_out_bytes
           then Seq.slice network_out_bytes 0 (SZ.v written)
           else B.empty))
        consumed
        (Ghost.reveal 'buffered)
        (Ghost.reveal 'pending_len))
    (Ghost.reveal old_consumed);
  assert (pure (client_driver_wire_logs_match
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len)));
  fold (channel_open hist ch st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  assert (pure (SZ.v written <= SZ.v resp.CT.network_out_len));
  assert (pure (resp.CT.status == CT.StepOk ==>
    SZ.v written <= SZ.v resp.CT.network_out_len));
  {
    local_write_resp = resp;
    local_write_written = written;
  }
}

fn driver_process_local_event
  (d:driver)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
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
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  unfold (driver_canonical_progress d 'st0);
  let result =
    process_local_event_and_write_once
      d.driver_client
      d.driver_channel
      d.driver_tcp_history
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  CP.lemma_client_local_progress
    'st0
    st1
    {
      CTypes.client_local_kind = kind;
      CTypes.client_local_payload = Ghost.reveal 'payload_bytes;
    }
    result.local_write_resp
    network_out_bytes
    app_out_bytes;
  MR.update d.driver_progress st1;
  assert (pure (CT.client_end_to_end_invariant st1));
  fold (driver_canonical_progress d st1);
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn driver_process_buffered_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
             (pending_after_consumed
               buffered_len
               result.network_read_buffer_resp.CT.consumed_len) **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 Seq.equal raw_bytes (Ghost.reveal 'old_raw) /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                   SZ.v result.network_read_len /\
                 result.network_read_len == buffered_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 B.length (Ghost.reveal 'buffered) == SZ.v buffered_len /\
                 SZ.v result.network_read_buffer_resp.CT.consumed_len <=
                   SZ.v buffered_len /\
                 Seq.equal buffered_after
                   (Seq.slice (Ghost.reveal 'buffered)
                     (SZ.v result.network_read_buffer_resp.CT.consumed_len)
                     (SZ.v buffered_len)) /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.network_read_buffer_resp
                  (Ghost.reveal result.network_read_prefix)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                  CT.NeedMoreInput ==>
                  CT.response_stuttered
                    'st0
                    st1
                    result.network_read_buffer_resp.CT.response
                    (Ghost.reveal 'old_network_out)
                    network_out_bytes
                    (Ghost.reveal 'old_app_out)
                    app_out_bytes) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                  CT.NeedMoreInput ==>
                  result.network_read_buffer_resp.CT.consumed_len == 0sz) /\
                 (SZ.v result.network_read_buffer_resp.CT.response.CT.app_out_len > 0 ==>
                  result.network_read_buffer_resp.CT.response.CT.status == CT.StepOk /\
                  result.network_read_buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 'buffered buffered_len);
  unfold (driver_canonical_progress d 'st0);
  assert (pure (
    'st0.CS.cs_model.CS.model_config ==
      (Ghost.reveal d.driver_initial).CS.cs_model.CS.model_config /\
    CP.client_initial_wire_logs_empty (Ghost.reveal d.driver_initial)));
  A.pts_to_len raw;
  assert (pure (A.length raw == SZ.v raw_capacity));
  A.to_mask raw;
  with raw_mask.
    assert (A.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v raw_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index (Ghost.reveal 'old_raw) i)));
  let raw_prefix_array =
    A.sub raw #1.0R #(fun _ -> True) 0sz (SZ.v buffered_len);
  with raw_prefix_mask.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask ==>
    Some? (Seq.index raw_prefix_mask i)));
  A.from_mask raw_prefix_array;
  with raw_prefix.
    assert (pts_to raw_prefix_array raw_prefix);
  assert (pure (B.length raw_prefix == SZ.v buffered_len));
  assert (pure (Seq.equal raw_prefix
    (Seq.slice (Ghost.reveal 'old_raw) 0 (SZ.v buffered_len))));
  assert (pure (Seq.equal raw_prefix (Ghost.reveal 'buffered)));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let buffer_resp =
    C.process_network_bytes
      d.driver_client
      raw_prefix_array
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (CR.connection_exactly d.driver_client st1 **
            pts_to raw_prefix_array raw_prefix **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (CR.connection_exactly d.driver_client st1)
    as (C.connection_exactly d.driver_client st1);
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
    CT.response_stuttered
      'st0
      st1
      buffer_resp.CT.response
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes));
  CT.lemma_network_bytes_end_to_end_correct_preserves_config
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes;
  assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
    buffer_resp.CT.consumed_len == 0sz));
  assert (pure (SZ.v buffer_resp.CT.response.CT.app_out_len > 0 ==>
    buffer_resp.CT.response.CT.status == CT.StepOk /\
    buffer_resp.CT.response.CT.network_out_len == 0sz));
  lemma_network_bytes_wire_lengths
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes;
  assert (pure (SZ.v buffer_resp.CT.consumed_len <= B.length raw_prefix));
  assert (pure (SZ.v buffer_resp.CT.consumed_len <= SZ.v buffered_len));
  let new_pending = pending_after_consumed buffered_len buffer_resp.CT.consumed_len;
  assert (pure (SZ.v new_pending ==
    SZ.v buffered_len - SZ.v buffer_resp.CT.consumed_len));
  A.to_mask raw_prefix_array;
  with raw_prefix_mask_after.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True));
  assert (pure (Seq.length raw_prefix_mask_after == SZ.v buffered_len));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Some? (Seq.index raw_prefix_mask_after i)));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Seq.index raw_prefix_mask_after i == Some (Seq.index raw_prefix i)));
  rewrite
    (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True))
    as
    (A.pts_to_mask (A.gsub raw 0 (SZ.v buffered_len)) #1.0R raw_prefix_mask_after (fun _ -> True));
  A.return_sub
    raw
    #1.0R
    #raw_mask
    #raw_prefix_mask_after
    #(fun k -> True /\ ~(0 <= k /\ k < SZ.v buffered_len))
    #(fun _ -> True)
    #0
    #(SZ.v buffered_len);
  with raw_joined_mask.
    assert (A.pts_to_mask raw #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(0 <= k /\ k < SZ.v buffered_len)) \/
        (0 <= k /\ k < SZ.v buffered_len /\ True)));
  assert (pure (Seq.length raw_joined_mask == Seq.length raw_mask));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i ==
      (if 0 <= i && i < SZ.v buffered_len
       then Seq.index raw_prefix_mask_after (i - 0)
       else Seq.index raw_mask i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i ==
      (if i < SZ.v buffered_len
       then Seq.index raw_prefix_mask_after i
       else Seq.index raw_mask i)));
  lemma_rejoined_raw_mask_matches_old
    (Ghost.reveal 'old_raw)
    raw_prefix
    raw_mask
    raw_prefix_mask_after
    raw_joined_mask
    (SZ.v buffered_len);
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v buffered_len)) \/
     (0 <= i /\ i < SZ.v buffered_len /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i == Some (Seq.index (Ghost.reveal 'old_raw) i)));
  A.from_mask raw;
  with raw_bytes.
    assert (pts_to raw raw_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  assert (pure (Seq.equal raw_bytes (Ghost.reveal 'old_raw)));
  assert (pure (CT.response_wf buffer_resp.CT.response network_out_bytes app_out_bytes));
  assert (pure (SZ.v buffer_resp.CT.response.CT.network_out_len <= B.length network_out_bytes));
  unfold (channel_open d.driver_tcp_history d.driver_channel 'st0 'buffered buffered_len);
  with received sent.
    assert (IO.is_channel d.driver_channel received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) buffered_len));
  let old_consumed =
    choose_wire_logs_match_witness
    'st0
    received
    sent
    (Ghost.reveal 'buffered)
    buffered_len;
  let consumed_prefix =
    Ghost.hide (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len);
  let new_buffered =
    Ghost.hide (Seq.slice (Ghost.reveal 'buffered)
      (SZ.v buffer_resp.CT.consumed_len)
      (SZ.v buffered_len));
  assert (pure (Ghost.reveal new_buffered ==
    Seq.slice (Ghost.reveal 'buffered)
      (SZ.v buffer_resp.CT.consumed_len)
      (SZ.v buffered_len)));
  Seq.lemma_len_slice
    (Ghost.reveal 'buffered)
    (SZ.v buffer_resp.CT.consumed_len)
    (SZ.v buffered_len);
  assert (pure (B.length (Ghost.reveal new_buffered) == SZ.v new_pending));
  assert (pure (Seq.equal (Ghost.reveal consumed_prefix)
    (Seq.slice (Ghost.reveal 'buffered) 0 (SZ.v buffer_resp.CT.consumed_len))));
  assert (pure (Seq.equal
    (Ghost.reveal consumed_prefix)
    (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len)));
  Seq.lemma_eq_elim
    (Ghost.reveal consumed_prefix)
    (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len);
  lemma_slice_append_full
    (Ghost.reveal 'buffered)
    (SZ.v buffer_resp.CT.consumed_len);
  assert (pure (Seq.equal
    (B.append (Ghost.reveal consumed_prefix) (Ghost.reveal new_buffered))
    (Ghost.reveal 'buffered)));
  lemma_network_bytes_logged_received_accounted
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes
    (Ghost.reveal old_consumed);
  Seq.append_assoc (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix) (Ghost.reveal new_buffered);
  assert (pure (Seq.equal
    (B.append (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix)) (Ghost.reveal new_buffered))
    received));
  let written = IO.write d.driver_channel network_out buffer_resp.CT.response.CT.network_out_len;
  tcp_history_note_write
    d.driver_tcp_history
    received
    sent
    (Ghost.hide (if SZ.v written <= B.length network_out_bytes
                 then Seq.slice network_out_bytes 0 (SZ.v written)
                 else B.empty));
  assert (pure (written == buffer_resp.CT.response.CT.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  Seq.lemma_len_append sent (Seq.slice network_out_bytes 0 (SZ.v written));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (CT.response_network_out buffer_resp.CT.response network_out_bytes)));
  assert (pure (Seq.equal sent 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim sent 'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (CT.response_network_out buffer_resp.CT.response network_out_bytes))));
  lemma_network_bytes_logged_received_exact_when_nonfailed
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    buffered_len;
  assert (pure (CT.connection_control_not_failed st1 ==>
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append (Ghost.reveal old_consumed)
        (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len))));
  assert (pure (client_driver_wire_logs_match_witness
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
    (Ghost.reveal new_buffered)
    new_pending));
  assert (pure (client_driver_wire_logs_match
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal new_buffered)
    new_pending));
  fold (channel_open d.driver_tcp_history d.driver_channel st1 (Ghost.reveal new_buffered) new_pending);
  assert (pure (SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
  assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
    SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
  CP.lemma_client_network_progress
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes;
  MR.update d.driver_progress st1;
  assert (pure (CT.client_end_to_end_invariant st1));
  fold (driver_canonical_progress d st1);
  fold (driver_exactly d st1 (Ghost.reveal new_buffered) new_pending);
  assert (pure (B.length raw_prefix == SZ.v buffered_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (B.length raw_bytes == SZ.v raw_capacity /\
    B.length raw_prefix == SZ.v buffered_len /\
    buffered_len == buffered_len /\
    SZ.v buffered_len <= SZ.v raw_capacity /\
    B.length network_out_bytes == SZ.v network_out_len /\
    B.length app_out_bytes == SZ.v app_out_len /\
    CT.network_bytes_end_to_end_correct
      'st0
      st1
      buffer_resp
      raw_prefix
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes /\
    (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
     buffer_resp.CT.consumed_len == 0sz) /\
    (buffer_resp.CT.response.CT.status == CT.StepOk ==>
     SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len)));
  assert (pure (new_pending ==
    pending_after_consumed buffered_len buffer_resp.CT.consumed_len));
  assert (pure (pending_after_consumed buffered_len
    buffer_resp.CT.consumed_len == new_pending));
  rewrite (driver_exactly d st1 (Ghost.reveal new_buffered) new_pending) as
    (driver_exactly d st1 (Ghost.reveal new_buffered)
      (pending_after_consumed buffered_len
        buffer_resp.CT.consumed_len));
  {
    network_read_len = buffered_len;
    network_read_buffer_resp = buffer_resp;
    network_read_written = written;
    network_read_prefix = Ghost.hide raw_prefix;
  }
}

noextract
let lemma_compact_buffer_prefix_step
  (original raw_before raw_after:B.bytes)
  (i consumed:nat)
  : Lemma
    (requires
      B.length raw_before == B.length original /\
      B.length raw_after == B.length original /\
      i + consumed < B.length original /\
      (forall (k:nat). k < i ==>
        Seq.index raw_before k == Seq.index original (k + consumed)) /\
      Seq.index raw_after i == Seq.index original (i + consumed) /\
      (forall (k:nat). k < i ==>
        Seq.index raw_after k == Seq.index raw_before k))
    (ensures
      forall (k:nat). k < i + 1 ==>
        Seq.index raw_after k == Seq.index original (k + consumed))
=
  let index_proof
    (k:nat { k < i + 1 })
    : Lemma
      (Seq.index raw_after k == Seq.index original (k + consumed))
  =
    if k < i then (
      assert (Seq.index raw_after k == Seq.index raw_before k);
      assert (Seq.index raw_before k == Seq.index original (k + consumed))
    ) else (
      assert (k == i)
    )
  in
  FStar.Classical.forall_intro
    #(k:nat { k < i + 1 })
    #(fun k ->
      Seq.index raw_after k == Seq.index original (k + consumed))
    index_proof

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  Memmove.memmove raw 0sz consumed_len new_len;
  assert (pure (new_len == pending_after_consumed buffered_len consumed_len));
  new_len
}

fn driver_process_buffered_network_bytes_compact_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after result.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.buffered_network_read.network_read_prefix) ==
                   SZ.v result.buffered_network_read.network_read_len /\
                 result.buffered_network_read.network_read_len == buffered_len /\
                 SZ.v result.buffered_network_new_len <= SZ.v buffered_len /\
                 SZ.v result.buffered_network_new_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.buffered_network_new_len)) /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.buffered_network_read.network_read_buffer_resp
                  (Ghost.reveal result.buffered_network_read.network_read_prefix)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                 (result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status ==
                  CT.NeedMoreInput ==>
                  CT.response_stuttered
                    'st0
                    st1
                    result.buffered_network_read.network_read_buffer_resp.CT.response
                    (Ghost.reveal 'old_network_out)
                    network_out_bytes
                    (Ghost.reveal 'old_app_out)
                    app_out_bytes) /\
                 (SZ.v result.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len > 0 ==>
                  result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk /\
                  result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                 (result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.buffered_network_read.network_read_written <=
                 SZ.v result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len))
{
  let read_result =
    driver_process_buffered_network_bytes_once
      d
      raw
      raw_capacity
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
    assert (driver_exactly d st1 buffered_after
              (pending_after_consumed
                buffered_len
                read_result.network_read_buffer_resp.CT.consumed_len) **
            pts_to raw raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  assert (pure (B.length (Ghost.reveal read_result.network_read_prefix) ==
    SZ.v read_result.network_read_len));
  assert (pure (read_result.network_read_len == buffered_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    read_result.network_read_buffer_resp
    (Ghost.reveal read_result.network_read_prefix)
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (
    read_result.network_read_buffer_resp.CT.response.CT.status ==
      CT.NeedMoreInput ==>
    CT.response_stuttered
      'st0
      st1
      read_result.network_read_buffer_resp.CT.response
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes));
  assert (pure (
    SZ.v read_result.network_read_buffer_resp.CT.response.CT.app_out_len > 0 ==>
    read_result.network_read_buffer_resp.CT.response.CT.status == CT.StepOk /\
    read_result.network_read_buffer_resp.CT.response.CT.network_out_len == 0sz));
  assert (pure (SZ.v read_result.network_read_buffer_resp.CT.consumed_len <=
    B.length (Ghost.reveal read_result.network_read_prefix)));
  assert (pure (SZ.v read_result.network_read_buffer_resp.CT.consumed_len <=
    SZ.v buffered_len));
  let consumed_zero =
    read_result.network_read_buffer_resp.CT.consumed_len = 0sz;
  if consumed_zero {
    assert (pure (SZ.v buffered_len <= SZ.v buffered_len));
    assert (pure (
      pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len == buffered_len));
    assert (pure (Seq.equal buffered_after
      (Seq.slice (Ghost.reveal 'buffered) 0 (SZ.v buffered_len))));
    SeqP.slice_length (Ghost.reveal 'buffered);
    Seq.lemma_eq_elim
      buffered_after
      (Seq.slice (Ghost.reveal 'buffered) 0 (SZ.v buffered_len));
    Seq.lemma_eq_elim
      (Ghost.reveal 'buffered)
      (Seq.slice (Ghost.reveal 'old_raw) 0 (SZ.v buffered_len));
    Seq.lemma_eq_elim raw_bytes (Ghost.reveal 'old_raw);
    assert (pure (Seq.equal buffered_after
      (Seq.slice raw_bytes 0 (SZ.v buffered_len))));
    rewrite (driver_exactly d st1 buffered_after
      (pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len)) as
      (driver_exactly d st1 buffered_after buffered_len);
    {
      buffered_network_read = read_result;
      buffered_network_new_len = buffered_len;
    }
  } else {
    let new_len =
      compact_buffer_suffix
        raw
        raw_capacity
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len;
    with compacted_raw.
      assert (pts_to raw compacted_raw);
    assert (pure (B.length compacted_raw == SZ.v raw_capacity));
    assert (pure (SZ.v new_len <= SZ.v buffered_len));
    assert (pure (Seq.equal buffered_after
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))));
    assert (pure (Seq.equal
      (Seq.slice compacted_raw 0 (SZ.v new_len))
      (Seq.slice raw_bytes
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))));
    SeqP.slice_slice
      (Ghost.reveal 'old_raw)
      0
      (SZ.v buffered_len)
      (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
      (SZ.v buffered_len);
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))
      (Seq.slice (Ghost.reveal 'old_raw)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))));
    Seq.lemma_eq_elim
      buffered_after
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len));
    Seq.lemma_eq_elim
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))
      (Seq.slice (Ghost.reveal 'old_raw)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len));
    Seq.lemma_eq_elim
      (Seq.slice compacted_raw 0 (SZ.v new_len))
      (Seq.slice raw_bytes
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len));
    Seq.lemma_eq_elim raw_bytes (Ghost.reveal 'old_raw);
    assert (pure (buffered_after == Seq.slice compacted_raw 0 (SZ.v new_len)));
    assert (pure (Seq.equal buffered_after (Seq.slice compacted_raw 0 (SZ.v new_len))));
    assert (pure (
      pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len == new_len));
    rewrite (driver_exactly d st1 buffered_after
      (pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len)) as
      (driver_exactly d st1 buffered_after new_len);
    {
      buffered_network_read = read_result;
      buffered_network_new_len = new_len;
    }
  }
}

fn driver_read_buffered_network_bytes_compact_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
            result.buffered_network_io_buffered.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_read_len <=
                  SZ.v raw_capacity - SZ.v buffered_len /\
                 B.length
                  (Ghost.reveal
                    result.buffered_network_io_buffered.buffered_network_read.network_read_prefix) ==
                  SZ.v
                    result.buffered_network_io_buffered.buffered_network_read.network_read_len /\
                 SZ.v
                  result.buffered_network_io_buffered.buffered_network_read.network_read_len <=
                  SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_buffered.buffered_network_new_len <=
                  SZ.v result.buffered_network_io_buffered.buffered_network_read.network_read_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0
                     (SZ.v result.buffered_network_io_buffered.buffered_network_new_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
                  (Ghost.reveal
                    result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                  (SZ.v
                   result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len > 0 ==>
                  result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk /\
                  result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                  (result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk ==>
                  SZ.v
                    result.buffered_network_io_buffered.buffered_network_read.network_read_written <=
                  SZ.v
                    result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 'buffered buffered_len);
  A.pts_to_len raw;
  assert (pure (A.length raw == SZ.v raw_capacity));
  A.to_mask raw;
  with raw_mask.
    assert (A.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v raw_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index (Ghost.reveal 'old_raw) i)));
  let available = SZ.sub raw_capacity buffered_len;
  assert (pure (SZ.v available == SZ.v raw_capacity - SZ.v buffered_len));
  let raw_tail_array =
    A.sub raw #1.0R #(fun _ -> True) buffered_len (SZ.v raw_capacity);
  with raw_tail_mask.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask (fun _ -> True));
  assert (pure (Seq.length raw_tail_mask == SZ.v available));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask ==>
    Some? (Seq.index raw_tail_mask i)));
  A.from_mask raw_tail_array;
  with raw_tail.
    assert (pts_to raw_tail_array raw_tail);
  assert (pure (B.length raw_tail == SZ.v available));
  unfold (channel_open d.driver_tcp_history d.driver_channel 'st0 'buffered buffered_len);
  with received sent.
    assert (IO.is_channel d.driver_channel received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) buffered_len));
  let old_consumed =
    choose_wire_logs_match_witness
    'st0
    received
    sent
    (Ghost.reveal 'buffered)
    buffered_len;
  let read_len = IO.read d.driver_channel raw_tail_array available;
  with raw_tail_after read_chunk.
    assert (IO.is_channel d.driver_channel (B.append received read_chunk) sent **
            pts_to raw_tail_array raw_tail_after);
  tcp_history_note_read
    d.driver_tcp_history
    received
    sent
    read_chunk;
  Seq.lemma_len_append received read_chunk;
  assert (pure (B.length read_chunk == SZ.v read_len));
  assert (pure (SZ.v buffered_len + SZ.v read_len <= SZ.v raw_capacity));
  SZ.fits_lte (SZ.v buffered_len + SZ.v read_len) (SZ.v raw_capacity);
  let total_len = buffered_len `SZ.add` read_len;
  assert (pure (SZ.v total_len == SZ.v buffered_len + SZ.v read_len));
  assert (pure (SZ.v total_len <= SZ.v raw_capacity));
  let new_buffered =
    Ghost.hide (B.append (Ghost.reveal 'buffered) read_chunk);
  Seq.lemma_len_append (Ghost.reveal 'buffered) read_chunk;
  Seq.append_assoc (Ghost.reveal old_consumed) (Ghost.reveal 'buffered) read_chunk;
  assert (pure (client_driver_wire_logs_match_witness
    'st0
    (B.append received read_chunk)
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal new_buffered)
    total_len));
  assert (pure (client_driver_wire_logs_match
    'st0
    (B.append received read_chunk)
    sent
    (Ghost.reveal new_buffered)
    total_len));
  fold (channel_open d.driver_tcp_history d.driver_channel 'st0 (Ghost.reveal new_buffered) total_len);
  assert (pure (B.length raw_tail_after == SZ.v available));
  assert (pure (SZ.v read_len <= SZ.v available));
  A.to_mask raw_tail_array;
  with raw_tail_mask_after.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True));
  assert (pure (Seq.length raw_tail_mask_after == B.length raw_tail_after));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask_after ==>
    Seq.index raw_tail_mask_after i == Some (Seq.index raw_tail_after i)));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask_after ==>
    Some? (Seq.index raw_tail_mask_after i)));
  rewrite
    (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub raw (SZ.v buffered_len) (SZ.v raw_capacity))
      #1.0R
      raw_tail_mask_after
      (fun _ -> True));
  A.return_sub
    raw
    #1.0R
    #raw_mask
    #raw_tail_mask_after
    #(fun k -> True /\ ~(SZ.v buffered_len <= k /\ k < SZ.v raw_capacity))
    #(fun _ -> True)
    #(SZ.v buffered_len)
    #(SZ.v raw_capacity);
  with raw_joined_mask.
    assert (A.pts_to_mask raw #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(SZ.v buffered_len <= k /\ k < SZ.v raw_capacity)) \/
        (SZ.v buffered_len <= k /\ k < SZ.v raw_capacity /\ True)));
  assert (pure (Seq.length raw_joined_mask == Seq.length raw_mask));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i ==
      (if SZ.v buffered_len <= i && i < SZ.v raw_capacity
       then Seq.index raw_tail_mask_after (i - SZ.v buffered_len)
       else Seq.index raw_mask i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(SZ.v buffered_len <= i /\ i < SZ.v raw_capacity)) \/
     (SZ.v buffered_len <= i /\ i < SZ.v raw_capacity /\ True))));
  DS.lemma_joined_mask_is_some
    raw_mask raw_tail_mask_after raw_joined_mask
    (SZ.v buffered_len) (SZ.v raw_capacity);
  A.from_mask raw;
  with raw_after_read.
    assert (pts_to raw raw_after_read);
  assert (pure (B.length raw_after_read == SZ.v raw_capacity));
  assert (pure (Seq.equal (Ghost.reveal 'buffered)
    (Seq.slice (Ghost.reveal 'old_raw) 0 (SZ.v buffered_len))));
  assert (pure (Seq.equal read_chunk
    (Seq.slice raw_tail_after 0 (SZ.v read_len))));
  assert (pure (forall (i:nat). i < B.length raw_after_read ==>
    Some (Seq.index raw_after_read i) == Seq.index raw_joined_mask i));
  assert (pure (forall (i:nat). i < SZ.v read_len ==>
    SZ.v buffered_len <= SZ.v buffered_len + i /\
    SZ.v buffered_len + i < SZ.v raw_capacity /\
    (SZ.v buffered_len + i) - SZ.v buffered_len == i));
  assert (pure (forall (i:nat). i < SZ.v read_len ==>
    SZ.v buffered_len + i < B.length raw_after_read));
  DS.lemma_mask_values_at_offset
    raw_after_read raw_joined_mask
    (SZ.v buffered_len) (SZ.v read_len);
  DS.lemma_joined_mask_values_at_offset
    raw_mask raw_tail_mask_after raw_joined_mask
    (SZ.v buffered_len) (SZ.v raw_capacity) (SZ.v read_len);
  assert (pure (forall (i:nat). i < SZ.v read_len ==>
    Seq.index raw_tail_mask_after i ==
      Some (Seq.index raw_tail_after i)));
  assert (pure (forall (i:nat). i < SZ.v buffered_len ==>
    i < SZ.v raw_capacity /\
    ~(SZ.v buffered_len <= i /\ i < SZ.v raw_capacity)));
  DS.lemma_joined_mask_values_before_offset
    raw_mask raw_tail_mask_after raw_joined_mask
    (SZ.v buffered_len) (SZ.v raw_capacity) (SZ.v buffered_len);
  assert (pure (forall (i:nat). i < SZ.v buffered_len ==>
    Seq.index raw_mask i ==
      Some (Seq.index (Ghost.reveal 'old_raw) i)));
  assert (pure (forall (i:nat). i < SZ.v buffered_len ==>
    Some (Seq.index raw_after_read i) == Seq.index raw_joined_mask i));
  assert (pure (forall (i:nat). i < SZ.v buffered_len ==>
    Seq.index raw_after_read i == Seq.index (Ghost.reveal 'old_raw) i));
  assert (pure (forall (i:nat). i < SZ.v read_len ==>
    Seq.index raw_after_read (SZ.v buffered_len + i) ==
    Seq.index raw_tail_after i));
  lemma_read_append_buffer_matches_raw_prefix
    raw_after_read
    (Ghost.reveal 'old_raw)
    raw_tail_after
    (Ghost.reveal 'buffered)
    read_chunk
    (SZ.v buffered_len)
    (SZ.v read_len)
    (SZ.v total_len);
  Seq.lemma_eq_elim
    (B.append (Ghost.reveal 'buffered) read_chunk)
    (Seq.slice raw_after_read 0 (SZ.v total_len));
  assert (pure (Seq.equal (Ghost.reveal new_buffered)
    (Seq.slice raw_after_read 0 (SZ.v total_len))));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal new_buffered) total_len);
  let buffered_result =
    driver_process_buffered_network_bytes_compact_once
      d
      raw
      raw_capacity
      total_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
    assert (driver_exactly d st1 buffered_after buffered_result.buffered_network_new_len **
            pts_to raw raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  assert (pure (SZ.v read_len <= SZ.v raw_capacity - SZ.v buffered_len));
  assert (pure (B.length (Ghost.reveal
    buffered_result.buffered_network_read.network_read_prefix) ==
    SZ.v buffered_result.buffered_network_read.network_read_len));
  assert (pure (buffered_result.buffered_network_read.network_read_len == total_len));
  assert (pure (SZ.v buffered_result.buffered_network_read.network_read_len <=
    SZ.v raw_capacity));
  assert (pure (SZ.v buffered_result.buffered_network_new_len <=
    SZ.v buffered_result.buffered_network_read.network_read_len));
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffered_result.buffered_network_read.network_read_buffer_resp
    (Ghost.reveal buffered_result.buffered_network_read.network_read_prefix)
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (
    SZ.v buffered_result.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len > 0 ==>
    buffered_result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk /\
    buffered_result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len == 0sz));
  assert (pure (
    buffered_result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk ==>
    SZ.v buffered_result.buffered_network_read.network_read_written <=
      SZ.v buffered_result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len));
  {
    buffered_network_io_read_len = read_len;
    buffered_network_io_buffered = buffered_result;
  }
}

fn rec driver_process_buffered_network_records
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_loop_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
            result.buffered_network_loop_last.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_loop_last.buffered_network_new_len <=
                  SZ.v buffered_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len)
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  if (fuel = 0sz) {
    assert (pure (no_op.buffered_network_new_len == buffered_len));
    rewrite (driver_exactly d 'st0 'buffered buffered_len) as
      (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len);
    let result = {
      buffered_network_loop_last = no_op;
      buffered_network_loop_exhausted = true;
    };
    assert (pure (result.buffered_network_loop_last.buffered_network_new_len ==
      no_op.buffered_network_new_len));
    rewrite (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len) as
      (driver_exactly d 'st0 'buffered
        result.buffered_network_loop_last.buffered_network_new_len);
    result
  } else {
    assert (pure (0 < SZ.v fuel));
    let empty_buffer = buffered_len = 0sz;
    if empty_buffer {
      assert (pure (no_op.buffered_network_new_len == buffered_len));
      rewrite (driver_exactly d 'st0 'buffered buffered_len) as
        (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len);
      let result = {
        buffered_network_loop_last = no_op;
        buffered_network_loop_exhausted = false;
      };
      assert (pure (result.buffered_network_loop_last.buffered_network_new_len ==
        no_op.buffered_network_new_len));
      rewrite (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len) as
        (driver_exactly d 'st0 'buffered
          result.buffered_network_loop_last.buffered_network_new_len);
      result
    } else {
      let step =
        driver_process_buffered_network_bytes_compact_once
          d
          raw
          raw_capacity
          buffered_len
          network_out
          network_out_len
          app_out
          app_out_len;
      with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
        assert (driver_exactly d st1 buffered_after step.buffered_network_new_len **
                pts_to raw raw_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      assert (pure (B.length raw_bytes == SZ.v raw_capacity));
      assert (pure (SZ.v step.buffered_network_new_len <= SZ.v buffered_len));
      assert (pure (SZ.v step.buffered_network_new_len <= SZ.v raw_capacity));
      let ok =
        step.buffered_network_read.network_read_buffer_resp.CT.response.CT.status =
        CT.StepOk;
      let no_app =
        step.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len =
        0sz;
      let consumed_zero =
        step.buffered_network_read.network_read_buffer_resp.CT.consumed_len = 0sz;
      let empty_after = step.buffered_network_new_len = 0sz;
      let continue_loop =
        ok && no_app && (consumed_zero = false) && (empty_after = false);
      if continue_loop {
        assert (pure (0 < SZ.v fuel));
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        assert (pure (Seq.equal buffered_after
          (Seq.slice raw_bytes 0 (SZ.v step.buffered_network_new_len))));
        driver_process_buffered_network_records
          d
          raw
          raw_capacity
          step.buffered_network_new_len
          network_out
          network_out_len
          app_out
          app_out_len
          next_fuel
      } else {
        {
          buffered_network_loop_last = step;
          buffered_network_loop_exhausted = false;
        }
      }
    }
  }
}

fn process_ready_internal_local_action_once
  (c:C.client)
  (ch:IO.channel)
  (hist:MR.mref CI.io_history_preorder)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
          channel_open hist ch 'st0 'buffered 'pending_len **
          pts_to empty_payload 'empty_payload_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'empty_payload_bytes == 0 /\
                B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           channel_open hist ch st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v                   result.ready_local_resp.CT.network_out_len) /\
                  True) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  rewrite (C.connection_exactly c 'st0) as (CR.connection_exactly c 'st0);
  let action =
    C.next_local_action
      c
      network_out_len
      certificate_public_key_len
      server_finished_payload_len;
  rewrite (CR.connection_exactly c 'st0) as (C.connection_exactly c 'st0);
  assert (pure (C.next_local_action_sound
    'st0
    network_out_len
    certificate_public_key_len
    server_finished_payload_len
    action));
  assert (pure (forall (i:nat{i < B.length (Ghost.reveal 'empty_payload_bytes)}).
    Seq.index (Ghost.reveal 'empty_payload_bytes) i == Seq.index B.empty i));
  Seq.lemma_eq_intro (Ghost.reveal 'empty_payload_bytes) B.empty;
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let ready = action.CT.next_local_ready;
  if ready {
    assert (pure (action.CT.next_local_ready == true));
    let needs_external_payload =
      action.CT.next_local_kind = CT.LocalValidateCertificate ||
      action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
    if needs_external_payload {
      assert (pure ('st0.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure ('st0 == 'st0));
      {
        ready_local_action = action;
        ready_local_processed = false;
        ready_local_resp = no_op_resp;
        ready_local_written = 0sz;
      }
    } else {
      assert (pure (C.next_local_action_internal_input_ready 'st0 action));
      assert (pure (internal_local_action_kind action.CT.next_local_kind));
      lemma_ready_internal_action_empty_payload_wf
        'st0
        network_out_len
        certificate_public_key_len
        server_finished_payload_len
        action
        (Ghost.reveal 'empty_payload_bytes);
      assert (pure (CT.local_input_wf
        'st0
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)));
      let write_result =
        process_local_event_and_write_once
          c
          ch
          hist
          action.CT.next_local_kind
          empty_payload
          0sz
          network_out
          network_out_len
          app_out
          app_out_len;
      with st1 network_out_bytes app_out_bytes.
        assert (C.connection_exactly c st1 **
                pts_to empty_payload 'empty_payload_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      assert (pure (CT.local_event_end_to_end_correct
        'st0
        st1
        write_result.local_write_resp
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)
        network_out_bytes
        app_out_bytes));
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (write_result.local_write_resp.CT.status == CT.StepOk ==>
        SZ.v write_result.local_write_written <=
        SZ.v write_result.local_write_resp.CT.network_out_len));
      {
        ready_local_action = action;
        ready_local_processed = true;
        ready_local_resp = write_result.local_write_resp;
        ready_local_written = write_result.local_write_written;
      }
    }
  } else {
    assert (pure ('st0.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ('st0 == 'st0));
    {
      ready_local_action = action;
      ready_local_processed = false;
      ready_local_resp = no_op_resp;
      ready_local_written = 0sz;
    }
  }
}

let lemma_ready_local_action_progress
  (st0 st1:CS.connection_state)
  (result:ready_local_action_result)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        (result.ready_local_processed ==>
          CT.local_event_end_to_end_correct
            st0
            st1
            result.ready_local_resp
            result.ready_local_action.CT.next_local_kind
            payload
            network_out
            app_out) /\
        (result.ready_local_processed == false ==> st1 == st0))
      (ensures
        EC.client_progress_preorder #CTypes.client_local_event st0 st1)
=
  if result.ready_local_processed then
    CP.lemma_client_local_progress
      st0
      st1
      {
        CTypes.client_local_kind = result.ready_local_action.CT.next_local_kind;
        CTypes.client_local_payload = payload;
      }
      result.ready_local_resp
      network_out
      app_out
  else
    assert (EC.client_progress_preorder #CTypes.client_local_event st0 st1)

fn driver_handshake_step
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v                   result.ready_local_resp.CT.network_out_len) /\
                  True) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  unfold (driver_canonical_progress d 'st0);
  let result =
    process_ready_internal_local_action_once
      d.driver_client
      d.driver_channel
      d.driver_tcp_history
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            channel_open d.driver_tcp_history d.driver_channel st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  lemma_ready_local_action_result_preserves_config
    'st0
    st1
    result
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  lemma_ready_local_action_progress
    'st0
    st1
    result
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  MR.update d.driver_progress st1;
  assert (pure (CT.client_end_to_end_invariant st1));
  fold (driver_canonical_progress d st1);
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn rec driver_drain_local_actions
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: driver_drain_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 (result.driver_drain_last.ready_local_processed \/
                  result.driver_drain_last.ready_local_written == 0sz) /\
                 (result.driver_drain_exhausted ==>
                  result.driver_drain_last.ready_local_processed == false /\
                  result.driver_drain_last.ready_local_written == 0sz))
  decreases (SZ.v fuel)
{
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_last = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    assert (pure (false == false /\ 0sz == 0sz));
    {
      driver_drain_last = no_op_last;
      driver_drain_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step =
      driver_handshake_step
        d
        empty_payload
        network_out
        network_out_len
        certificate_public_key_len
        server_finished_payload_len
        app_out
        app_out_len;
    with st1 network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
              pts_to empty_payload 'empty_payload_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (B.length app_out_bytes == SZ.v app_out_len));
    assert (pure (step.ready_local_processed \/
      step.ready_local_written == 0sz));
    let proceed =
      step.ready_local_processed &&
      step.ready_local_resp.CT.status = CT.StepOk;
    if proceed {
      let next_fuel = SZ.sub fuel 1sz;
      assert (pure (SZ.v next_fuel < SZ.v fuel));
      let result =
        driver_drain_local_actions
          d
          empty_payload
          network_out
          network_out_len
          certificate_public_key_len
          server_finished_payload_len
          app_out
          app_out_len
          next_fuel;
      result
    } else {
      {
        driver_drain_last = step;
        driver_drain_exhausted = false;
      }
    }
  }
}

fn driver_progress_buffered_network_step
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
             result.buffered_network_io_buffered.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_buffered.buffered_network_new_len <=
                  SZ.v raw_capacity /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0
                     (SZ.v result.buffered_network_io_buffered.buffered_network_new_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 client_buffered_network_io_step_correct
                   st1
                   result
                   network_out_bytes
                   app_out_bytes /\
                 B.length
                   (CT.response_app_out
                     result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response
                     app_out_bytes) ==
                   SZ.v
                     result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len /\
                 (SZ.v
                   result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len > 0 ==>
                  result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk /\
                  result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len == 0sz) /\
                 (result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.status == CT.StepOk ==>
                  SZ.v
                    result.buffered_network_io_buffered.buffered_network_read.network_read_written <=
                  SZ.v
                    result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 TChannel.application_log st1 ==
                   (let output =
                      CT.response_app_out
                        result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response
                        app_out_bytes in
                    if B.length output == 0
                    then TChannel.application_log 'st0
                    else
                      Common.ChannelImplementation.append_received
                        (TChannel.application_log 'st0)
                        output) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1))
{
  let empty_buffer = buffered_len = 0sz;
  if empty_buffer {
    let read_result =
      driver_read_buffered_network_bytes_compact_once
      d
      raw
      raw_capacity
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len;
    with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 buffered_after
                read_result.buffered_network_io_buffered.buffered_network_new_len **
              pts_to raw raw_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (CT.network_bytes_end_to_end_correct
      'st0
      st1
      read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes));
    CT.lemma_network_bytes_end_to_end_correct_preserves_config
      'st0
      st1
      read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    CChannel.lemma_network_response_app_out_length
      'st0
      st1
      read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    CChannel.lemma_network_bytes_application_log
      'st0
      st1
      read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    assert (pure (client_buffered_network_io_step_correct
      st1
      read_result
      network_out_bytes
      app_out_bytes));
    assert (pure (CT.client_end_to_end_invariant 'st0 ==>
      CT.client_end_to_end_invariant st1));
    read_result
  } else {
    let processed =
      driver_process_buffered_network_bytes_compact_once
        d
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len;
    with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 buffered_after processed.buffered_network_new_len **
              pts_to raw raw_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (CT.network_bytes_end_to_end_correct
      'st0
      st1
      processed.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal processed.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes));
    CT.lemma_network_bytes_end_to_end_correct_preserves_config
      'st0
      st1
      processed.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal processed.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    CChannel.lemma_network_response_app_out_length
      'st0
      st1
      processed.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal processed.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    CChannel.lemma_network_bytes_application_log
      'st0
      st1
      processed.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal processed.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    assert (pure (CT.client_end_to_end_invariant 'st0 ==>
      CT.client_end_to_end_invariant st1));
    assert (pure (B.length raw_bytes == SZ.v raw_capacity));
    assert (pure (SZ.v processed.buffered_network_new_len <= SZ.v buffered_len));
    assert (pure (SZ.v processed.buffered_network_new_len <= SZ.v raw_capacity));
    let need_more =
      processed.buffered_network_read.network_read_buffer_resp.CT.response.CT.status =
      CT.NeedMoreInput;
    if need_more {
      assert (pure (CT.response_stuttered
        'st0
        st1
        processed.buffered_network_read.network_read_buffer_resp.CT.response
        (Ghost.reveal 'old_network_out)
        network_out_bytes
        (Ghost.reveal 'old_app_out)
        app_out_bytes));
      assert (pure (Seq.equal buffered_after
        (Seq.slice raw_bytes 0 (SZ.v processed.buffered_network_new_len))));
      let read_result =
        driver_read_buffered_network_bytes_compact_once
        d
        raw
        raw_capacity
        processed.buffered_network_new_len
        network_out
        network_out_len
        app_out
        app_out_len;
      with st2 buffered_after2 raw_bytes2 network_out_bytes2 app_out_bytes2.
        assert (driver_exactly d st2 buffered_after2
                  read_result.buffered_network_io_buffered.buffered_network_new_len **
                pts_to raw raw_bytes2 **
                pts_to network_out network_out_bytes2 **
                pts_to app_out app_out_bytes2);
      assert (pure (CT.network_bytes_end_to_end_correct
        st1
        st2
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        (Ghost.reveal
          read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
        network_out_bytes
        network_out_bytes2
        app_out_bytes
        app_out_bytes2));
      CT.lemma_network_bytes_end_to_end_correct_preserves_config
        st1
        st2
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        (Ghost.reveal
          read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
        network_out_bytes
        network_out_bytes2
        app_out_bytes
        app_out_bytes2;
      CChannel.lemma_network_response_app_out_length
        st1
        st2
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        (Ghost.reveal
          read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
        network_out_bytes
        network_out_bytes2
        app_out_bytes
        app_out_bytes2;
      CChannel.lemma_network_bytes_application_log
        st1
        st2
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        (Ghost.reveal
          read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
        network_out_bytes
        network_out_bytes2
        app_out_bytes
        app_out_bytes2;
      assert (pure (
        B.length
          (CT.response_app_out
            processed.buffered_network_read.network_read_buffer_resp.CT.response
            app_out_bytes) == 0));
      assert (pure (
        TChannel.application_log st1 == TChannel.application_log 'st0));
      assert (pure (
        TChannel.application_log st2 ==
          (let output =
             CT.response_app_out
               read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response
               app_out_bytes2 in
           if B.length output == 0
           then TChannel.application_log 'st0
           else
             Common.ChannelImplementation.append_received
               (TChannel.application_log 'st0)
               output)));
      assert (pure (st2.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (client_buffered_network_io_step_correct
        st2
        read_result
        network_out_bytes2
        app_out_bytes2));
      assert (pure (CT.client_end_to_end_invariant st1 ==>
        CT.client_end_to_end_invariant st2));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st2));
      read_result
    } else {
      assert (pure (Seq.equal buffered_after
        (Seq.slice raw_bytes 0 (SZ.v processed.buffered_network_new_len))));
      let result = {
        buffered_network_io_read_len = 0sz;
        buffered_network_io_buffered = processed;
      };
      assert (pure (
        result.buffered_network_io_buffered.buffered_network_new_len ==
        processed.buffered_network_new_len));
      assert (pure (client_buffered_network_io_step_correct
        st1
        result
        network_out_bytes
        app_out_bytes));
      rewrite (driver_exactly d st1 buffered_after processed.buffered_network_new_len) as
        (driver_exactly d st1 buffered_after
          result.buffered_network_io_buffered.buffered_network_new_len);
      result
    }
  }
}

fn top_driver_process_one_local_action
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (certificate_public_key_len:SZ.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 (result.ready_local_processed ==>
                  (CT.client_end_to_end_invariant 'st0 ==>
                   CT.client_end_to_end_invariant st1)) /\
                 (result.ready_local_processed == false ==> st1 == 'st0) /\
                 TChannel.application_log st1 ==
                   TChannel.application_log 'st0)
{
  unfold (top_driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let step =
    driver_handshake_step
      d.top_driver_core
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (step.ready_local_processed ==>
    (CT.client_end_to_end_invariant 'st0 ==>
     CT.client_end_to_end_invariant st1)));
  assert (pure (step.ready_local_processed == false ==> st1 == 'st0));
  assert (pure (step.ready_local_processed ==>
    step.ready_local_action.CT.next_local_kind <>
      CT.LocalDeliverApplicationData /\
    step.ready_local_action.CT.next_local_kind <>
      CT.LocalSendApplicationData));
  CChannel.lemma_optional_receive_local_application_log
    'st0
    st1
    step.ready_local_processed
    step.ready_local_resp
    step.ready_local_action.CT.next_local_kind
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (
    TChannel.application_log st1 == TChannel.application_log 'st0));
  if step.ready_local_processed {
    fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
    step
  } else {
    assert (pure (step.ready_local_written == 0sz));
    assert (pure (st1 == 'st0));
    let ready = step.ready_local_action.CT.next_local_ready;
    if ready {
      let validate =
        step.ready_local_action.CT.next_local_kind = CT.LocalValidateCertificate;
      if validate {
        assert (pure (C.next_local_action_sound
          'st0
          network_out_len
          certificate_public_key_len
          server_finished_payload_len
          step.ready_local_action));
        assert (pure (Some?
          'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
        assert (pure (Some?
          st1.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
        let leaf_len =
          driver_copy_certificate_leaf_der
            d.top_driver_core
            auth_leaf_der
            auth_leaf_der_len;
        with auth_leaf_der_bytes.
          assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                  pts_to auth_leaf_der auth_leaf_der_bytes);
        let leaf_fits = SZ.lte leaf_len certificate_public_key_len;
        if leaf_fits {
          assert (pure (SZ.v leaf_len <= SZ.v certificate_public_key_len));
          A.pts_to_len auth_payload;
          assert (pure (A.length auth_payload == SZ.v certificate_public_key_len));
          A.to_mask auth_payload;
          with auth_payload_mask.
            assert (A.pts_to_mask auth_payload #1.0R auth_payload_mask (fun _ -> True));
          assert (pure (Seq.length auth_payload_mask == SZ.v certificate_public_key_len));
          assert (pure (forall (i:nat). i < Seq.length auth_payload_mask ==>
            Some? (Seq.index auth_payload_mask i)));
          let auth_payload_prefix =
            A.sub auth_payload #1.0R #(fun _ -> True) 0sz (SZ.v leaf_len);
          with auth_payload_prefix_mask.
            assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask (fun _ -> True));
          assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask ==>
            Some? (Seq.index auth_payload_prefix_mask i)));
          A.from_mask auth_payload_prefix;
          with auth_payload_prefix_bytes_before.
            assert (pts_to auth_payload_prefix auth_payload_prefix_bytes_before);
          assert (pure (B.length auth_payload_prefix_bytes_before == SZ.v leaf_len));
          let ok =
            O.validate_certificate_for_local_event
              d.top_driver_auth
              #(st1)
              auth_leaf_der
              auth_leaf_der_len
              leaf_len
              auth_payload_prefix
              leaf_len;
          with auth_payload_prefix_bytes.
            assert (O.is_auth_context d.top_driver_auth **
                    pts_to auth_payload_prefix auth_payload_prefix_bytes);
          assert (pure (B.length auth_payload_prefix_bytes == SZ.v leaf_len));
          if ok {
            assert (pure (CT.local_input_wf
              st1
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes));
            let write_result =
              driver_process_local_event
                d.top_driver_core
                CT.LocalValidateCertificate
                auth_payload_prefix
                leaf_len
                network_out
                network_out_len
                app_out
                app_out_len;
            with st2 network_out_bytes2 app_out_bytes2.
              assert (driver_exactly d.top_driver_core st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                      pts_to auth_payload_prefix auth_payload_prefix_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            assert (pure (CT.local_event_end_to_end_correct
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2));
            CT.lemma_local_event_end_to_end_correct_preserves_config
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2;
            assert (pure (st2.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant st1 ==>
              CT.client_end_to_end_invariant st2));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st2));
            CChannel.lemma_receive_local_application_log
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2;
            assert (pure (
              TChannel.application_log st2 ==
                TChannel.application_log 'st0));
            A.to_mask auth_payload_prefix;
            with auth_payload_prefix_mask_after.
              assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask_after ==>
              Some? (Seq.index auth_payload_prefix_mask_after i)));
            rewrite
              (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True))
              as
              (A.pts_to_mask (A.gsub auth_payload 0 (SZ.v leaf_len)) #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            A.return_sub
              auth_payload
              #1.0R
              #auth_payload_mask
              #auth_payload_prefix_mask_after
              #(fun k -> True /\ ~(0 <= k /\ k < SZ.v leaf_len))
              #(fun _ -> True)
              #0
              #(SZ.v leaf_len);
            with auth_payload_joined_mask.
              assert (A.pts_to_mask auth_payload #1.0R auth_payload_joined_mask
                (fun k ->
                  (True /\ ~(0 <= k /\ k < SZ.v leaf_len)) \/
                  (0 <= k /\ k < SZ.v leaf_len /\ True)));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_joined_mask ==>
              Some? (Seq.index auth_payload_joined_mask i)));
            A.from_mask auth_payload;
            with auth_payload_bytes.
              assert (pts_to auth_payload auth_payload_bytes);
            assert (pure (B.length auth_payload_bytes == SZ.v certificate_public_key_len));
            fold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            A.to_mask auth_payload_prefix;
            with auth_payload_prefix_mask_after.
              assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask_after ==>
              Some? (Seq.index auth_payload_prefix_mask_after i)));
            rewrite
              (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True))
              as
              (A.pts_to_mask (A.gsub auth_payload 0 (SZ.v leaf_len)) #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            A.return_sub
              auth_payload
              #1.0R
              #auth_payload_mask
              #auth_payload_prefix_mask_after
              #(fun k -> True /\ ~(0 <= k /\ k < SZ.v leaf_len))
              #(fun _ -> True)
              #0
              #(SZ.v leaf_len);
            with auth_payload_joined_mask.
              assert (A.pts_to_mask auth_payload #1.0R auth_payload_joined_mask
                (fun k ->
                  (True /\ ~(0 <= k /\ k < SZ.v leaf_len)) \/
                  (0 <= k /\ k < SZ.v leaf_len /\ True)));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_joined_mask ==>
              Some? (Seq.index auth_payload_joined_mask i)));
            A.from_mask auth_payload;
            with auth_payload_bytes.
              assert (pts_to auth_payload auth_payload_bytes);
            assert (pure (B.length auth_payload_bytes == SZ.v certificate_public_key_len));
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            step
          }
        } else {
          fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
          step
        }
      } else {
        let verify =
          step.ready_local_action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
        if verify {
          assert (pure (C.next_local_action_sound
            'st0
            network_out_len
            certificate_public_key_len
            server_finished_payload_len
            step.ready_local_action));
          assert (pure (Some?
            'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
          assert (pure (Some?
            st1.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
          assert (pure (Some?
            'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          assert (pure (Some?
            st1.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          let input_len =
            driver_copy_certificate_verify_input
              d.top_driver_core
              auth_cv_input
              auth_cv_input_len;
          with auth_cv_input_bytes.
            assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                    pts_to auth_cv_input auth_cv_input_bytes);
          let signature_snapshot =
            driver_copy_certificate_verify_signature
              d.top_driver_core
              auth_signature
              auth_signature_len;
          with auth_signature_bytes.
            assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                    pts_to auth_signature auth_signature_bytes);
          let ok =
            O.verify_certificate_signature_for_local_event
              d.top_driver_auth
              #(st1)
              auth_cv_input
              auth_cv_input_len
              input_len
              signature_snapshot.CR.cv_signature_scheme
              auth_signature
              auth_signature_len
              signature_snapshot.CR.cv_signature_len;
          if ok {
            assert (pure (CT.local_input_wf
              st1
              CT.LocalVerifyCertificateSignature
              B.empty));
            let write_result =
              driver_process_local_event
                d.top_driver_core
                CT.LocalVerifyCertificateSignature
                empty_payload
                0sz
                network_out
                network_out_len
                app_out
                app_out_len;
            with st2 network_out_bytes2 app_out_bytes2.
              assert (driver_exactly d.top_driver_core st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                      pts_to empty_payload 'empty_payload_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            assert (pure (CT.local_event_end_to_end_correct
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2));
            CT.lemma_local_event_end_to_end_correct_preserves_config
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2;
            assert (pure (st2.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant st1 ==>
              CT.client_end_to_end_invariant st2));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st2));
            CChannel.lemma_receive_local_application_log
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2;
            assert (pure (
              TChannel.application_log st2 ==
                TChannel.application_log 'st0));
            fold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            step
          }
        } else {
          fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
          step
        }
      }
    } else {
      fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
      step
    }
  }
}

fn rec driver_handshake
  (d:top_driver)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.driver_workflow_rx_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1) /\
                 (result.driver_workflow_status == DriverWorkflowOk ==>
                  st1.CS.cs_model.CS.model_control == CS.ControlApplicationData))
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    {
      driver_workflow_status = DriverWorkflowExhausted;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    unfold (top_driver_exactly d 'st0 'buffered buffered_len);
    let snapshot = driver_control_snapshot d.top_driver_core;
    with st_snapshot.
      assert (driver_exactly d.top_driver_core st_snapshot 'buffered buffered_len);
    assert (pure (st_snapshot.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    fold (top_driver_exactly d st_snapshot 'buffered buffered_len);
    let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
    if app_ready {
      assert (pure (CR.control_snapshot_matches snapshot st_snapshot));
      assert (pure (st_snapshot.CS.cs_model.CS.model_control == CS.ControlApplicationData));
      {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len = buffered_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = no_op_io;
      }
    } else {
      let failed = snapshot.CR.snapshot_control_tag = 5uy;
      if failed {
        {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len = buffered_len;
          driver_workflow_local = {
            driver_drain_last = no_op_local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = no_op_io;
        }
      } else {
        let local =
          top_driver_process_one_local_action
            d
            empty_payload
            network_out
            network_out_len
            auth_leaf_der
            auth_leaf_der_len
            auth_payload
            certificate_public_key_len
            auth_cv_input
            auth_cv_input_len
            auth_signature
            auth_signature_len
            server_finished_payload_len
            app_out
            app_out_len;
        with st_local network_out_local auth_leaf_der_local auth_payload_local auth_cv_input_local auth_signature_local app_out_local.
          assert (top_driver_exactly d st_local 'buffered buffered_len **
                  pts_to network_out network_out_local **
                  pts_to auth_leaf_der auth_leaf_der_local **
                  pts_to auth_payload auth_payload_local **
                  pts_to auth_cv_input auth_cv_input_local **
                  pts_to auth_signature auth_signature_local **
                  pts_to app_out app_out_local);
        assert (pure (st_local.CS.cs_model.CS.model_config ==
          st_snapshot.CS.cs_model.CS.model_config));
        assert (pure (st_local.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
        if local.ready_local_processed {
          assert (pure (local.ready_local_processed == true));
          assert (pure (local.ready_local_processed == true ==>
            (CT.client_end_to_end_invariant 'st0 ==>
             CT.client_end_to_end_invariant st_local)));
          assert (pure (CT.client_end_to_end_invariant 'st0 ==>
            CT.client_end_to_end_invariant st_local))
        } else {
          assert (pure (st_local == 'st0));
          assert (pure (CT.client_end_to_end_invariant 'st0 ==>
            CT.client_end_to_end_invariant st_local))
        };
        if local.ready_local_processed {
          let ok = local.ready_local_resp.CT.status = CT.StepOk;
          let wrote_all =
            local.ready_local_written = local.ready_local_resp.CT.network_out_len;
          if (ok && wrote_all) {
            let next_fuel = SZ.sub fuel 1sz;
            assert (pure (SZ.v next_fuel < SZ.v fuel));
            driver_handshake
              d
              empty_payload
              raw
              raw_capacity
              buffered_len
              network_out
              network_out_len
              auth_leaf_der
              auth_leaf_der_len
              auth_payload
              auth_cv_input
              auth_cv_input_len
              auth_signature
              auth_signature_len
              certificate_public_key_len
              server_finished_payload_len
              app_out
              app_out_len
              local_fuel
              next_fuel
          } else {
            {
              driver_workflow_status = DriverWorkflowStepFailed;
              driver_workflow_rx_len = buffered_len;
              driver_workflow_local = {
                driver_drain_last = local;
                driver_drain_exhausted = false;
              };
              driver_workflow_network = no_op_io;
            }
          }
        } else {
          let still_ready = local.ready_local_action.CT.next_local_ready;
          if still_ready {
            {
              driver_workflow_status = DriverWorkflowStepFailed;
              driver_workflow_rx_len = buffered_len;
              driver_workflow_local = {
                driver_drain_last = local;
                driver_drain_exhausted = false;
              };
              driver_workflow_network = no_op_io;
            }
          } else {
            assert (pure (B.length 'old_raw == SZ.v raw_capacity));
            assert (pure (SZ.v buffered_len <= SZ.v raw_capacity));
            assert (pure (Seq.equal 'buffered
              (Seq.slice 'old_raw 0 (SZ.v buffered_len))));
            assert (pure (B.length network_out_local == SZ.v network_out_len));
            assert (pure (B.length app_out_local == SZ.v app_out_len));
            assert (pure (L.max_record_fragment_len <= SZ.v app_out_len));
            assert (pure (st_local == 'st0));
            unfold (top_driver_exactly d st_local 'buffered buffered_len);
            let network =
              driver_progress_buffered_network_step
                d.top_driver_core
                raw
                raw_capacity
                buffered_len
                network_out
                network_out_len
                app_out
                app_out_len;
            with st_network buffered_network raw_network network_out_network app_out_network.
              assert (driver_exactly d.top_driver_core st_network
                        buffered_network
                        network.buffered_network_io_buffered.buffered_network_new_len **
                      pts_to raw raw_network **
                      pts_to network_out network_out_network **
                      pts_to app_out app_out_network);
            assert (pure (st_network.CS.cs_model.CS.model_config ==
              st_local.CS.cs_model.CS.model_config));
            assert (pure (st_network.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            fold (top_driver_exactly d st_network
              buffered_network
              network.buffered_network_io_buffered.buffered_network_new_len);
            assert (pure (CT.client_end_to_end_invariant st_local ==>
              CT.client_end_to_end_invariant st_network));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st_network));
            let net_read =
              network.buffered_network_io_buffered.buffered_network_read;
            let net_resp = net_read.network_read_buffer_resp.CT.response;
            let net_ok = net_resp.CT.status = CT.StepOk;
            let net_need_more = net_resp.CT.status = CT.NeedMoreInput;
            let net_bad_status = (net_ok || net_need_more) = false;
            let net_wrote_all =
              net_read.network_read_written = net_resp.CT.network_out_len;
            let net_short_write = net_ok && (net_wrote_all = false);
            let net_failed = net_bad_status || net_short_write;
            if net_failed {
              let result = {
                driver_workflow_status = DriverWorkflowStepFailed;
                driver_workflow_rx_len =
                  network.buffered_network_io_buffered.buffered_network_new_len;
                driver_workflow_local = {
                  driver_drain_last = local;
                  driver_drain_exhausted = false;
                };
                driver_workflow_network = network;
              };
              assert (pure (result.driver_workflow_status == DriverWorkflowStepFailed));
              assert (pure (result.driver_workflow_rx_len ==
                network.buffered_network_io_buffered.buffered_network_new_len));
              assert (pure (B.length raw_network == SZ.v raw_capacity));
              assert (pure (B.length auth_leaf_der_local == SZ.v auth_leaf_der_len));
              assert (pure (B.length auth_payload_local == SZ.v certificate_public_key_len));
              assert (pure (B.length auth_cv_input_local == SZ.v auth_cv_input_len));
              assert (pure (B.length auth_signature_local == SZ.v auth_signature_len));
              assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
              assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
              assert (pure (Seq.equal buffered_network
                (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
              assert (pure (B.length network_out_network == SZ.v network_out_len));
              assert (pure (B.length app_out_network == SZ.v app_out_len));
              assert (pure (CT.client_end_to_end_invariant 'st0 ==>
                CT.client_end_to_end_invariant st_network));
              assert (pure (result.driver_workflow_status == DriverWorkflowOk ==>
                st_network.CS.cs_model.CS.model_control == CS.ControlApplicationData));
              rewrite (top_driver_exactly
                d
                st_network
                buffered_network
                network.buffered_network_io_buffered.buffered_network_new_len) as
                (top_driver_exactly
                  d
                  st_network
                  buffered_network
                  result.driver_workflow_rx_len);
              result
            } else {
              assert (pure (0 < SZ.v fuel));
              let next_fuel = SZ.sub fuel 1sz;
              assert (pure (SZ.v next_fuel < SZ.v fuel));
              assert (pure (B.length 'empty_payload_bytes == 0));
              assert (pure (B.length raw_network == SZ.v raw_capacity));
              assert (pure (
                SZ.v network.buffered_network_io_buffered.buffered_network_new_len <=
                  SZ.v raw_capacity));
              assert (pure (
                B.length buffered_network ==
                  SZ.v network.buffered_network_io_buffered.buffered_network_new_len));
              assert (pure (Seq.equal
                buffered_network
                (Seq.slice
                  raw_network
                  0
                  (SZ.v network.buffered_network_io_buffered.buffered_network_new_len))));
              assert (pure (B.length network_out_network == SZ.v network_out_len));
              assert (pure (B.length auth_leaf_der_local == SZ.v auth_leaf_der_len));
              assert (pure (
                B.length auth_payload_local == SZ.v certificate_public_key_len));
              assert (pure (B.length auth_cv_input_local == SZ.v auth_cv_input_len));
              assert (pure (B.length auth_signature_local == SZ.v auth_signature_len));
              assert (pure (
                Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len));
              assert (pure (
                SZ.v certificate_public_key_len <= Bounds.max_public_key_len));
              assert (pure (
                Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len));
              assert (pure (L.max_signature_len <= SZ.v auth_signature_len));
              assert (pure (B.length app_out_network == SZ.v app_out_len));
              assert (pure (L.max_record_fragment_len <= SZ.v app_out_len));
              driver_handshake
                d
                empty_payload
                raw
                raw_capacity
                network.buffered_network_io_buffered.buffered_network_new_len
                network_out
                network_out_len
                auth_leaf_der
                auth_leaf_der_len
                auth_payload
                auth_cv_input
                auth_cv_input_len
                auth_signature
                auth_signature_len
                certificate_public_key_len
                server_finished_payload_len
                app_out
                app_out_len
                local_fuel
                next_fuel
            }
          }
        }
      }
    }
  }
}
