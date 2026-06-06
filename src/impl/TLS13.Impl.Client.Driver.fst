module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module IO = TLS13.IO
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

noextract
let internal_local_action_kind
  (kind:CT.local_event_kind)
  : prop =
  match kind with
  | CT.LocalValidateCertificate
  | CT.LocalVerifyCertificateSignature ->
    False
  | _ ->
    True

let lemma_ready_internal_action_empty_payload_wf
  (st:TLS13.Spec.ConnectionState.connection_state)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (action:CT.next_local_action)
  (payload:B.bytes)
  : Lemma
      (requires C.next_local_action_sound
                  st
                  network_out_len
                  certificate_public_key_len
                  server_finished_payload_len
                  action /\
                action.CT.next_local_ready == true /\
                internal_local_action_kind action.CT.next_local_kind /\
                Seq.equal payload B.empty)
      (ensures CT.local_input_wf st action.CT.next_local_kind payload)
=
  assert (C.next_local_action_internal_input_ready st action);
  match action.CT.next_local_kind with
  | CT.LocalValidateCertificate ->
    assert False
  | CT.LocalVerifyCertificateSignature ->
    assert False
  | CT.LocalVerifyFinished ->
    ()
  | CT.LocalDeliverApplicationData ->
    assert False
  | CT.LocalSendApplicationData ->
    assert False
  | CT.LocalSendCloseNotify ->
    assert False
  | CT.LocalFail ->
    assert False
  | _ ->
    ()

fn driver_connect
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to connect_host 'connect_host_bytes **
           pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len /\
                 B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: option driver
  ensures pts_to connect_host 'connect_host_bytes **
          pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some d ->
             driver_exactly
               d
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds) **
             pure (CT.client_state_correct
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds) /\
                   CT.client_end_to_end_invariant
                     (CR.configured_initial_state
                       (Ghost.reveal 'server_name_bytes)
                       (Ghost.reveal 'trust_anchors_bytes)
                       validation_time_seconds))
           | None ->
             emp)
{
  let ch_opt = IO.connect_tcp connect_host connect_host_len port;
  match ch_opt {
    None -> {
    None
  }
    Some ch -> {
    let c =
      C.new_client
        server_name
        server_name_len
        trust_anchors
        trust_anchors_len
        validation_time_seconds;
    rewrite
      (CR.connection_exactly
        c
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds))
      as
      (C.connection_exactly
        c
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds));
    fold
      (driver_exactly
        {
          driver_client = c;
          driver_channel = ch;
        }
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds));
    Some {
      driver_client = c;
      driver_channel = ch;
    }
  }
  }
}

fn driver_control_snapshot
  (d:driver)
  requires driver_exactly d 'st0
  returns snapshot:CR.control_snapshot
  ensures driver_exactly d 'st0 **
          pure (CR.control_snapshot_matches snapshot 'st0)
{
  unfold (driver_exactly d 'st0);
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot = C.control_snapshot d.driver_client;
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0);
  snapshot
}

fn driver_copy_certificate_leaf_der
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                 | Some leaf ->
                   SZ.v copied_len == B.length leaf /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                 | None -> False))
{
  unfold (driver_exactly d 'st0);
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
  fold (driver_exactly d 'st0);
  copied_len
}

fn driver_copy_certificate_verify_input
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                 | Some input ->
                   SZ.v copied_len == B.length input /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                 | None -> False))
{
  unfold (driver_exactly d 'st0);
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
  fold (driver_exactly d 'st0);
  copied_len
}

fn driver_copy_certificate_verify_signature
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:CR.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          driver_exactly d 'st0 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.CR.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                 | Some cv ->
                   L.signature_scheme_matches snapshot.CR.cv_signature_scheme cv.M.scheme /\
                   SZ.v snapshot.CR.cv_signature_len == B.length cv.M.signature /\
                   Seq.equal
                     (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                     cv.M.signature
                 | None -> False))
{
  unfold (driver_exactly d 'st0);
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
  fold (driver_exactly d 'st0);
  snapshot
}

fn process_local_event_and_write_once
  (c:C.client)
  (ch:IO.channel)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           IO.is_channel ch **
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
           IO.is_channel ch **
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
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))
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
  let ok = resp.CT.status = CT.StepOk;
  if ok {
    assert (pure (resp.CT.status == CT.StepOk));
    assert (pure (CT.response_wf resp network_out_bytes app_out_bytes));
    assert (pure (SZ.v resp.CT.network_out_len <= B.length network_out_bytes));
    let written = IO.write ch network_out resp.CT.network_out_len;
    assert (pure (SZ.v written <= SZ.v resp.CT.network_out_len));
    assert (pure (resp.CT.status == CT.StepOk ==>
      SZ.v written <= SZ.v resp.CT.network_out_len));
    assert (pure (resp.CT.status == CT.StepOk \/ written == 0sz));
    {
      local_write_resp = resp;
      local_write_written = written;
    }
  } else {
    assert (pure (SZ.v 0sz <= SZ.v resp.CT.network_out_len));
    assert (pure (resp.CT.status == CT.StepOk ==>
      SZ.v 0sz <= SZ.v resp.CT.network_out_len));
    assert (pure (resp.CT.status == CT.StepOk \/ 0sz == 0sz));
    {
      local_write_resp = resp;
      local_write_written = 0sz;
    }
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
  requires driver_exactly d 'st0 **
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
           driver_exactly d st1 **
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
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))
{
  unfold (driver_exactly d 'st0);
  let result =
    process_local_event_and_write_once
      d.driver_client
      d.driver_channel
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
  fold (driver_exactly d st1);
  result
}

fn receive_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw 'raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                   'st0
                   st1
                   result.network_write_buffer_resp
                   (Ghost.reveal 'raw_bytes)
                   (Ghost.reveal 'old_network_out)
                   network_out_bytes
                   (Ghost.reveal 'old_app_out)
                   app_out_bytes /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                  CT.StepOk ==>
                  SZ.v result.network_write_written <=
                  SZ.v result.network_write_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                  CT.StepOk \/
                  result.network_write_written == 0sz))
{
  unfold (driver_exactly d 'st0);
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let buffer_resp =
    C.process_network_bytes
      d.driver_client
      raw
      raw_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (CR.connection_exactly d.driver_client st1 **
            pts_to raw 'raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (CR.connection_exactly d.driver_client st1)
    as (C.connection_exactly d.driver_client st1);
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    (Ghost.reveal 'raw_bytes)
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  let ok = buffer_resp.CT.response.CT.status = CT.StepOk;
  if ok {
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk));
    assert (pure (CT.response_wf buffer_resp.CT.response network_out_bytes app_out_bytes));
    assert (pure (SZ.v buffer_resp.CT.response.CT.network_out_len <= B.length network_out_bytes));
    let written = IO.write d.driver_channel network_out buffer_resp.CT.response.CT.network_out_len;
    assert (pure (SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
      SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk \/ written == 0sz));
    fold (driver_exactly d st1);
    {
      network_write_buffer_resp = buffer_resp;
      network_write_written = written;
    }
  } else {
    assert (pure (SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
      SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk \/ 0sz == 0sz));
    fold (driver_exactly d st1);
    {
      network_write_buffer_resp = buffer_resp;
      network_write_written = 0sz;
    }
  }
}

fn driver_receive_application_data_once
  (d:driver)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw 'raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.network_write_buffer_resp
                  (Ghost.reveal 'raw_bytes)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                  CT.StepOk ==>
                  SZ.v result.network_write_written <=
                  SZ.v result.network_write_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_write_buffer_resp.CT.response.CT.status ==
                  CT.StepOk \/
                  result.network_write_written == 0sz))
{
  receive_network_bytes_once
    d
    raw
    raw_len
    network_out
    network_out_len
    app_out
    app_out_len
}

fn driver_read_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                   SZ.v result.network_read_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
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
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_read_written == 0sz))
{
  unfold (driver_exactly d 'st0);
  let read_len = IO.read d.driver_channel raw raw_capacity;
  with raw_after.
    assert (IO.is_channel d.driver_channel **
            pts_to raw raw_after);
  assert (pure (B.length raw_after == SZ.v raw_capacity));
  assert (pure (SZ.v read_len <= SZ.v raw_capacity));
  A.pts_to_len raw;
  assert (pure (A.length raw == SZ.v raw_capacity));
  A.to_mask raw;
  with raw_mask.
    assert (A.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v raw_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index raw_after i)));
  let raw_prefix_array =
    A.sub raw #1.0R #(fun _ -> True) 0sz (SZ.v read_len);
  with raw_prefix_mask.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask ==>
    Some? (Seq.index raw_prefix_mask i)));
  A.from_mask raw_prefix_array;
  with raw_prefix.
    assert (pts_to raw_prefix_array raw_prefix);
  assert (pure (B.length raw_prefix == SZ.v read_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let buffer_resp =
    C.process_network_bytes
      d.driver_client
      raw_prefix_array
      read_len
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
  A.to_mask raw_prefix_array;
  with raw_prefix_mask_after.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Some? (Seq.index raw_prefix_mask_after i)));
  rewrite
    (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True))
    as
    (A.pts_to_mask (A.gsub raw 0 (SZ.v read_len)) #1.0R raw_prefix_mask_after (fun _ -> True));
  A.return_sub
    raw
    #1.0R
    #raw_mask
    #raw_prefix_mask_after
    #(fun k -> True /\ ~(0 <= k /\ k < SZ.v read_len))
    #(fun _ -> True)
    #0
    #(SZ.v read_len);
  with raw_joined_mask.
    assert (A.pts_to_mask raw #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(0 <= k /\ k < SZ.v read_len)) \/
        (0 <= k /\ k < SZ.v read_len /\ True)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v read_len)) \/
     (0 <= i /\ i < SZ.v read_len /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  A.from_mask raw;
  with raw_bytes.
    assert (pts_to raw raw_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  let ok = buffer_resp.CT.response.CT.status = CT.StepOk;
  if ok {
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk));
    assert (pure (CT.response_wf buffer_resp.CT.response network_out_bytes app_out_bytes));
    assert (pure (SZ.v buffer_resp.CT.response.CT.network_out_len <= B.length network_out_bytes));
    let written = IO.write d.driver_channel network_out buffer_resp.CT.response.CT.network_out_len;
    assert (pure (SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
      SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk \/ written == 0sz));
    fold (driver_exactly d st1);
    assert (pure (B.length raw_prefix == SZ.v read_len));
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
      B.length raw_prefix == SZ.v read_len /\
      SZ.v read_len <= SZ.v raw_capacity /\
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
      (buffer_resp.CT.response.CT.status == CT.StepOk ==>
       SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len) /\
      (buffer_resp.CT.response.CT.status == CT.StepOk \/ written == 0sz)));
    assert (driver_exactly d st1 **
            pts_to raw raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes **
            pure (B.length raw_bytes == SZ.v raw_capacity /\
              B.length raw_prefix == SZ.v read_len /\
              SZ.v read_len <= SZ.v raw_capacity /\
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
              (buffer_resp.CT.response.CT.status == CT.StepOk ==>
               SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len) /\
              (buffer_resp.CT.response.CT.status == CT.StepOk \/ written == 0sz)));
    {
      network_read_len = read_len;
      network_read_buffer_resp = buffer_resp;
      network_read_written = written;
      network_read_prefix = Ghost.hide raw_prefix;
    }
  } else {
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
      SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk \/ 0sz == 0sz));
    fold (driver_exactly d st1);
    assert (pure (B.length raw_prefix == SZ.v read_len));
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
      B.length raw_prefix == SZ.v read_len /\
      SZ.v read_len <= SZ.v raw_capacity /\
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
      (buffer_resp.CT.response.CT.status == CT.StepOk ==>
       SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len) /\
      (buffer_resp.CT.response.CT.status == CT.StepOk \/ 0sz == 0sz)));
    assert (driver_exactly d st1 **
            pts_to raw raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes **
            pure (B.length raw_bytes == SZ.v raw_capacity /\
              B.length raw_prefix == SZ.v read_len /\
              SZ.v read_len <= SZ.v raw_capacity /\
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
              (buffer_resp.CT.response.CT.status == CT.StepOk ==>
               SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len) /\
              (buffer_resp.CT.response.CT.status == CT.StepOk \/ 0sz == 0sz)));
    {
      network_read_len = read_len;
      network_read_buffer_resp = buffer_resp;
      network_read_written = 0sz;
      network_read_prefix = Ghost.hide raw_prefix;
    }
  }
}

fn driver_read_application_data_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                   SZ.v result.network_read_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
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
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.network_read_written == 0sz))
{
  driver_read_network_bytes_once
    d
    raw
    raw_capacity
    network_out
    network_out_len
    app_out
    app_out_len
}

fn process_ready_internal_local_action_once
  (c:C.client)
  (ch:IO.channel)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           IO.is_channel ch **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           IO.is_channel ch **
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
                   SZ.v result.ready_local_resp.CT.network_out_len) /\
                  (result.ready_local_resp.CT.status == CT.StepOk \/
                   result.ready_local_written == 0sz)) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz))
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
      assert (pure (write_result.local_write_resp.CT.status == CT.StepOk ==>
        SZ.v write_result.local_write_written <=
        SZ.v write_result.local_write_resp.CT.network_out_len));
      assert (pure (write_result.local_write_resp.CT.status == CT.StepOk \/
        write_result.local_write_written == 0sz));
      {
        ready_local_action = action;
        ready_local_processed = true;
        ready_local_resp = write_result.local_write_resp;
        ready_local_written = write_result.local_write_written;
      }
    }
  } else {
    {
      ready_local_action = action;
      ready_local_processed = false;
      ready_local_resp = no_op_resp;
      ready_local_written = 0sz;
    }
  }
}

fn driver_handshake_step
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
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
                   SZ.v result.ready_local_resp.CT.network_out_len) /\
                  (result.ready_local_resp.CT.status == CT.StepOk \/
                   result.ready_local_written == 0sz)) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz))
{
  unfold (driver_exactly d 'st0);
  let result =
    process_ready_internal_local_action_once
      d.driver_client
      d.driver_channel
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  fold (driver_exactly d st1);
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
  requires driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: driver_drain_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
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
      assert (driver_exactly d st1 **
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

fn send_application_data_once
  (c:C.client)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           IO.is_channel ch **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           IO.is_channel ch **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))
{
  process_local_event_and_write_once
    c
    ch
    CT.LocalSendApplicationData
    payload
    payload_len
    network_out
    network_out_len
    app_out
    app_out_len
}

fn driver_send_application_data
  (d:driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))
{
  unfold (driver_exactly d 'st0);
  let result =
    send_application_data_once
      d.driver_client
      d.driver_channel
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
  fold (driver_exactly d st1);
  result
}

fn driver_send_close_notify
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendCloseNotify
                   (Ghost.reveal 'empty_payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len) /\
                 (result.local_write_resp.CT.status == CT.StepOk \/
                  result.local_write_written == 0sz))
{
  unfold (driver_exactly d 'st0);
  assert (pure (CT.local_input_wf
    'st0
    CT.LocalSendCloseNotify
    (Ghost.reveal 'empty_payload_bytes)));
  let result =
    process_local_event_and_write_once
      d.driver_client
      d.driver_channel
      CT.LocalSendCloseNotify
      empty_payload
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  fold (driver_exactly d st1);
  result
}

fn driver_close (d:driver)
  requires driver_exactly d 'st0
  ensures C.connection_exactly d.driver_client 'st0
{
  unfold (driver_exactly d 'st0);
  IO.close d.driver_channel
}
