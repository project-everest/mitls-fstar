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
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

let driver_network_out_capacity : SZ.t = SZ.uint_to_t 20000
let driver_app_out_capacity : SZ.t = SZ.uint_to_t 16640
let driver_rx_capacity : SZ.t = SZ.uint_to_t 65535
let driver_public_key_payload_capacity : SZ.t = SZ.uint_to_t 4096
let driver_auth_leaf_der_capacity : SZ.t = SZ.uint_to_t 32768
let driver_certificate_verify_input_capacity : SZ.t = SZ.uint_to_t 256
let driver_signature_capacity : SZ.t = SZ.uint_to_t 4096
let driver_server_finished_payload_len : SZ.t = 36sz

noeq type client_driver = {
  client_driver_client: C.client;
  client_driver_auth: O.auth_context;
  client_driver_channel: Box.box (option IO.channel);
  client_driver_buffered_len: Box.box SZ.t;
  client_driver_empty_payload: V.vec U8.t;
  client_driver_raw: V.vec U8.t;
  client_driver_network_out: V.vec U8.t;
  client_driver_auth_leaf_der: V.vec U8.t;
  client_driver_auth_payload: V.vec U8.t;
  client_driver_auth_cv_input: V.vec U8.t;
  client_driver_auth_signature: V.vec U8.t;
  client_driver_app_out: V.vec U8.t;
}

noeq type driver = {
  driver_client: C.client;
  driver_channel: IO.channel;
}

noextract
let driver_exactly
  (d:driver)
  (st:TLS13.Spec.ConnectionState.connection_state)
  : slprop =
  C.connection_exactly d.driver_client st **
  IO.is_channel d.driver_channel

noeq type top_driver = {
  top_driver_core: driver;
  top_driver_auth: O.auth_context;
}

let no_channel : option IO.channel = None

noextract
let top_driver_exactly
  (d:top_driver)
  (st:TLS13.Spec.ConnectionState.connection_state)
  : slprop =
  driver_exactly d.top_driver_core st **
  O.is_auth_context d.top_driver_auth

noextract
let client_driver_buffers
  (d:client_driver)
  (buffered_len:SZ.t)
  : slprop =
  Box.pts_to d.client_driver_buffered_len buffered_len **
  exists* empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out.
    V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.client_driver_raw #1.0R raw **
    V.pts_to d.client_driver_network_out #1.0R network_out **
    V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
    V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
    V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
    V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
    V.pts_to d.client_driver_app_out #1.0R app_out **
    pure (
      B.length empty_payload == 0 /\
      B.length raw == SZ.v driver_rx_capacity /\
      B.length network_out == SZ.v driver_network_out_capacity /\
      B.length auth_leaf_der == SZ.v driver_auth_leaf_der_capacity /\
      B.length auth_payload == SZ.v driver_public_key_payload_capacity /\
      B.length auth_cv_input == SZ.v driver_certificate_verify_input_capacity /\
      B.length auth_signature == SZ.v driver_signature_capacity /\
      B.length app_out == SZ.v driver_app_out_capacity /\
      SZ.v buffered_len <= SZ.v driver_rx_capacity /\
      Bounds.max_handshake_flight_len <= SZ.v driver_auth_leaf_der_capacity /\
      SZ.v driver_public_key_payload_capacity <= Bounds.max_public_key_len /\
      Bounds.max_certificate_verify_input_len <= SZ.v driver_certificate_verify_input_capacity /\
      L.max_signature_len <= SZ.v driver_signature_capacity /\
      L.max_record_fragment_len <= SZ.v driver_app_out_capacity /\
      V.is_full_vec d.client_driver_empty_payload /\
      V.is_full_vec d.client_driver_raw /\
      V.is_full_vec d.client_driver_network_out /\
      V.is_full_vec d.client_driver_auth_leaf_der /\
      V.is_full_vec d.client_driver_auth_payload /\
      V.is_full_vec d.client_driver_auth_cv_input /\
      V.is_full_vec d.client_driver_auth_signature /\
      V.is_full_vec d.client_driver_app_out)

noextract
let client_driver_live
  (d:client_driver)
  (st:TLS13.Spec.ConnectionState.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  O.is_auth_context d.client_driver_auth **
  exists* buffered_len.
    Box.pts_to d.client_driver_channel no_channel **
    client_driver_buffers d buffered_len

noextract
let client_driver_connected
  (d:client_driver)
  (st:TLS13.Spec.ConnectionState.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  O.is_auth_context d.client_driver_auth **
  exists* ch buffered_len.
    Box.pts_to d.client_driver_channel (Some ch) **
    IO.is_channel ch **
    client_driver_buffers d buffered_len

noextract
let client_driver_closed
  (d:client_driver)
  (st:TLS13.Spec.ConnectionState.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st

type network_write_result = {
  network_write_buffer_resp: CT.client_buffer_response;
  network_write_written: SZ.t;
}

type local_write_result = {
  local_write_resp: CT.client_response;
  local_write_written: SZ.t;
}

noeq type network_read_result = {
  network_read_len: SZ.t;
  network_read_buffer_resp: CT.client_buffer_response;
  network_read_written: SZ.t;
  network_read_prefix: Ghost.erased B.bytes;
}

noeq type buffered_network_result = {
  buffered_network_read: network_read_result;
  buffered_network_new_len: SZ.t;
}

noeq type buffered_network_io_result = {
  buffered_network_io_read_len: SZ.t;
  buffered_network_io_buffered: buffered_network_result;
}

noeq type buffered_network_loop_result = {
  buffered_network_loop_last: buffered_network_result;
  buffered_network_loop_exhausted: bool;
}

type ready_local_action_result = {
  ready_local_action: CT.next_local_action;
  ready_local_processed: bool;
  ready_local_resp: CT.client_response;
  ready_local_written: SZ.t;
}

type driver_drain_result = {
  driver_drain_last: ready_local_action_result;
  driver_drain_exhausted: bool;
}

noeq type driver_workflow_result = {
  driver_workflow_status: driver_workflow_status;
  driver_workflow_rx_len: SZ.t;
  driver_workflow_local: driver_drain_result;
  driver_workflow_network: buffered_network_io_result;
}

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

fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: option client_driver
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some d ->
             client_driver_live
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
  let auth_opt =
    O.auth_context_new
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  match auth_opt {
    None -> {
      None
    }
    Some auth -> {
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
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy driver_rx_capacity;
      let network_out = V.alloc 0uy driver_network_out_capacity;
      let auth_leaf_der = V.alloc 0uy driver_auth_leaf_der_capacity;
      let auth_payload = V.alloc 0uy driver_public_key_payload_capacity;
      let auth_cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
      let auth_signature = V.alloc 0uy driver_signature_capacity;
      let app_out = V.alloc 0uy driver_app_out_capacity;
      assert (pure (Bounds.max_handshake_flight_len <= SZ.v driver_auth_leaf_der_capacity));
      assert (pure (SZ.v driver_public_key_payload_capacity <= Bounds.max_public_key_len));
      assert (pure (Bounds.max_certificate_verify_input_len <= SZ.v driver_certificate_verify_input_capacity));
      assert (pure (L.max_signature_len <= SZ.v driver_signature_capacity));
      assert (pure (L.max_record_fragment_len <= SZ.v driver_app_out_capacity));
      let d = {
        client_driver_client = c;
        client_driver_auth = auth;
        client_driver_channel = channel;
        client_driver_buffered_len = buffered_len;
        client_driver_empty_payload = empty_payload;
        client_driver_raw = raw;
        client_driver_network_out = network_out;
        client_driver_auth_leaf_der = auth_leaf_der;
        client_driver_auth_payload = auth_payload;
        client_driver_auth_cv_input = auth_cv_input;
        client_driver_auth_signature = auth_signature;
        client_driver_app_out = app_out;
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.client_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.client_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.client_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.client_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to auth_leaf_der #1.0R (Seq.create (SZ.v driver_auth_leaf_der_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_leaf_der #1.0R (Seq.create (SZ.v driver_auth_leaf_der_capacity) 0uy));
      rewrite
        (V.pts_to auth_payload #1.0R (Seq.create (SZ.v driver_public_key_payload_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_payload #1.0R (Seq.create (SZ.v driver_public_key_payload_capacity) 0uy));
      rewrite
        (V.pts_to auth_cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to auth_signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (C.connection_exactly
          c
          (CR.configured_initial_state
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds))
        as
        (C.connection_exactly
          d.client_driver_client
          (CR.configured_initial_state
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds));
      rewrite (O.is_auth_context auth) as (O.is_auth_context d.client_driver_auth);
      fold (client_driver_buffers d 0sz);
      fold
        (client_driver_live
          d
          (CR.configured_initial_state
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds));
      Some d
    }
  }
}

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

fn driver_open
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
  returns result: option top_driver
  ensures pts_to connect_host 'connect_host_bytes **
          pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some d ->
             top_driver_exactly
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
  let auth_opt =
    O.auth_context_new
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  match auth_opt {
    None -> {
      None
    }
    Some auth -> {
      let connected =
        driver_connect
          connect_host
          connect_host_len
          port
          server_name
          server_name_len
          trust_anchors
          trust_anchors_len
          validation_time_seconds;
      match connected {
        None -> {
          O.auth_context_free auth;
          None
        }
        Some d -> {
          fold
            (top_driver_exactly
              {
                top_driver_core = d;
                top_driver_auth = auth;
              }
              (CR.configured_initial_state
                (Ghost.reveal 'server_name_bytes)
                (Ghost.reveal 'trust_anchors_bytes)
                validation_time_seconds));
          Some {
            top_driver_core = d;
            top_driver_auth = auth;
          }
        }
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

fn driver_process_buffered_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
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
                 result.network_read_len == buffered_len /\
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
  A.to_mask raw_prefix_array;
  with raw_prefix_mask_after.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Some? (Seq.index raw_prefix_mask_after i)));
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
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v buffered_len)) \/
     (0 <= i /\ i < SZ.v buffered_len /\ True))));
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
      (buffer_resp.CT.response.CT.status == CT.StepOk ==>
       SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len) /\
      (buffer_resp.CT.response.CT.status == CT.StepOk \/ written == 0sz)));
    {
      network_read_len = buffered_len;
      network_read_buffer_resp = buffer_resp;
      network_read_written = written;
      network_read_prefix = Ghost.hide raw_prefix;
    }
  } else {
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
      SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len));
    assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk \/ 0sz == 0sz));
    fold (driver_exactly d st1);
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
      (buffer_resp.CT.response.CT.status == CT.StepOk ==>
       SZ.v 0sz <= SZ.v buffer_resp.CT.response.CT.network_out_len) /\
      (buffer_resp.CT.response.CT.status == CT.StepOk \/ 0sz == 0sz)));
    {
      network_read_len = buffered_len;
      network_read_buffer_resp = buffer_resp;
      network_read_written = 0sz;
      network_read_prefix = Ghost.hide raw_prefix;
    }
  }
}

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
                 SZ.v new_len <= SZ.v buffered_len)
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  let no_shift = consumed_len = 0sz;
  if no_shift {
    assert (pure (new_len == buffered_len));
    new_len
  } else {
    let mut i = 0sz;
    while ((R.read i) `SZ.lt` new_len)
      invariant live i
      invariant exists* raw_loop.
        pts_to raw raw_loop **
        pure (B.length raw_loop == SZ.v raw_capacity /\
              SZ.v (R.read i) <= SZ.v new_len /\
              SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
              SZ.v new_len <= SZ.v buffered_len /\
              SZ.v consumed_len <= SZ.v buffered_len /\
              SZ.v buffered_len <= SZ.v raw_capacity)
    {
      let vi = R.read i;
      assert (pure (SZ.v vi < SZ.v new_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v buffered_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v raw_capacity));
      SZ.fits_lte (SZ.v vi + SZ.v consumed_len) (SZ.v raw_capacity);
      let src_idx = vi `SZ.add` consumed_len;
      assert (pure (SZ.v src_idx < SZ.v raw_capacity));
      with raw_before_read.
        assert (pts_to raw raw_before_read);
      assert (pure (B.length raw_before_read == SZ.v raw_capacity));
      let b = raw.(src_idx);
      assert (pure (SZ.v vi < SZ.v raw_capacity));
      raw.(vi) <- b;
      with raw_after_write.
        assert (pts_to raw raw_after_write);
      assert (pure (B.length raw_after_write == SZ.v raw_capacity));
      assert (pure (SZ.v vi + 1 <= SZ.v new_len));
      SZ.fits_lte (SZ.v vi + 1) (SZ.v new_len);
      let next_i = vi `SZ.add` 1sz;
      R.write i next_i;
    };
    with raw_done.
      assert (pts_to raw raw_done);
    assert (pure (B.length raw_done == SZ.v raw_capacity));
    new_len
  }
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
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.buffered_network_read.network_read_prefix) ==
                   SZ.v result.buffered_network_read.network_read_len /\
                 result.buffered_network_read.network_read_len == buffered_len /\
                 SZ.v result.buffered_network_new_len <= SZ.v buffered_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
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
                 CT.StepOk ==>
                 SZ.v result.buffered_network_read.network_read_written <=
                 SZ.v result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len) /\
                 (result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk \/
                 result.buffered_network_read.network_read_written == 0sz))
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
  with st1 raw_bytes network_out_bytes app_out_bytes.
    assert (driver_exactly d st1 **
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
  assert (pure (SZ.v read_result.network_read_buffer_resp.CT.consumed_len <=
    B.length (Ghost.reveal read_result.network_read_prefix)));
  assert (pure (SZ.v read_result.network_read_buffer_resp.CT.consumed_len <=
    SZ.v buffered_len));
  let step_ok =
    read_result.network_read_buffer_resp.CT.response.CT.status = CT.StepOk;
  if step_ok {
    let consumed_nonzero =
      read_result.network_read_buffer_resp.CT.consumed_len = 0sz;
    if consumed_nonzero {
      assert (pure (SZ.v buffered_len <= SZ.v buffered_len));
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
      {
        buffered_network_read = read_result;
        buffered_network_new_len = new_len;
      }
    }
  } else {
    assert (pure (SZ.v buffered_len <= SZ.v buffered_len));
    {
      buffered_network_read = read_result;
      buffered_network_new_len = buffered_len;
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
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
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
                  app_out_bytes)
{
  unfold (driver_exactly d 'st0);
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
  let read_len = IO.read d.driver_channel raw_tail_array available;
  with raw_tail_after.
    assert (IO.is_channel d.driver_channel **
            pts_to raw_tail_array raw_tail_after);
  assert (pure (B.length raw_tail_after == SZ.v available));
  assert (pure (SZ.v read_len <= SZ.v available));
  A.to_mask raw_tail_array;
  with raw_tail_mask_after.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True));
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
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(SZ.v buffered_len <= i /\ i < SZ.v raw_capacity)) \/
     (SZ.v buffered_len <= i /\ i < SZ.v raw_capacity /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  A.from_mask raw;
  with raw_after_read.
    assert (pts_to raw raw_after_read);
  assert (pure (B.length raw_after_read == SZ.v raw_capacity));
  assert (pure (SZ.v buffered_len + SZ.v read_len <= SZ.v raw_capacity));
  SZ.fits_lte (SZ.v buffered_len + SZ.v read_len) (SZ.v raw_capacity);
  let total_len = buffered_len `SZ.add` read_len;
  assert (pure (SZ.v total_len == SZ.v buffered_len + SZ.v read_len));
  assert (pure (SZ.v total_len <= SZ.v raw_capacity));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0);
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
  with st1 raw_bytes network_out_bytes app_out_bytes.
    assert (driver_exactly d st1 **
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
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_loop_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
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
    {
      buffered_network_loop_last = no_op;
      buffered_network_loop_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let empty_buffer = buffered_len = 0sz;
    if empty_buffer {
      {
        buffered_network_loop_last = no_op;
        buffered_network_loop_exhausted = false;
      }
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
      with st1 raw_bytes network_out_bytes app_out_bytes.
        assert (driver_exactly d st1 **
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
                  result.ready_local_written == 0sz) /\
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
                  result.ready_local_written == 0sz) /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
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

fn driver_progress_buffered_network_step
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_buffered.buffered_network_new_len <=
                  SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len)
{
  let empty_buffer = buffered_len = 0sz;
  if empty_buffer {
    driver_read_buffered_network_bytes_compact_once
      d
      raw
      raw_capacity
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len
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
    with st1 raw_bytes network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 **
              pts_to raw raw_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (B.length raw_bytes == SZ.v raw_capacity));
    assert (pure (SZ.v processed.buffered_network_new_len <= SZ.v buffered_len));
    assert (pure (SZ.v processed.buffered_network_new_len <= SZ.v raw_capacity));
    let need_more =
      processed.buffered_network_read.network_read_buffer_resp.CT.response.CT.status =
      CT.NeedMoreInput;
    if need_more {
      driver_read_buffered_network_bytes_compact_once
        d
        raw
        raw_capacity
        processed.buffered_network_new_len
        network_out
        network_out_len
        app_out
        app_out_len
    } else {
      {
        buffered_network_io_read_len = 0sz;
        buffered_network_io_buffered = processed;
      }
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
  requires top_driver_exactly d 'st0 **
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
           top_driver_exactly d st1 **
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
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz))
{
  unfold (top_driver_exactly d 'st0);
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
    assert (driver_exactly d.top_driver_core st1 **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  if step.ready_local_processed {
    fold (top_driver_exactly d st1);
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
          assert (driver_exactly d.top_driver_core st1 **
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
              assert (driver_exactly d.top_driver_core st2 **
                      pts_to auth_payload_prefix auth_payload_prefix_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
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
            fold (top_driver_exactly d st2);
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
            fold (top_driver_exactly d st1);
            step
          }
        } else {
          fold (top_driver_exactly d st1);
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
            assert (driver_exactly d.top_driver_core st1 **
                    pts_to auth_cv_input auth_cv_input_bytes);
          let signature_snapshot =
            driver_copy_certificate_verify_signature
              d.top_driver_core
              auth_signature
              auth_signature_len;
          with auth_signature_bytes.
            assert (driver_exactly d.top_driver_core st1 **
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
              assert (driver_exactly d.top_driver_core st2 **
                      pts_to empty_payload 'empty_payload_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            fold (top_driver_exactly d st2);
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            fold (top_driver_exactly d st1);
            step
          }
        } else {
          fold (top_driver_exactly d st1);
          step
        }
      }
    } else {
      fold (top_driver_exactly d st1);
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
  requires top_driver_exactly d 'st0 **
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
  ensures exists* st1 raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 **
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
    unfold (top_driver_exactly d 'st0);
    let snapshot = driver_control_snapshot d.top_driver_core;
    with st_snapshot.
      assert (driver_exactly d.top_driver_core st_snapshot);
    fold (top_driver_exactly d st_snapshot);
    let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
    if app_ready {
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
          assert (top_driver_exactly d st_local **
                  pts_to network_out network_out_local **
                  pts_to auth_leaf_der auth_leaf_der_local **
                  pts_to auth_payload auth_payload_local **
                  pts_to auth_cv_input auth_cv_input_local **
                  pts_to auth_signature auth_signature_local **
                  pts_to app_out app_out_local);
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
            unfold (top_driver_exactly d st_local);
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
            with st_network raw_network network_out_network app_out_network.
              assert (driver_exactly d.top_driver_core st_network **
                      pts_to raw raw_network **
                      pts_to network_out network_out_network **
                      pts_to app_out app_out_network);
            fold (top_driver_exactly d st_network);
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
              {
                driver_workflow_status = DriverWorkflowStepFailed;
                driver_workflow_rx_len =
                  network.buffered_network_io_buffered.buffered_network_new_len;
                driver_workflow_local = {
                  driver_drain_last = local;
                  driver_drain_exhausted = false;
                };
                driver_workflow_network = network;
              }
            } else {
              let next_fuel = SZ.sub fuel 1sz;
              assert (pure (SZ.v next_fuel < SZ.v fuel));
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

fn rec driver_receive_application_data
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
  requires top_driver_exactly d 'st0 **
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
  ensures exists* st1 raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 **
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
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len)
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
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
    unfold (top_driver_exactly d 'st0);
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
    with st_network raw_network network_out_network app_out_network.
      assert (driver_exactly d.top_driver_core st_network **
              pts_to raw raw_network **
              pts_to network_out network_out_network **
              pts_to app_out app_out_network);
    fold (top_driver_exactly d st_network);
    let no_op_resp = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.NeedMoreInput;
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
      {
        driver_workflow_status = DriverWorkflowStepFailed;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
      }
    } else {
    let app_ready =
      network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len =
      0sz;
    if (app_ready = false) {
      {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
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
        assert (top_driver_exactly d st_local **
                pts_to network_out network_out_local **
                pts_to auth_leaf_der auth_leaf_der_local **
                pts_to auth_payload auth_payload_local **
                pts_to auth_cv_input auth_cv_input_local **
                pts_to auth_signature auth_signature_local **
                pts_to app_out app_out_local);
      let local_processed = local.ready_local_processed;
      let local_ready = local.ready_local_action.CT.next_local_ready;
      let local_ok = local.ready_local_resp.CT.status = CT.StepOk;
      let local_wrote_all =
        local.ready_local_written = local.ready_local_resp.CT.network_out_len;
      let local_short_write = local_processed && local_ok && (local_wrote_all = false);
      let local_failed =
        (local_processed && ((local_ok = false) || local_short_write)) ||
        ((local_processed = false) && local_ready);
      if local_failed {
        {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len =
            network.buffered_network_io_buffered.buffered_network_new_len;
          driver_workflow_local = {
            driver_drain_last = local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = network;
        }
      } else {
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        driver_receive_application_data
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

fn rec driver_await_peer_close_notify
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
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
    let snapshot = driver_control_snapshot d;
    with st_snapshot.
      assert (driver_exactly d st_snapshot);
    let closed = snapshot.CR.snapshot_control_tag = 4uy;
    if closed {
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
      let network =
        driver_progress_buffered_network_step
          d
          raw
          raw_capacity
          buffered_len
          network_out
          network_out_len
          app_out
          app_out_len;
      with st_network raw_network network_out_network app_out_network.
        assert (driver_exactly d st_network **
                pts_to raw raw_network **
                pts_to network_out network_out_network **
                pts_to app_out app_out_network);
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
        {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len =
            network.buffered_network_io_buffered.buffered_network_new_len;
          driver_workflow_local = {
            driver_drain_last = no_op_local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = network;
        }
      } else {
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        driver_await_peer_close_notify
          d
          raw
          raw_capacity
          network.buffered_network_io_buffered.buffered_network_new_len
          network_out
          network_out_len
          app_out
          app_out_len
          next_fuel
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

fn top_driver_send_application_data
  (d:top_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 **
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
           top_driver_exactly d st1 **
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
  unfold (top_driver_exactly d 'st0);
  let result =
    driver_send_application_data
      d.top_driver_core
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (driver_exactly d.top_driver_core st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  fold (top_driver_exactly d st1);
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

fn rec driver_close_workflow
  (d:top_driver)
  (wait_for_peer:bool)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           C.connection_exactly d.top_driver_core.driver_client st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len)
  decreases (SZ.v fuel)
{
  unfold (top_driver_exactly d 'st0);
  let close_result =
    driver_send_close_notify
      d.top_driver_core
      empty_payload
      network_out
      network_out_len
      app_out
      app_out_len;
  with st_after_close_notify network_out_after_close app_out_after_close.
    assert (driver_exactly d.top_driver_core st_after_close_notify **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_after_close **
            pts_to app_out app_out_after_close);
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
    ready_local_resp = close_result.local_write_resp;
    ready_local_written = close_result.local_write_written;
  };
  let close_ok = close_result.local_write_resp.CT.status = CT.StepOk;
  let close_wrote_all =
    close_result.local_write_written = close_result.local_write_resp.CT.network_out_len;
  let close_failed = (close_ok && close_wrote_all) = false;
  if close_failed {
    unfold (driver_exactly d.top_driver_core st_after_close_notify);
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    {
      driver_workflow_status = DriverWorkflowStepFailed;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else if wait_for_peer {
    let waited =
      driver_await_peer_close_notify
        d.top_driver_core
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len
        fuel;
    with st_wait raw_wait network_out_wait app_out_wait.
      assert (driver_exactly d.top_driver_core st_wait **
              pts_to raw raw_wait **
              pts_to network_out network_out_wait **
              pts_to app_out app_out_wait);
    unfold (driver_exactly d.top_driver_core st_wait);
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    let wait_ok = waited.driver_workflow_status = DriverWorkflowOk;
    if wait_ok {
      {
        driver_workflow_status = DriverWorkflowClosed;
        driver_workflow_rx_len = waited.driver_workflow_rx_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = waited.driver_workflow_network;
      }
    } else {
      {
        driver_workflow_status = waited.driver_workflow_status;
        driver_workflow_rx_len = waited.driver_workflow_rx_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = waited.driver_workflow_network;
      }
    }
  } else {
    unfold (driver_exactly d.top_driver_core st_after_close_notify);
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    {
      driver_workflow_status = DriverWorkflowClosed;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  }
}

fn driver_close (d:driver)
  requires driver_exactly d 'st0
  ensures C.connection_exactly d.driver_client 'st0
{
  unfold (driver_exactly d 'st0);
  IO.close d.driver_channel
}

inline_for_extraction
fn free_client_driver_buffers
  (d:client_driver)
  (buffered_len:SZ.t)
  requires client_driver_buffers d buffered_len
  ensures emp
{
  unfold (client_driver_buffers d buffered_len);
  with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out.
    assert (Box.pts_to d.client_driver_buffered_len buffered_len **
            V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.client_driver_raw #1.0R raw **
            V.pts_to d.client_driver_network_out #1.0R network_out **
            V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
            V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
            V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
            V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
            V.pts_to d.client_driver_app_out #1.0R app_out);
  V.free d.client_driver_empty_payload;
  V.free d.client_driver_raw;
  V.free d.client_driver_network_out;
  V.free d.client_driver_auth_leaf_der;
  V.free d.client_driver_auth_payload;
  V.free d.client_driver_auth_cv_input;
  V.free d.client_driver_auth_signature;
  V.free d.client_driver_app_out;
  Box.free d.client_driver_buffered_len;
}

inline_for_extraction
fn free_disconnected_client_driver
  (d:client_driver)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.client_driver_client 'st0 **
           O.is_auth_context d.client_driver_auth **
           Box.pts_to d.client_driver_channel no_channel **
           client_driver_buffers d buffered_len
  ensures client_driver_closed d 'st0
{
  O.auth_context_free d.client_driver_auth;
  Box.free d.client_driver_channel;
  free_client_driver_buffers d buffered_len;
  fold (client_driver_closed d 'st0);
}

inline_for_extraction
fn close_failed_connect
  (d:client_driver)
  (ch:IO.channel)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.client_driver_client 'st0 **
           O.is_auth_context d.client_driver_auth **
           IO.is_channel ch **
           Box.pts_to d.client_driver_channel no_channel **
           client_driver_buffers d buffered_len
  ensures client_driver_closed d 'st0
{
  IO.close ch;
  free_disconnected_client_driver d buffered_len;
}

fn connect
  (d:client_driver)
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_live d 'st0 **
           pts_to connect_host 'connect_host_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len)
  returns status:driver_workflow_status
  ensures exists* st1.
          pts_to connect_host 'connect_host_bytes **
          (match status with
           | DriverWorkflowOk ->
             client_driver_connected d st1
           | _ ->
             client_driver_closed d st1)
{
  unfold (client_driver_live d 'st0);
  with buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel no_channel **
            client_driver_buffers d buffered_len);
  unfold (client_driver_buffers d buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  fold (client_driver_buffers d buffered_len);
  let ch_opt = IO.connect_tcp connect_host connect_host_len port;
  match ch_opt {
    None -> {
      free_disconnected_client_driver d current_buffered_len;
      DriverWorkflowStepFailed
    }
    Some ch -> {
      unfold (client_driver_buffers d buffered_len);
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out);
      V.to_array_pts_to d.client_driver_empty_payload;
      V.to_array_pts_to d.client_driver_raw;
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_auth_leaf_der;
      V.to_array_pts_to d.client_driver_auth_payload;
      V.to_array_pts_to d.client_driver_auth_cv_input;
      V.to_array_pts_to d.client_driver_auth_signature;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = ch;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      rewrite (IO.is_channel ch) as (IO.is_channel core.driver_channel);
      fold (driver_exactly core 'st0);
      rewrite (driver_exactly core 'st0) as (driver_exactly td.top_driver_core 'st0);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0);
      let result =
        driver_handshake
          td
          (V.vec_to_array d.client_driver_empty_payload)
          (V.vec_to_array d.client_driver_raw)
          driver_rx_capacity
          current_buffered_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_auth_leaf_der)
          driver_auth_leaf_der_capacity
          (V.vec_to_array d.client_driver_auth_payload)
          (V.vec_to_array d.client_driver_auth_cv_input)
          driver_certificate_verify_input_capacity
          (V.vec_to_array d.client_driver_auth_signature)
          driver_signature_capacity
          driver_public_key_payload_capacity
          driver_server_finished_payload_len
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity
          local_fuel
          fuel;
      with st1 raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
        assert (top_driver_exactly td st1 **
                pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
                pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_leaf_der) auth_leaf_der_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_payload) auth_payload_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_cv_input) auth_cv_input_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_signature) auth_signature_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      unfold (top_driver_exactly td st1);
      rewrite (driver_exactly td.top_driver_core st1) as (driver_exactly core st1);
      unfold (driver_exactly core st1);
      V.to_vec_pts_to d.client_driver_empty_payload;
      V.to_vec_pts_to d.client_driver_raw;
      V.to_vec_pts_to d.client_driver_network_out;
      V.to_vec_pts_to d.client_driver_auth_leaf_der;
      V.to_vec_pts_to d.client_driver_auth_payload;
      V.to_vec_pts_to d.client_driver_auth_cv_input;
      V.to_vec_pts_to d.client_driver_auth_signature;
      V.to_vec_pts_to d.client_driver_app_out;
      Box.(d.client_driver_buffered_len := result.driver_workflow_rx_len);
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
      fold (client_driver_buffers d result.driver_workflow_rx_len);
      rewrite (C.connection_exactly core.driver_client st1) as
        (C.connection_exactly d.client_driver_client st1);
      rewrite (IO.is_channel core.driver_channel) as (IO.is_channel ch);
      rewrite (O.is_auth_context td.top_driver_auth) as
        (O.is_auth_context d.client_driver_auth);
      match result.driver_workflow_status {
        DriverWorkflowOk -> {
          Box.(d.client_driver_channel := Some ch);
          fold (client_driver_connected d st1);
          DriverWorkflowOk
        }
        DriverWorkflowNeedMoreInput -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowNeedMoreInput
        }
        DriverWorkflowNeedExternalAction -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowNeedExternalAction
        }
        DriverWorkflowStepFailed -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowStepFailed
        }
        DriverWorkflowExhausted -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowExhausted
        }
        DriverWorkflowClosed -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowClosed
        }
      }
    }
  }
}

fn send
  (d:client_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires client_driver_connected d 'st0 **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 CT.local_input_wf
                  'st0
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes))
  returns status:driver_workflow_status
  ensures exists* st1.
          pts_to payload 'payload_bytes **
          client_driver_connected d st1
{
  unfold (client_driver_connected d 'st0);
  with ch buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch **
            client_driver_buffers d buffered_len);
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  unfold (client_driver_buffers d buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  match current_channel {
    None -> {
      assert (pure False);
      fold (client_driver_buffers d current_buffered_len);
      fold (client_driver_connected d 'st0);
      DriverWorkflowStepFailed
    }
    Some concrete_ch -> {
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out);
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = concrete_ch;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      rewrite (IO.is_channel ch) as (IO.is_channel core.driver_channel);
      fold (driver_exactly core 'st0);
      rewrite (driver_exactly core 'st0) as (driver_exactly td.top_driver_core 'st0);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0);
      let result =
        top_driver_send_application_data
          td
          payload
          payload_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity;
      with st1 network_out_bytes app_out_bytes.
        assert (top_driver_exactly td st1 **
                pts_to payload 'payload_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      unfold (top_driver_exactly td st1);
      rewrite (driver_exactly td.top_driver_core st1) as (driver_exactly core st1);
      unfold (driver_exactly core st1);
      V.to_vec_pts_to d.client_driver_network_out;
      V.to_vec_pts_to d.client_driver_app_out;
      assert (pure (concrete_ch == ch));
      rewrite (C.connection_exactly core.driver_client st1) as
        (C.connection_exactly d.client_driver_client st1);
      rewrite (IO.is_channel core.driver_channel) as (IO.is_channel ch);
      rewrite (O.is_auth_context td.top_driver_auth) as
        (O.is_auth_context d.client_driver_auth);
      fold (client_driver_buffers d current_buffered_len);
      fold (client_driver_connected d st1);
      let ok = result.local_write_resp.CT.status = CT.StepOk;
      let wrote_all = result.local_write_written = result.local_write_resp.CT.network_out_len;
      if (ok && wrote_all) {
        DriverWorkflowOk
      } else {
        DriverWorkflowStepFailed
      }
    }
  }
}

fn receive
  (d:client_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* st1 out_bytes.
          client_driver_connected d st1 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.client_receive_len <= SZ.v out_len)
{
  unfold (client_driver_connected d 'st0);
  with ch buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch **
            client_driver_buffers d buffered_len);
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  unfold (client_driver_buffers d buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  match current_channel {
    None -> {
      assert (pure False);
      fold (client_driver_buffers d current_buffered_len);
      fold (client_driver_connected d 'st0);
      {
        client_receive_status = DriverWorkflowStepFailed;
        client_receive_len = 0sz;
      }
    }
    Some concrete_ch -> {
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out);
      V.to_array_pts_to d.client_driver_empty_payload;
      V.to_array_pts_to d.client_driver_raw;
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_auth_leaf_der;
      V.to_array_pts_to d.client_driver_auth_payload;
      V.to_array_pts_to d.client_driver_auth_cv_input;
      V.to_array_pts_to d.client_driver_auth_signature;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = concrete_ch;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      rewrite (IO.is_channel ch) as (IO.is_channel core.driver_channel);
      fold (driver_exactly core 'st0);
      rewrite (driver_exactly core 'st0) as (driver_exactly td.top_driver_core 'st0);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0);
      let workflow =
        driver_receive_application_data
          td
          (V.vec_to_array d.client_driver_empty_payload)
          (V.vec_to_array d.client_driver_raw)
          driver_rx_capacity
          current_buffered_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_auth_leaf_der)
          driver_auth_leaf_der_capacity
          (V.vec_to_array d.client_driver_auth_payload)
          (V.vec_to_array d.client_driver_auth_cv_input)
          driver_certificate_verify_input_capacity
          (V.vec_to_array d.client_driver_auth_signature)
          driver_signature_capacity
          driver_public_key_payload_capacity
          driver_server_finished_payload_len
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity
          local_fuel
          fuel;
      with st1 raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
        assert (top_driver_exactly td st1 **
                pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
                pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_leaf_der) auth_leaf_der_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_payload) auth_payload_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_cv_input) auth_cv_input_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_signature) auth_signature_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      let response =
        workflow.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response;
      let copy_len = response.CT.app_out_len;
      let app_fits = SZ.lte copy_len out_len;
      let app_src_fits = SZ.lte copy_len driver_app_out_capacity;
      let workflow_ok = workflow.driver_workflow_status = DriverWorkflowOk;
      if (workflow_ok && app_fits && app_src_fits) {
        A.pts_to_len (V.vec_to_array d.client_driver_app_out);
        A.pts_to_len out;
        assert (pure (SZ.v copy_len <= SZ.v out_len));
        assert (pure (SZ.v copy_len <= B.length app_out_bytes));
        assert (pure (A.length (V.vec_to_array d.client_driver_app_out) == B.length app_out_bytes));
        assert (pure (A.length out == SZ.v out_len));
        assert (pure (SZ.v copy_len <= A.length (V.vec_to_array d.client_driver_app_out)));
        assert (pure (SZ.v copy_len <= A.length out));
        let _ = A.memcpy_l copy_len (V.vec_to_array d.client_driver_app_out) out;
        with out_bytes.
          assert (pts_to out out_bytes);
        unfold (top_driver_exactly td st1);
        rewrite (driver_exactly td.top_driver_core st1) as (driver_exactly core st1);
        unfold (driver_exactly core st1);
        V.to_vec_pts_to d.client_driver_empty_payload;
        V.to_vec_pts_to d.client_driver_raw;
        V.to_vec_pts_to d.client_driver_network_out;
        V.to_vec_pts_to d.client_driver_auth_leaf_der;
        V.to_vec_pts_to d.client_driver_auth_payload;
        V.to_vec_pts_to d.client_driver_auth_cv_input;
        V.to_vec_pts_to d.client_driver_auth_signature;
        V.to_vec_pts_to d.client_driver_app_out;
        Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
        assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
        assert (pure (concrete_ch == ch));
        rewrite (C.connection_exactly core.driver_client st1) as
          (C.connection_exactly d.client_driver_client st1);
        rewrite (IO.is_channel core.driver_channel) as (IO.is_channel ch);
        rewrite (O.is_auth_context td.top_driver_auth) as
          (O.is_auth_context d.client_driver_auth);
        fold (client_driver_buffers d workflow.driver_workflow_rx_len);
        fold (client_driver_connected d st1);
        {
          client_receive_status = DriverWorkflowOk;
          client_receive_len = copy_len;
        }
      } else {
        unfold (top_driver_exactly td st1);
        rewrite (driver_exactly td.top_driver_core st1) as (driver_exactly core st1);
        unfold (driver_exactly core st1);
        V.to_vec_pts_to d.client_driver_empty_payload;
        V.to_vec_pts_to d.client_driver_raw;
        V.to_vec_pts_to d.client_driver_network_out;
        V.to_vec_pts_to d.client_driver_auth_leaf_der;
        V.to_vec_pts_to d.client_driver_auth_payload;
        V.to_vec_pts_to d.client_driver_auth_cv_input;
        V.to_vec_pts_to d.client_driver_auth_signature;
        V.to_vec_pts_to d.client_driver_app_out;
        Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
        assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
        assert (pure (concrete_ch == ch));
        rewrite (C.connection_exactly core.driver_client st1) as
          (C.connection_exactly d.client_driver_client st1);
        rewrite (IO.is_channel core.driver_channel) as (IO.is_channel ch);
        rewrite (O.is_auth_context td.top_driver_auth) as
          (O.is_auth_context d.client_driver_auth);
        fold (client_driver_buffers d workflow.driver_workflow_rx_len);
        fold (client_driver_connected d st1);
        {
          client_receive_status =
            if workflow_ok then DriverWorkflowStepFailed else workflow.driver_workflow_status;
          client_receive_len = 0sz;
        }
      }
    }
  }
}

fn close
  (d:client_driver)
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0
  returns status:driver_workflow_status
  ensures exists* st1.
          client_driver_closed d st1
{
  unfold (client_driver_connected d 'st0);
  with ch buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch **
            client_driver_buffers d buffered_len);
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (concrete_ch == ch));
  unfold (client_driver_buffers d buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out.
    assert (Box.pts_to d.client_driver_buffered_len buffered_len **
            V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.client_driver_raw #1.0R raw **
            V.pts_to d.client_driver_network_out #1.0R network_out **
            V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
            V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
            V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
            V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
            V.pts_to d.client_driver_app_out #1.0R app_out);
  V.to_array_pts_to d.client_driver_empty_payload;
  V.to_array_pts_to d.client_driver_raw;
  V.to_array_pts_to d.client_driver_network_out;
  V.to_array_pts_to d.client_driver_app_out;
  let core = {
    driver_client = d.client_driver_client;
    driver_channel = concrete_ch;
  };
  let td = {
    top_driver_core = core;
    top_driver_auth = d.client_driver_auth;
  };
  rewrite (C.connection_exactly d.client_driver_client 'st0) as
    (C.connection_exactly core.driver_client 'st0);
  rewrite (IO.is_channel ch) as (IO.is_channel core.driver_channel);
  fold (driver_exactly core 'st0);
  rewrite (driver_exactly core 'st0) as (driver_exactly td.top_driver_core 'st0);
  rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
  fold (top_driver_exactly td 'st0);
  let workflow =
    driver_close_workflow
      td
      wait_for_peer
      (V.vec_to_array d.client_driver_empty_payload)
      (V.vec_to_array d.client_driver_raw)
      driver_rx_capacity
      current_buffered_len
      (V.vec_to_array d.client_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.client_driver_app_out)
      driver_app_out_capacity
      fuel;
  with st1 raw_bytes network_out_bytes app_out_bytes.
    assert (C.connection_exactly td.top_driver_core.driver_client st1 **
            pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
            pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
            pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
            pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
  rewrite (C.connection_exactly td.top_driver_core.driver_client st1) as
    (C.connection_exactly d.client_driver_client st1);
  V.to_vec_pts_to d.client_driver_empty_payload;
  V.to_vec_pts_to d.client_driver_raw;
  V.to_vec_pts_to d.client_driver_network_out;
  V.to_vec_pts_to d.client_driver_app_out;
  Box.(d.client_driver_channel := no_channel);
  Box.free d.client_driver_channel;
  Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
  assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
  fold (client_driver_buffers d workflow.driver_workflow_rx_len);
  free_client_driver_buffers d workflow.driver_workflow_rx_len;
  fold (client_driver_closed d st1);
  workflow.driver_workflow_status
}
