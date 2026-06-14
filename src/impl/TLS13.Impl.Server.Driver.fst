module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module IM = TLS13.Impl.Messages
module IO = TLS13.IO
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

let driver_network_out_capacity : SZ.t = SZ.uint_to_t 20000
let driver_app_out_capacity : SZ.t = SZ.uint_to_t 16640
let driver_rx_capacity : SZ.t = SZ.uint_to_t 65535
let driver_material_capacity : SZ.t = 64sz
let driver_certificate_verify_input_capacity : SZ.t = SZ.uint_to_t 256
let driver_signature_capacity : SZ.t = SZ.uint_to_t 4096

let no_channel : option IO.channel = None

noeq type server_driver = {
  server_driver_server: S.server;
  server_driver_credentials: O.server_credentials;
  server_driver_channel: Box.box (option IO.channel);
  server_driver_buffered_len: Box.box SZ.t;
  server_driver_empty_payload: V.vec U8.t;
  server_driver_raw: V.vec U8.t;
  server_driver_network_out: V.vec U8.t;
  server_driver_material_payload: V.vec U8.t;
  server_driver_certificate_verify_input: V.vec U8.t;
  server_driver_signature: V.vec U8.t;
  server_driver_app_out: V.vec U8.t;
}

noextract
let logged_received_bytes_accounted
  (logged:B.bytes)
  (consumed:B.bytes)
  : prop =
  B.length logged <= B.length consumed /\
  (forall b. SeqP.count b logged <= SeqP.count b consumed)

noextract
let server_driver_wire_logs_match_witness
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  B.length buffered == SZ.v buffered_len /\
  Seq.equal (B.append consumed buffered) received /\
  logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed

noextract
let server_driver_wire_logs_match
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop =
  exists consumed.
    server_driver_wire_logs_match_witness
      st
      received
      sent
      consumed
      buffered
      buffered_len

noextract
let server_driver_buffers
  (d:server_driver)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  Box.pts_to d.server_driver_buffered_len buffered_len **
  exists* empty_payload raw network_out material cv_input signature app_out.
    V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.server_driver_raw #1.0R raw **
    V.pts_to d.server_driver_network_out #1.0R network_out **
    V.pts_to d.server_driver_material_payload #1.0R material **
    V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
    V.pts_to d.server_driver_signature #1.0R signature **
    V.pts_to d.server_driver_app_out #1.0R app_out **
    pure (
      B.length empty_payload == 0 /\
      B.length raw == SZ.v driver_rx_capacity /\
      B.length buffered == SZ.v buffered_len /\
      SZ.v buffered_len <= SZ.v driver_rx_capacity /\
      Seq.equal buffered (Seq.slice raw 0 (SZ.v buffered_len)) /\
      B.length network_out == SZ.v driver_network_out_capacity /\
      B.length material == SZ.v driver_material_capacity /\
      B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
      B.length signature == SZ.v driver_signature_capacity /\
      B.length app_out == SZ.v driver_app_out_capacity /\
      Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity /\
      IM.max_signature_len <= SZ.v driver_signature_capacity /\
      IM.max_record_fragment_len <= SZ.v driver_app_out_capacity /\
      V.is_full_vec d.server_driver_empty_payload /\
      V.is_full_vec d.server_driver_raw /\
      V.is_full_vec d.server_driver_network_out /\
      V.is_full_vec d.server_driver_material_payload /\
      V.is_full_vec d.server_driver_certificate_verify_input /\
      V.is_full_vec d.server_driver_signature /\
      V.is_full_vec d.server_driver_app_out)

noextract
let server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  Box.pts_to d.server_driver_channel no_channel **
  server_driver_buffers d B.empty 0sz **
  pure (ST.server_end_to_end_invariant st /\
        server_driver_wire_logs_match st B.empty B.empty B.empty 0sz)

noextract
let server_driver_connected
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  exists* ch buffered buffered_len.
    Box.pts_to d.server_driver_channel (Some ch) **
    IO.is_channel ch received sent **
    server_driver_buffers d buffered buffered_len **
    pure (ST.server_end_to_end_invariant st /\
          server_driver_wire_logs_match st received sent buffered buffered_len)

noextract
let server_driver_closed
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop =
  S.connection_exactly d.server_driver_server st **
  O.is_server_credentials
    d.server_driver_credentials
    certificate_chain
    credential_identity **
  Box.pts_to d.server_driver_channel no_channel **
  exists* buffered buffered_len.
    server_driver_buffers d buffered buffered_len **
    pure (ST.server_end_to_end_invariant st)

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity))
           | None ->
             emp)
{
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      None
    }
    Some creds -> {
      with credential_identity. assert (
        O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let erased_identity : erased CS.server_credential_identity =
        Ghost.hide credential_identity;
      let s =
        S.new_server_erased_credential_identity
          certificate_chain
          certificate_chain_len
          #erased_identity;
      assert (pure (Ghost.reveal erased_identity == credential_identity));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            (Ghost.reveal erased_identity)))
        as
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy driver_rx_capacity;
      let network_out = V.alloc 0uy driver_network_out_capacity;
      let material_payload = V.alloc 0uy driver_material_capacity;
      let cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
      let signature = V.alloc 0uy driver_signature_capacity;
      let app_out = V.alloc 0uy driver_app_out_capacity;
      assert (pure (Bounds.max_certificate_verify_input_len <=
        SZ.v driver_certificate_verify_input_capacity));
      assert (pure (IM.max_signature_len <= SZ.v driver_signature_capacity));
      assert (pure (IM.max_record_fragment_len <= SZ.v driver_app_out_capacity));
      let d = {
        server_driver_server = s;
        server_driver_credentials = creds;
        server_driver_channel = channel;
        server_driver_buffered_len = buffered_len;
        server_driver_empty_payload = empty_payload;
        server_driver_raw = raw;
        server_driver_network_out = network_out;
        server_driver_material_payload = material_payload;
        server_driver_certificate_verify_input = cv_input;
        server_driver_signature = signature;
        server_driver_app_out = app_out;
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.server_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.server_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.server_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.server_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy))
        as
        (V.pts_to d.server_driver_material_payload #1.0R (Seq.create (SZ.v driver_material_capacity) 0uy));
      rewrite
        (V.pts_to cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.server_driver_certificate_verify_input #1.0R
          (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.server_driver_signature #1.0R
          (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_app_out #1.0R
          (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (S.connection_exactly
          d.server_driver_server
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        as
        (O.is_server_credentials
          d.server_driver_credentials
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      fold (server_driver_buffers d B.empty 0sz);
      fold (server_driver_live
        d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
      Some d
    }
  }
}

fn accept_transport_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns status:server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerDriverTransportOk ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  unfold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
  let listener_opt = IO.listen_tcp bind_host bind_host_len port;
  match listener_opt {
    None -> {
      fold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
      ServerDriverListenFailed
    }
    Some listener -> {
      let ch_opt = IO.accept_tcp listener;
      match ch_opt {
        None -> {
          IO.close_listener listener;
          fold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
          ServerDriverAcceptFailed
        }
        Some ch -> {
          IO.close_listener listener;
          Box.(d.server_driver_channel := Some ch);
          fold (server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            B.empty
            B.empty);
          ServerDriverTransportOk
        }
      }
    }
  }
}

fn close_transport_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  IO.close concrete_ch;
  Box.(d.server_driver_channel := no_channel);
  fold (server_driver_closed d 'st0 'certificate_chain 'credential_identity);
}

fn start_server_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pure (CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures server_driver_connected
            d
            (CM.started_server_state 'st0)
            'certificate_chain
            'credential_identity
            'received
            'sent
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));

  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  assert (pure (Seq.equal empty_payload B.empty));
  V.to_array_pts_to d.server_driver_empty_payload;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;

  rewrite (S.connection_exactly d.server_driver_server 'st0) as
    (SSetup.connection_exactly d.server_driver_server 'st0);
  let resp =
    SSetup.process_start_server_local_event
      d.server_driver_server
      ST.LocalStartServer
      (V.vec_to_array d.server_driver_empty_payload)
      0sz
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      SSetup.connection_exactly d.server_driver_server st1 **
      pts_to (V.vec_to_array d.server_driver_empty_payload) empty_payload **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  rewrite (SSetup.connection_exactly d.server_driver_server st1) as
    (S.connection_exactly d.server_driver_server st1);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    ST.LocalStartServer
    empty_payload
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  assert (pure (st1 == CM.started_server_state 'st0));
  rewrite (S.connection_exactly d.server_driver_server st1) as
    (S.connection_exactly
      d.server_driver_server
      (CM.started_server_state 'st0));
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_sent;
  CL.lemma_append_empty_right 'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (Seq.equal 'sent (CM.started_server_state 'st0).CS.cs_wire_log.CL.raw_sent));
  assert (pure (server_driver_wire_logs_match
    (CM.started_server_state 'st0)
    'received
    'sent
    buffered
    buffered_len));

  V.to_vec_pts_to d.server_driver_empty_payload;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    (CM.started_server_state 'st0)
    'certificate_chain
    'credential_identity
    'received
    'sent);
  resp
}

fn start_server_if_ready
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed ->
             server_driver_connected
               d
               (CM.started_server_state 'st0)
               'certificate_chain
               'credential_identity
               'received
               'sent
           | _ ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (ST.server_state_correct 'st0));
  let action = S.next_local_action d.server_driver_server;
  assert (pure (ST.next_local_action_sound 'st0 action));
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  if action.ST.next_local_ready {
    assert (pure (action.ST.next_local_ready == true));
    if (action.ST.next_local_kind = ST.LocalStartServer) {
      assert (pure (action.ST.next_local_kind == ST.LocalStartServer));
      assert (pure (CM.can_start_server 'st0));
      let _ = start_server_once d;
      ServerDriverLocalProcessed
    } else {
      ServerDriverLocalExternalOrUnsupported
    }
  } else {
    ServerDriverLocalNotReady
  }
}
