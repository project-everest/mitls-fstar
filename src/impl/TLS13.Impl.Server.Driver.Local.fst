module TLS13.Impl.Server.Driver.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module ID = FStar.IndefiniteDescription
module IO = TLS13.IO
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module S = TLS13.Impl.Server
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

open TLS13.Impl.Server.Driver.State

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

noextract
let server_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists network_out_bytes app_out_bytes.
    ST.server_local_event_end_to_end_correct
      st0
      st1
      resp
      kind
      payload
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append sent (ST.response_network_out resp network_out_bytes))

let lemma_server_driver_local_write_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out_bytes
          app_out_bytes /\
        Seq.equal
          sent'
          (B.append sent (ST.response_network_out resp network_out_bytes)))
      (ensures server_driver_local_write_correct
        st0 st1 resp kind payload sent sent')
=
  FStar.Classical.exists_intro
    (fun app_out_bytes' ->
      ST.server_local_event_end_to_end_correct
        st0
        st1
        resp
        kind
        payload
        network_out_bytes
        app_out_bytes' /\
      Seq.equal
        sent'
        (B.append sent (ST.response_network_out resp network_out_bytes)))
    app_out_bytes;
  FStar.Classical.exists_intro
    (fun network_out_bytes' ->
      exists app_out_bytes'.
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out_bytes'
          app_out_bytes' /\
        Seq.equal
          sent'
          (B.append sent (ST.response_network_out resp network_out_bytes')))
    network_out_bytes

let lemma_server_driver_local_write_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires server_driver_local_write_correct st0 st1 resp kind payload sent sent')
      (ensures
          st1.CS.cs_model.CS.model_config ==
            st0.CS.cs_model.CS.model_config)
=
  let network_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out_bytes -> exists app_out_bytes.
          ST.server_local_event_end_to_end_correct
            st0
            st1
            resp
            kind
            payload
            network_out_bytes
            app_out_bytes /\
          Seq.equal
            sent'
            (B.append sent (ST.response_network_out resp network_out_bytes))) in
  let app_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out_bytes ->
          ST.server_local_event_end_to_end_correct
            st0
            st1
            resp
            kind
            payload
            network_out_bytes
            app_out_bytes /\
          Seq.equal
            sent'
            (B.append sent (ST.response_network_out resp network_out_bytes))) in
  assert (ST.server_local_event_end_to_end_correct
    st0
    st1
    resp
    kind
    payload
    network_out_bytes
    app_out_bytes);
  ST.lemma_server_local_event_preserves_config
    st0
    st1
    resp
    kind
    payload
    network_out_bytes
    app_out_bytes

fn process_local_event_and_write_once
  (d:server_driver)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 ST.server_local_event_input_ready_with_credentials
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal 'certificate_chain)
                   (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            kind
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent')
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
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;

  let resp =
    S.process_local_event_with_credentials
      d.server_driver_server
      d.server_driver_credentials
      kind
      payload
      payload_len
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      O.is_server_credentials
        d.server_driver_credentials
        'certificate_chain
        'credential_identity **
      pts_to payload 'payload_bytes **
      pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (SZ.v resp.ST.network_out_len <= B.length network_out_bytes));

  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  let written =
    IO.write
      concrete_ch
      (V.vec_to_array d.server_driver_network_out)
      resp.ST.network_out_len;
  assert (pure (written == resp.ST.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  rewrite
    (IO.is_channel
      concrete_ch
      'received
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)))
    as
    (IO.is_channel
      ch
      'received
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (ST.response_network_out resp network_out_bytes)));
  let old_consumed =
    Ghost.hide (ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        server_driver_wire_logs_match_witness
          'st0
          (Ghost.reveal 'received)
          (Ghost.reveal 'sent)
          consumed
          buffered
          buffered_len));
  assert (pure (server_driver_wire_logs_match_witness
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));
  assert (pure (Seq.equal
    (Ghost.reveal 'sent)
    'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim
    (Ghost.reveal 'sent)
    'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (ST.response_network_out resp network_out_bytes))));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received;
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    st1.CS.cs_wire_log.CL.raw_sent));
  assert (pure (server_driver_wire_logs_match_witness
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));
  assert (pure (server_driver_wire_logs_match
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    buffered
    buffered_len));
  lemma_server_driver_local_write_correct_intro
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    network_out_bytes
    app_out_bytes;
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  assert (pure (server_driver_config_matches_credentials
    st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));

  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty)));
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append
      (Ghost.reveal 'sent)
      (ST.response_network_out resp network_out_bytes))));
  assert (pure (
    ST.server_local_event_end_to_end_correct
      'st0
      st1
      resp
      kind
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty))
      (B.append
        (Ghost.reveal 'sent)
        (ST.response_network_out resp network_out_bytes))));
  lemma_server_driver_local_write_correct_intro
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    network_out_bytes
    app_out_bytes;
  assert (pure (server_driver_local_write_correct
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))));
  resp
}
