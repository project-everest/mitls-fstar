module TLS13.Impl.Server.Driver.State

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.ConnectionState
module IO = TLS13.IO
module IM = TLS13.Impl.Messages
module ID = FStar.IndefiniteDescription
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module ST = TLS13.Impl.Server.Types
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

let driver_network_out_capacity : SZ.t = SZ.uint_to_t 20000
let driver_app_out_capacity : SZ.t = SZ.uint_to_t 16640
let driver_rx_capacity : SZ.t = SZ.uint_to_t 65535
let driver_material_capacity : SZ.t = 64sz
let driver_certificate_verify_input_capacity : SZ.t = SZ.uint_to_t 256
let driver_signature_capacity : SZ.t = SZ.uint_to_t 4096

let no_channel : option IO.channel = None

let lemma_logged_received_bytes_accounted_transport
  (st:CS.connection_state)
  (received:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed /\
        Seq.equal (B.append consumed buffered) received)
      (ensures
        B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
        (forall b.
          SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
          SeqP.count b received))
=
  Seq.lemma_len_append consumed buffered;
  Seq.lemma_eq_elim (B.append consumed buffered) received;
  SeqP.lemma_append_count consumed buffered

let lemma_server_driver_wire_logs_match_received_accounted
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires server_driver_wire_logs_match st received sent buffered buffered_len)
      (ensures
        B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
        (forall b.
          SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
          SeqP.count b received))
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        server_driver_wire_logs_match_witness
          st
          received
          sent
          consumed
          buffered
          buffered_len) in
  assert (server_driver_wire_logs_match_witness
    st
    received
    sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  lemma_logged_received_bytes_accounted_transport
    st
    received
    (Ghost.reveal consumed)
    buffered

let lemma_server_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures
        exists retained.
          Seq.equal received
            (B.append st.CS.cs_wire_log.CL.raw_received retained))
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        server_driver_wire_logs_match_witness
          st
          received
          sent
          consumed
          buffered
          buffered_len) in
  assert (server_driver_wire_logs_match_witness
    st
    received
    sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (Seq.equal st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed));
  assert (Seq.equal (B.append (Ghost.reveal consumed) buffered) received);
  Seq.lemma_eq_elim st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed);
  Seq.lemma_eq_elim (B.append st.CS.cs_wire_log.CL.raw_received buffered) received;
  assert (Seq.equal received (B.append st.CS.cs_wire_log.CL.raw_received buffered));
  FStar.Classical.exists_intro
    (fun retained ->
      Seq.equal received
        (B.append st.CS.cs_wire_log.CL.raw_received retained))
    buffered

let lemma_server_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures
        B.length received == B.length st.CS.cs_wire_log.CL.raw_received)
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        server_driver_wire_logs_match_witness
          st
          received
          sent
          consumed
          buffered
          buffered_len) in
  assert (server_driver_wire_logs_match_witness
    st
    received
    sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (Seq.equal st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed));
  assert (Seq.equal (B.append (Ghost.reveal consumed) buffered) received);
  Seq.lemma_len_append (Ghost.reveal consumed) buffered;
  Seq.lemma_eq_elim st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed);
  Seq.lemma_eq_elim (B.append st.CS.cs_wire_log.CL.raw_received buffered) received;
  assert (B.length buffered == 0);
  assert (B.length received == B.length st.CS.cs_wire_log.CL.raw_received)

let lemma_legal_response_network_out_len
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        SZ.v resp.ST.network_out_len <= B.length network_out /\
        B.length (ST.response_network_out resp network_out) ==
          SZ.v resp.ST.network_out_len)
=
  if SZ.v resp.ST.network_out_len <= B.length network_out then (
    Seq.lemma_len_slice network_out 0 (SZ.v resp.ST.network_out_len)
  ) else (
    assert (Seq.equal (ST.response_network_out resp network_out) raw_sent);
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.lemma_eq_elim raw_sent B.empty
  )

let lemma_legal_response_for_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + B.length raw_sent /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received + B.length raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          (B.append st0.CS.cs_wire_log.CL.raw_received raw_received))
=
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (st1.CS.cs_wire_log == {
    CL.raw_sent = B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent;
    CL.raw_received = B.append st0.CS.cs_wire_log.CL.raw_received raw_received;
  });
  Seq.lemma_len_append st0.CS.cs_wire_log.CL.raw_sent raw_sent;
  Seq.lemma_len_append st0.CS.cs_wire_log.CL.raw_received raw_received

let lemma_local_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires ST.server_local_event_end_to_end_correct
        st0 st1 resp kind payload network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + SZ.v resp.ST.network_out_len /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (ST.response_network_out resp network_out)) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received /\
        SZ.v resp.ST.network_out_len <= B.length network_out)
=
  assert (ST.legal_handled_local_response st0 st1 resp kind payload network_out app_out);
  if (exists ev raw_sent raw_received.
        ST.legal_local_response
          st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) then (
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (ST.legal_local_response
      st0 st1 resp kind payload ev raw_sent raw_received network_out app_out);
    assert (ST.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CS.event_raw_delta_legal st0.CS.cs_model ev raw_sent raw_received);
    assert (ST.local_event_kind_matches kind payload ev);
    (match ev with
     | CS.ConnLocalEvent _ ->
       assert (Seq.equal raw_received B.empty)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_direction with
        | CL.Sent ->
          assert (Seq.equal raw_received B.empty)
        | CL.Received ->
          (match kind with
           | ST.LocalSendApplicationData
           | ST.LocalSendServerHello
           | ST.LocalSendEncryptedExtensions
           | ST.LocalSendCertificate
           | ST.LocalSendCertificateVerify
           | ST.LocalSendServerFinished
           | ST.LocalSendCloseNotify ->
             assert (msg.CL.message_direction == CL.Sent);
             assert False
           | _ ->
             assert False)));
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_received B.empty;
    lemma_legal_response_network_out_len
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (Seq.equal raw_sent (ST.response_network_out resp network_out));
    Seq.lemma_eq_elim raw_sent (ST.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  ) else (
    assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
      B.empty
      B.empty
      network_out
      app_out;
    lemma_legal_response_network_out_len
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
      B.empty
      B.empty
      network_out
      app_out;
    assert (Seq.equal B.empty (ST.response_network_out resp network_out));
    Seq.lemma_eq_elim B.empty (ST.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  )

let lemma_server_local_event_received_exact_when_nonfailed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp kind payload network_out app_out /\
        server_driver_wire_logs_match_witness
          st0 received sent consumed buffered buffered_len)
      (ensures
        ST.server_connection_control_not_failed st1 ==>
          Seq.equal st1.CS.cs_wire_log.CL.raw_received consumed)
=
  if ST.server_connection_control_not_failed st1 then (
    assert (ST.legal_handled_local_response st0 st1 resp kind payload network_out app_out);
    if (exists ev raw_sent raw_received.
          ST.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) then (
      let ev =
        ID.indefinite_description_ghost
          CS.conn_event
          (fun ev -> exists raw_sent raw_received.
            ST.legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      let raw_sent =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_sent -> exists raw_received.
            ST.legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      let raw_received =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_received ->
            ST.legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      assert (ST.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out);
      ST.lemma_legal_response_for_event_nonfailed_previous
        st0
        st1
        resp
        ev
        raw_sent
        raw_received
        network_out
        app_out;
      assert (ST.server_connection_control_not_failed st0);
      assert (Seq.equal st0.CS.cs_wire_log.CL.raw_received consumed);
      lemma_local_event_wire_lengths
        st0
        st1
        resp
        kind
        payload
        network_out
        app_out;
      Seq.lemma_eq_elim st1.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received
    ) else (
      assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
      ST.lemma_unexpected_message_response_control_failed
        st0
        st1
        resp
        network_out
        app_out;
      ST.lemma_server_connection_control_not_failed_contradicts_failed
        st1
        CM.tls_unexpected_message_error
    )
  )

let lemma_logged_received_bytes_accounted_append_delta
  (old_logged:B.bytes)
  (old_consumed:B.bytes)
  (raw_delta:B.bytes)
  (consumed_delta:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted old_logged old_consumed /\
        (Seq.equal raw_delta B.empty \/ Seq.equal raw_delta consumed_delta))
      (ensures
        logged_received_bytes_accounted
          (B.append old_logged raw_delta)
          (B.append old_consumed consumed_delta))
=
  Seq.lemma_len_append old_logged raw_delta;
  Seq.lemma_len_append old_consumed consumed_delta;
  SeqP.lemma_append_count old_logged raw_delta;
  SeqP.lemma_append_count old_consumed consumed_delta;
  if Seq.equal raw_delta B.empty then (
    Seq.lemma_eq_elim raw_delta B.empty
  ) else (
    Seq.lemma_eq_elim raw_delta consumed_delta
  )

fn forget_server_driver_connected_app_out
  (d:server_driver)
  requires server_driver_connected_with_app_out
            d
            'st
            'certificate_chain
            'credential_identity
            'received
            'sent
            'app_out
  ensures server_driver_connected
            d
            'st
            'certificate_chain
            'credential_identity
            'received
            'sent
{
  unfold (server_driver_connected_with_app_out
    d
    'st
    'certificate_chain
    'credential_identity
    'received
    'sent
    'app_out);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers_with_app_out
              d
              buffered
              buffered_len
              'app_out);
  unfold (server_driver_buffers_with_app_out
    d
    buffered
    buffered_len
    'app_out);
  with empty_payload raw network_out material cv_input signature.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R 'app_out);
  fold (server_driver_buffers d buffered buffered_len);
  fold (server_driver_connected
    d
    'st
    'certificate_chain
    'credential_identity
    'received
    'sent)
}

fn expose_server_driver_connected_app_out
  (d:server_driver)
  requires server_driver_connected
            d
            'st
            'certificate_chain
            'credential_identity
            'received
            'sent
  ensures exists* app_out.
            server_driver_connected_with_app_out
              d
              'st
              'certificate_chain
              'credential_identity
              'received
              'sent
              app_out
{
  unfold (server_driver_connected
    d
    'st
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
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
  fold (server_driver_buffers_with_app_out d buffered buffered_len app_out);
  fold (server_driver_connected_with_app_out
    d
    'st
    'certificate_chain
    'credential_identity
    'received
    'sent
    app_out)
}
