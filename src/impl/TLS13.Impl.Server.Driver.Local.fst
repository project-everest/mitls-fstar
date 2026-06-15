module TLS13.Impl.Server.Driver.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module ID = FStar.IndefiniteDescription
module IO = TLS13.IO
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module RS = TLS13.Record.Spec
module S = TLS13.Impl.Server
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module W = TLS13.Wire.Spec
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module U64 = FStar.UInt64
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

let lemma_legal_response_for_event_preserves_server_selection_except_select
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_response_for_event
          st0
          st1
          resp
          ev
          raw_sent
          raw_received
          network_out
          app_out /\
        (match ev with
         | CS.ConnLocalEvent (CS.LocalSelectServerParameters _) -> False
         | _ -> True))
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
          st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
=
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model);
  assert (
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)

let lemma_legal_local_response_preserves_server_selection_except_select
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_local_response
          st0
          st1
          resp
          kind
          payload
          ev
          raw_sent
          raw_received
          network_out
          app_out /\
        kind <> ST.LocalSelectServerParameters)
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
          st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
=
  assert (ST.local_event_kind_matches kind payload ev);
  assert (match ev with
    | CS.ConnLocalEvent (CS.LocalSelectServerParameters _) -> False
    | _ -> True);
  assert (ST.legal_response_for_event
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out);
  lemma_legal_response_for_event_preserves_server_selection_except_select
    st0
    st1
    resp
    ev
    raw_sent
    raw_received
    network_out
    app_out

let lemma_legal_handled_local_response_preserves_server_selection_except_select
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.legal_handled_local_response
          st0
          st1
          resp
          kind
          payload
          network_out
          app_out /\
        kind <> ST.LocalSelectServerParameters)
      (ensures
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
          st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
=
  let goal (_:unit) =
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection in
  FStar.Classical.or_elim
    #(exists ev raw_sent raw_received.
       ST.legal_local_response
         st0
         st1
         resp
         kind
         payload
         ev
         raw_sent
         raw_received
         network_out
         app_out)
    #(ST.unexpected_message_response st0 st1 resp network_out app_out)
    #goal
    (fun h ->
      FStar.Classical.exists_elim (goal ())
        #CS.conn_event
        #(fun ev -> exists raw_sent raw_received.
          ST.legal_local_response
            st0
            st1
            resp
            kind
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out)
        h
        (fun ev ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_sent -> exists raw_received.
          ST.legal_local_response
            st0
            st1
            resp
            kind
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out)
        ()
        (fun raw_sent ->
      FStar.Classical.exists_elim (goal ())
        #B.bytes
        #(fun raw_received ->
          ST.legal_local_response
            st0
            st1
            resp
            kind
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out)
        ()
        (fun raw_received ->
          lemma_legal_local_response_preserves_server_selection_except_select
            st0
            st1
            resp
            kind
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out))))
    (fun _ ->
      assert (ST.legal_response_for_event
        st0
        st1
        resp
        (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.UnexpectedMessage)))
        B.empty
        B.empty
        network_out
        app_out);
      lemma_legal_response_for_event_preserves_server_selection_except_select
        st0
        st1
        resp
        (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.UnexpectedMessage)))
        B.empty
        B.empty
        network_out
        app_out)

let lemma_server_driver_local_write_correct_preserves_supported_profile_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        server_driver_local_write_correct st0 st1 resp kind payload sent sent' /\
        kind <> ST.LocalSelectServerParameters /\
        ST.server_local_event_input_ready_with_credentials
          st0 kind payload certificate_chain credential_identity /\
        server_driver_config_matches_credentials
          st0 certificate_chain credential_identity /\
        server_driver_supported_profile_selection st0 credential_identity)
      (ensures
        server_driver_supported_profile_selection st1 credential_identity)
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
  lemma_server_driver_local_write_correct_preserves_config
    st0
    st1
    resp
    kind
    payload
    sent
    sent';
  assert (ST.legal_handled_local_response
    st0
    st1
    resp
    kind
    payload
    network_out_bytes
    app_out_bytes);
  lemma_legal_handled_local_response_preserves_server_selection_except_select
    st0
    st1
    resp
    kind
    payload
    network_out_bytes
    app_out_bytes;
  assert (
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (server_driver_supported_profile_selection st1 credential_identity)

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
                 kind <> ST.LocalSelectServerParameters /\
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
  lemma_server_driver_local_write_correct_preserves_supported_profile_selection
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  assert (pure (server_driver_supported_profile_selection
    st1
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

fn process_empty_local_event_and_write_once
  (d:server_driver)
  (kind:ST.local_event_kind)
  requires server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent **
            pure (ST.server_local_event_input_ready_with_credentials
              'st0
              kind
              B.empty
              (Ghost.reveal 'certificate_chain)
              (Ghost.reveal 'credential_identity) /\
              kind <> ST.LocalSelectServerParameters)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
           server_driver_connected
             d
             st1
             'certificate_chain
             'credential_identity
             'received
             sent'
{
  let mut empty_payload = [| 0uy; 0sz |];
  with empty_payload_bytes.
    assert (pts_to empty_payload empty_payload_bytes);
  assert (pure (B.length empty_payload_bytes == 0));
  assert (pure (forall (i:nat{i < B.length empty_payload_bytes}).
    Seq.index empty_payload_bytes i == Seq.index B.empty i));
  Seq.lemma_eq_intro empty_payload_bytes B.empty;
  assert (pure (Seq.equal empty_payload_bytes B.empty));
  Seq.lemma_eq_elim empty_payload_bytes B.empty;
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    kind
    empty_payload_bytes
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (kind <> ST.LocalSelectServerParameters));
  let resp =
    process_local_event_and_write_once
       d
       kind
       empty_payload
       0sz;
  resp
}

fn process_ready_empty_local_action_once
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
              exists* st1 sent'.
                server_driver_connected
                  d
                  st1
                  'certificate_chain
                  'credential_identity
                  'received
                  sent'
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
    match action.ST.next_local_kind {
       ST.LocalStartServer -> {
         assert (pure (CM.can_start_server 'st0));
         let _ = start_server_once d;
         ServerDriverLocalProcessed
       }
       ST.LocalInstallServerHandshakeTrafficKeys -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalInstallClientHandshakeTrafficKeys -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalInstallServerApplicationTrafficKeys -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalInstallClientApplicationTrafficKeys -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalSendEncryptedExtensions -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalSendCertificate -> {
         assert (pure (action.ST.next_local_payload == ST.LocalPayloadNone));
         assert (pure ('st0.CS.cs_model.CS.model_control ==
           CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
         assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role ==
           CS.ServerEndpoint));
         assert (pure (
           'st0.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions <> None));
         assert (pure (
           'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate == None));
         assert (pure (
           'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der == None));
         assert (pure (Some?
           'st0.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic));
         assert (pure (U64.fits
           ('st0.CS.cs_model.CS.model_record.CS.record_write.RS.seq + 1)));
         assert (pure (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
           | Some cfg ->
             B.length cfg.CS.server_certificate_chain <=
               Bounds.max_server_certificate_chain_len /\
             B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
               B.length
                 (W.serialize_certificate_from_credential
                   { M.chain = [cfg.CS.server_certificate_chain] }) <=
                 Bounds.max_transcript_len /\
             CS.legal_event
               'st0.CS.cs_model
               (CS.ConnNetworkEvent {
                 CL.message_direction = CL.Sent;
                 CL.message_value =
                   M.TlsHandshake
                     (M.Certificate { M.chain = [cfg.CS.server_certificate_chain] });
               })
           | None -> False));
         assert (pure (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
           | Some cfg ->
             cfg.CS.server_certificate_chain ==
               Ghost.reveal 'certificate_chain /\
             cfg.CS.server_credential_identity ==
               Ghost.reveal 'credential_identity
           | None -> False));
         assert (pure (B.length (Ghost.reveal 'certificate_chain) <=
           Bounds.max_server_certificate_chain_len));
         W.lemma_serialize_certificate_from_single_chain_len
           (Ghost.reveal 'certificate_chain);
         assert (pure (13 + B.length (Ghost.reveal 'certificate_chain) + 17 <= 16640));
         assert (pure (
           B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
             13 + B.length (Ghost.reveal 'certificate_chain) <=
               Bounds.max_transcript_len));
         assert (pure (CS.legal_event
           'st0.CS.cs_model
           (CS.ConnNetworkEvent {
             CL.message_direction = CL.Sent;
             CL.message_value =
               M.TlsHandshake
                 (M.Certificate { M.chain = [Ghost.reveal 'certificate_chain] });
           })));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalSendCertificateVerify -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       ST.LocalSendServerFinished -> {
         assert (pure (ST.server_local_event_input_ready
           'st0
           action.ST.next_local_kind
           B.empty));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let _ =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         ServerDriverLocalProcessed
       }
       _ -> {
         ServerDriverLocalExternalOrUnsupported
       }
    }
  } else {
    ServerDriverLocalNotReady
  }
}

fn rec drain_ready_empty_local_actions
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns result:server_driver_local_drain_result
  ensures exists* st1 sent'.
           server_driver_connected
             d
             st1
             'certificate_chain
             'credential_identity
             'received
             sent'
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    let result:server_driver_local_drain_result = {
       server_driver_local_drain_last = ServerDriverLocalNotReady;
       server_driver_local_drain_exhausted = true;
    };
    result
  } else {
    assert (pure (0 < SZ.v fuel));
    let status = process_ready_empty_local_action_once d;
    match status {
       ServerDriverLocalProcessed -> {
         with st1 sent'.
           assert (server_driver_connected
             d
             st1
             'certificate_chain
             'credential_identity
             'received
             sent');
         let next_fuel = SZ.sub fuel 1sz;
         assert (pure (SZ.v next_fuel < SZ.v fuel));
         drain_ready_empty_local_actions d next_fuel
       }
       ServerDriverLocalNotReady -> {
         let result:server_driver_local_drain_result = {
           server_driver_local_drain_last = ServerDriverLocalNotReady;
           server_driver_local_drain_exhausted = false;
         };
         result
       }
       ServerDriverLocalExternalOrUnsupported -> {
         let result:server_driver_local_drain_result = {
           server_driver_local_drain_last = ServerDriverLocalExternalOrUnsupported;
           server_driver_local_drain_exhausted = false;
         };
         result
       }
    }
  }

}

fn send_application_data_once
    (d:server_driver)
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
                    ST.server_local_event_input_ready
                      'st0
                      ST.LocalSendApplicationData
                      (Ghost.reveal 'payload_bytes))
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
               ST.LocalSendApplicationData
               (Ghost.reveal 'payload_bytes)
               (Ghost.reveal 'sent)
               sent')
  {
    assert (pure (ST.server_local_event_input_ready_with_credentials
       'st0
       ST.LocalSendApplicationData
       (Ghost.reveal 'payload_bytes)
       (Ghost.reveal 'certificate_chain)
       (Ghost.reveal 'credential_identity)));
    process_local_event_and_write_once
       d
       ST.LocalSendApplicationData
       payload
       payload_len
  }

  fn send_close_notify_once
    (d:server_driver)
    requires server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
              pure (ST.server_local_event_input_ready
                'st0
                ST.LocalSendCloseNotify
                B.empty)
    returns resp:ST.server_response
    ensures exists* st1 sent'.
             server_driver_connected
               d
               st1
               'certificate_chain
               'credential_identity
               'received
               sent'
  {
    assert (pure (ST.server_local_event_input_ready_with_credentials
       'st0
       ST.LocalSendCloseNotify
       B.empty
       (Ghost.reveal 'certificate_chain)
       (Ghost.reveal 'credential_identity)));
    process_empty_local_event_and_write_once
       d
       ST.LocalSendCloseNotify
  }

  fn send_certificate_once
    (d:server_driver)
    requires server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
              pure (ST.server_local_event_input_ready_with_credentials
                'st0
                ST.LocalSendCertificate
                B.empty
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
               sent'
  {
    process_empty_local_event_and_write_once
       d
       ST.LocalSendCertificate
  }

  fn sign_certificate_verify_once
    (d:server_driver)
    requires server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
              pure (ST.server_local_event_input_ready_with_credentials
                'st0
                ST.LocalSignCertificateVerify
                B.empty
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
               sent'
  {
    process_empty_local_event_and_write_once
       d
       ST.LocalSignCertificateVerify
  }

  fn verify_client_finished_once
    (d:server_driver)
    requires server_driver_connected
                 d
                 'st0
                 'certificate_chain
                 'credential_identity
                 'received
                 'sent **
              pure (ST.server_local_event_input_ready
                'st0
                ST.LocalVerifyClientFinished
                B.empty)
    returns resp:ST.server_response
    ensures exists* st1 sent'.
             server_driver_connected
               d
               st1
               'certificate_chain
               'credential_identity
               'received
               sent'
  {
    assert (pure (ST.server_local_event_input_ready_with_credentials
       'st0
       ST.LocalVerifyClientFinished
       B.empty
       (Ghost.reveal 'certificate_chain)
       (Ghost.reveal 'credential_identity)));
    process_empty_local_event_and_write_once
       d
       ST.LocalVerifyClientFinished
  }
