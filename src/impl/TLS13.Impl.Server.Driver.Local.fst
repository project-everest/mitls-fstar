module TLS13.Impl.Server.Driver.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CM = TLS13.Impl.ConnectionState.Model
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module ID = FStar.IndefiniteDescription
module IM = TLS13.Impl.Messages
module IO = Common.TCP
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module RS = TLS13.Record.Spec
module S = TLS13.Impl.Server
module SSetup = TLS13.Impl.Server.Setup
module SS = TLS13.Impl.Server.Send
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Sem = TLS13.Wire.Semantics
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
            'sent **
           pure ((CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)
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
  assert (pure ((CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
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

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
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
  match ev with
  | CS.ConnNetworkEvent _ ->
    assert (st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
  | CS.ConnLocalEvent local ->
    assert (st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
#pop-options

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
        (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
        B.empty
        B.empty
        network_out
        app_out);
      lemma_legal_response_for_event_preserves_server_selection_except_select
        st0
        st1
        resp
        (CS.ConnLocalEvent (CS.LocalFail (T.AlertError T.Unexpected_message)))
        B.empty
        B.empty
        network_out
        app_out)

let lemma_server_driver_selection_present_of_some
  (st:CS.connection_state)
  : Lemma
      (requires Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
      (ensures server_driver_selection_present_when_required st)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloSent -> ()
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> ()
  | CS.ControlHandshaking CS.HsServerFinishedSent -> ()
  | CS.ControlHandshaking CS.HsClientFinishedReceived -> ()
  | CS.ControlApplicationData -> ()
  | CS.ControlClosing -> ()
  | CS.ControlClosed -> ()
  | _ -> ()

let lemma_server_driver_selection_present_from_same_selected
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
          st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection)
      (ensures server_driver_selection_present_when_required st1)
=
  assert (Some? st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  lemma_server_driver_selection_present_of_some st1

let lemma_server_local_ready_selection_facts
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.server_local_event_input_ready_with_credentials
          st kind payload certificate_chain credential_identity)
      (ensures
        (match kind with
        | ST.LocalDeriveSharedSecret ->
          Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_selection
        | ST.LocalInstallClientHandshakeTrafficKeys ->
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsServerHelloSent
        | ST.LocalInstallServerHandshakeTrafficKeys ->
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsServerHelloSent
        | ST.LocalInstallClientApplicationTrafficKeys ->
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsClientFinishedReceived
        | ST.LocalInstallServerApplicationTrafficKeys ->
          st.CS.cs_model.CS.model_control ==
            CS.ControlHandshaking CS.HsServerFinishedSent
        | ST.LocalDeliverApplicationData ->
          False
        | _ ->
          True))
=
  match kind with
  | ST.LocalDeriveSharedSecret ->
    assert (ST.server_local_event_input_ready st kind payload);
    (match st.CS.cs_model.CS.model_handshake.CS.hs_server_selection with
     | Some _ -> ()
     | None -> assert False)
  | ST.LocalInstallClientHandshakeTrafficKeys ->
    assert (ST.server_local_event_input_ready st kind payload)
  | ST.LocalInstallServerHandshakeTrafficKeys ->
    assert (ST.server_local_event_input_ready st kind payload)
  | ST.LocalInstallClientApplicationTrafficKeys ->
    assert (ST.server_local_event_input_ready st kind payload)
  | ST.LocalInstallServerApplicationTrafficKeys ->
    assert (ST.server_local_event_input_ready st kind payload)
  | ST.LocalDeliverApplicationData ->
    assert (ST.server_local_event_input_ready st kind payload);
    assert False
  | _ ->
    ()

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
        kind <> ST.LocalStartServer /\
        kind <> ST.LocalSendServerHello /\
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
  lemma_server_local_ready_selection_facts
    st0
    kind
    payload
    certificate_chain
    credential_identity;
  match kind with
  | ST.LocalStartServer ->
    assert False
  | ST.LocalSelectServerParameters ->
    assert False
  | ST.LocalDeriveSharedSecret ->
    assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    lemma_server_driver_selection_present_from_same_selected st0 st1
  | ST.LocalInstallClientHandshakeTrafficKeys ->
    assert (
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent);
    assert (server_driver_selection_present_when_required st0);
    assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    lemma_server_driver_selection_present_from_same_selected st0 st1
  | ST.LocalInstallServerHandshakeTrafficKeys ->
    assert (
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerHelloSent);
    assert (server_driver_selection_present_when_required st0);
    assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    lemma_server_driver_selection_present_from_same_selected st0 st1
  | ST.LocalInstallClientApplicationTrafficKeys ->
    assert (
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientFinishedReceived);
    assert (server_driver_selection_present_when_required st0);
    assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    lemma_server_driver_selection_present_from_same_selected st0 st1
  | ST.LocalInstallServerApplicationTrafficKeys ->
    assert (
      st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedSent);
    assert (server_driver_selection_present_when_required st0);
    assert (Some? st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    lemma_server_driver_selection_present_from_same_selected st0 st1
  | ST.LocalSignCertificateVerify ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalVerifyClientFinished ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalDeliverApplicationData ->
    assert False
  | ST.LocalSendServerHello ->
    assert False
  | ST.LocalSendEncryptedExtensions ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalSendCertificate ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalSendCertificateVerify ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalSendServerFinished ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalSendApplicationData ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalSendCloseNotify ->
    assert (server_driver_selection_present_when_required st1)
  | ST.LocalFail ->
    assert (server_driver_selection_present_when_required st1);
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
                 kind <> ST.LocalStartServer /\
                 kind <> ST.LocalSendServerHello /\
                 ST.server_local_event_input_ready_with_credentials
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal 'certificate_chain)
                   (Ghost.reveal 'credential_identity) /\
                 // TODO-A1: callee (S.process_local_event_with_credentials) requires
                 // serialize-length equations deleted by the wire-format migration.
                 (kind == ST.LocalVerifyClientFinished /\
                  Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                    Bounds.max_transcript_len /\
                  CM.can_verify_client_finished 'st0
                    (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
                 (kind == ST.LocalSendCertificateVerify /\
                  Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
                  (let cv = Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
                   B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
                     8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
                   B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                     B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
                     Bounds.max_transcript_len)) /\
                 (kind == ST.LocalSendCertificate ==>
                  1 <= B.length (Ghost.reveal 'certificate_chain) /\
                  B.length (Ghost.reveal 'certificate_chain) <= 32768 /\
                  B.length (W.serialize_handshake
                    (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                    13 + B.length (Ghost.reveal 'certificate_chain)))
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
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config)
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
  lemma_server_local_event_received_exact_when_nonfailed
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len;
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
       else B.empty)) /\
     st1.CS.cs_model.CS.model_config ==
       'st0.CS.cs_model.CS.model_config));
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
              kind <> ST.LocalSelectServerParameters /\
              kind <> ST.LocalStartServer /\
              kind <> ST.LocalSendServerHello /\
              // TODO-A1: threading callee obligations from S.process_local_event_with_credentials
              (kind == ST.LocalVerifyClientFinished /\
               Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
               B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                 Bounds.max_transcript_len /\
               CM.can_verify_client_finished 'st0
                 (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
              (kind == ST.LocalSendCertificateVerify /\
               Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
               (let cv = Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
                B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
                  8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
                B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                  B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
                  Bounds.max_transcript_len)) /\
              (kind == ST.LocalSendCertificate ==>
               1 <= B.length (Ghost.reveal 'certificate_chain) /\
               B.length (Ghost.reveal 'certificate_chain) <= 32768 /\
               B.length (W.serialize_handshake
                 (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                 13 + B.length (Ghost.reveal 'certificate_chain)))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
           server_driver_connected
             d
             st1
             'certificate_chain
             'credential_identity
             'received
             sent' **
           pure (server_driver_local_write_correct
             'st0
             st1
             resp
             kind
             B.empty
             (Ghost.reveal 'sent)
             sent' /\
             st1.CS.cs_model.CS.model_config ==
               'st0.CS.cs_model.CS.model_config)
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
  assert (pure (empty_payload_bytes == B.empty));
  assert (pure (ST.server_local_event_input_ready_with_credentials
    'st0
    kind
    empty_payload_bytes
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (kind <> ST.LocalSelectServerParameters));
  assert (pure (kind <> ST.LocalStartServer));
  assert (pure (kind <> ST.LocalSendServerHello));
  let resp =
    process_local_event_and_write_once
       d
       kind
       empty_payload
       0sz;
  with st1 sent'.
    assert (server_driver_connected
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      sent');
  assert (pure (server_driver_local_write_correct
    'st0
    st1
    resp
    kind
    empty_payload_bytes
    (Ghost.reveal 'sent)
    sent'));
  assert (pure (server_driver_local_write_correct
    'st0
    st1
    resp
    kind
    B.empty
    (Ghost.reveal 'sent)
    sent'));
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st1
    resp
    kind
    B.empty
    (Ghost.reveal 'sent)
    sent';
  resp
}

fn process_empty_local_event_exact_network_len_and_write_once
  (d:server_driver)
  (kind:ST.local_event_kind)
  (exact_network_out_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (SZ.v exact_network_out_len <= SZ.v driver_network_out_capacity /\
                 ST.server_local_event_input_ready_with_credentials
                   'st0
                   kind
                   B.empty
                   (Ghost.reveal 'certificate_chain)
                   (Ghost.reveal 'credential_identity) /\
                 kind <> ST.LocalSelectServerParameters /\
                 kind <> ST.LocalStartServer /\
                 kind <> ST.LocalSendServerHello /\
                 // TODO-A1: threading callee obligations from S.process_local_event_with_credentials
                 (kind == ST.LocalVerifyClientFinished /\
                  Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                    Bounds.max_transcript_len /\
                  CM.can_verify_client_finished 'st0
                    (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)) /\
                 (kind == ST.LocalSendCertificateVerify /\
                  Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==>
                  (let cv = Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
                   B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
                     8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
                   B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                     B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
                     Bounds.max_transcript_len)) /\
                 (kind == ST.LocalSendCertificate ==>
                  1 <= B.length (Ghost.reveal 'certificate_chain) /\
                  B.length (Ghost.reveal 'certificate_chain) <= 32768 /\
                  B.length (W.serialize_handshake
                    (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                    13 + B.length (Ghost.reveal 'certificate_chain)))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            kind
            B.empty
            (Ghost.reveal 'sent)
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config)
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
  V.to_array_pts_to d.server_driver_empty_payload;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  assert (pure (B.length empty_payload == 0));
  assert (pure (forall (i:nat{i < B.length empty_payload}).
    Seq.index empty_payload i == Seq.index B.empty i));
  Seq.lemma_eq_intro empty_payload B.empty;
  assert (pure (Seq.equal empty_payload B.empty));
  Seq.lemma_eq_elim empty_payload B.empty;
  assert (pure (B.length network_out == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out == SZ.v driver_app_out_capacity));
  A.pts_to_len (V.vec_to_array d.server_driver_network_out);
  assert (pure (A.length (V.vec_to_array d.server_driver_network_out) ==
    SZ.v driver_network_out_capacity));
  A.to_mask (V.vec_to_array d.server_driver_network_out);
  with network_out_mask.
    assert (A.pts_to_mask
      (V.vec_to_array d.server_driver_network_out)
      #1.0R
      network_out_mask
      (fun _ -> True));
  assert (pure (Seq.length network_out_mask == SZ.v driver_network_out_capacity));
  assert (pure (forall (i:nat). i < Seq.length network_out_mask ==>
    Seq.index network_out_mask i == Some (Seq.index network_out i)));
  let exact_network_out =
    A.sub
      (V.vec_to_array d.server_driver_network_out)
      #1.0R
      #(fun _ -> True)
      0sz
      (SZ.v exact_network_out_len);
  with exact_network_out_mask.
    assert (A.pts_to_mask exact_network_out #1.0R exact_network_out_mask (fun _ -> True));
  Seq.lemma_len_slice network_out_mask 0 (SZ.v exact_network_out_len);
  assert (pure (Seq.length exact_network_out_mask == SZ.v exact_network_out_len));
  assert (pure (forall (i:nat). i < Seq.length exact_network_out_mask ==>
    Some? (Seq.index exact_network_out_mask i)));
  A.from_mask exact_network_out;
  with old_exact_network_out.
    assert (pts_to exact_network_out old_exact_network_out);
  assert (pure (B.length old_exact_network_out == Seq.length exact_network_out_mask));
  assert (pure (B.length old_exact_network_out == SZ.v exact_network_out_len));
  Seq.lemma_len_slice network_out 0 (SZ.v exact_network_out_len);
  assert (pure (forall (i:nat{i < B.length old_exact_network_out}).
    Some (Seq.index old_exact_network_out i) ==
      Seq.index (Seq.slice network_out_mask 0 (SZ.v exact_network_out_len)) i));
  assert (pure (forall (i:nat{i < B.length old_exact_network_out}).
    Seq.index (Seq.slice network_out_mask 0 (SZ.v exact_network_out_len)) i ==
      Some (Seq.index network_out i)));
  assert (pure (forall (i:nat{i < B.length old_exact_network_out}).
    Seq.index old_exact_network_out i == Seq.index network_out i));
  assert (pure (forall (i:nat{i < B.length old_exact_network_out}).
    Seq.index old_exact_network_out i ==
      Seq.index (Seq.slice network_out 0 (SZ.v exact_network_out_len)) i));
  Seq.lemma_eq_intro
    old_exact_network_out
    (Seq.slice network_out 0 (SZ.v exact_network_out_len));
  assert (pure (Seq.equal old_exact_network_out
    (Seq.slice network_out 0 (SZ.v exact_network_out_len))));

  let resp =
    S.process_local_event_with_credentials
      d.server_driver_server
      d.server_driver_credentials
      kind
      (V.vec_to_array d.server_driver_empty_payload)
      0sz
      exact_network_out
      exact_network_out_len
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (
      S.connection_exactly d.server_driver_server st1 **
      O.is_server_credentials
        d.server_driver_credentials
        'certificate_chain
        'credential_identity **
      pts_to (V.vec_to_array d.server_driver_empty_payload) empty_payload **
      pts_to exact_network_out network_out_bytes **
      pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v exact_network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_local_event_end_to_end_correct
    'st0
    st1
    resp
    kind
    B.empty
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_end_to_end_invariant st1));
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    kind
    B.empty
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
      exact_network_out
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
  lemma_server_local_event_received_exact_when_nonfailed
    'st0
    st1
    resp
    kind
    B.empty
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len;
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
    B.empty
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
    B.empty
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
    B.empty
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

  A.to_mask exact_network_out;
  with exact_network_out_mask_after.
    assert (A.pts_to_mask exact_network_out #1.0R exact_network_out_mask_after (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length exact_network_out_mask_after ==>
    Some? (Seq.index exact_network_out_mask_after i)));
  assert (pure (forall (i:nat). i < Seq.length exact_network_out_mask_after ==>
    Seq.index exact_network_out_mask_after i == Some (Seq.index network_out_bytes i)));
  rewrite
    (A.pts_to_mask exact_network_out #1.0R exact_network_out_mask_after (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub (V.vec_to_array d.server_driver_network_out) 0 (SZ.v exact_network_out_len))
      #1.0R
      exact_network_out_mask_after
      (fun _ -> True));
  A.return_sub
    (V.vec_to_array d.server_driver_network_out)
    #1.0R
    #network_out_mask
    #exact_network_out_mask_after
    #(fun k -> True /\ ~(0 <= k /\ k < SZ.v exact_network_out_len))
    #(fun _ -> True)
    #0
    #(SZ.v exact_network_out_len);
  with network_out_joined_mask.
    assert (A.pts_to_mask (V.vec_to_array d.server_driver_network_out) #1.0R network_out_joined_mask
      (fun k ->
        (True /\ ~(0 <= k /\ k < SZ.v exact_network_out_len)) \/
        (0 <= k /\ k < SZ.v exact_network_out_len /\ True)));
  assert (pure (forall (i:nat). i < Seq.length network_out_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v exact_network_out_len)) \/
     (0 <= i /\ i < SZ.v exact_network_out_len /\ True))));
  assert (pure (forall (i:nat). i < Seq.length network_out_joined_mask ==>
    Seq.index network_out_joined_mask i ==
      (if 0 <= i && i < SZ.v exact_network_out_len
       then Seq.index exact_network_out_mask_after i
       else Seq.index network_out_mask i)));
  assert (pure (forall (i:nat). i < Seq.length network_out_joined_mask ==>
    Some? (Seq.index network_out_joined_mask i)));
  A.from_mask (V.vec_to_array d.server_driver_network_out);
  with joined_network_out.
    assert (pts_to (V.vec_to_array d.server_driver_network_out) joined_network_out);
  assert (pure (B.length joined_network_out == SZ.v driver_network_out_capacity));

  V.to_vec_pts_to d.server_driver_empty_payload;
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
  lemma_server_driver_local_write_correct_intro
    'st0
    st1
    resp
    kind
    B.empty
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    network_out_bytes
    app_out_bytes;
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  resp
}

fn process_send_certificate_exact_and_write_once
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
                   (Ghost.reveal 'credential_identity) /\
                 B.length (Ghost.reveal 'certificate_chain) <=
                   Bounds.max_server_certificate_chain_len /\
                 // TODO-A1: chain lower bound needed by SS.build_certificate_from_credentials
                 1 <= B.length (Ghost.reveal 'certificate_chain) /\
                 // TODO-A1: serialize-length equation (deleted lemma_serialize_certificate_from_single_chain_len)
                 B.length (W.serialize_handshake
                   (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                   13 + B.length (Ghost.reveal 'certificate_chain))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
           pure (st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)
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
  assert (pure (server_driver_config_matches_credentials
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (server_driver_supported_profile_selection
    'st0
    (Ghost.reveal 'credential_identity)));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));
  let built = SS.build_certificate_from_credentials d.server_driver_credentials;
  match built {
    None -> {
      assert_norm (IM.max_certificate_chain_bytes == 32768);
      assert_norm (Bounds.max_server_certificate_chain_len == 16610);
      assert (pure False);
      fold (server_driver_connected
        d
        'st0
        'certificate_chain
        'credential_identity
        'received
        'sent);
      process_empty_local_event_and_write_once d ST.LocalSendCertificate
    }
    Some lcert -> {
      assert (pure (SZ.v lcert.IM.certificate_msg_chain_bytes_len ==
        B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (SZ.fits (SZ.v lcert.IM.certificate_msg_chain_bytes_len + 13)));
      let fragment_len =
        SZ.add lcert.IM.certificate_msg_chain_bytes_len 13sz;
      assert (pure (SZ.v fragment_len ==
        13 + B.length (Ghost.reveal 'certificate_chain)));
      assert (pure (SZ.fits (SZ.v fragment_len + 22)));
      let expected_network_out_len = SZ.add fragment_len 22sz;
      assert (pure (SZ.v expected_network_out_len ==
        13 + B.length (Ghost.reveal 'certificate_chain) + 22));
      assert_norm (Bounds.max_server_certificate_chain_len == 16610);
      assert_norm (driver_network_out_capacity == 20000sz);
      assert (pure (SZ.v expected_network_out_len <= SZ.v driver_network_out_capacity));
      IM.free_certificate_msg lcert;
      fold (server_driver_connected
        d
        'st0
        'certificate_chain
        'credential_identity
        'received
        'sent);
      process_empty_local_event_exact_network_len_and_write_once
        d
        ST.LocalSendCertificate
        expected_network_out_len
    }
  }
}

fn process_send_certificate_verify_exact_and_write_once
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
                   ST.LocalSendCertificateVerify
                   B.empty
                   (Ghost.reveal 'certificate_chain)
                   (Ghost.reveal 'credential_identity) /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
                 // TODO-A1: serialize-length equation (deleted lemma_serialize_certificate_verify_from_signature_len)
                 // and transcript bound needed by S.process_local_event_with_credentials LSCV arm.
                 (let cv = Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
                  B.length (W.serialize_handshake (M.CertificateVerify cv)) ==
                    8 + B.length (Sem.certificateVerify_signature_bytes cv) /\
                  B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
                    B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
                    Bounds.max_transcript_len))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
           pure (st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)
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
  assert (pure (server_driver_config_matches_credentials
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (server_driver_supported_profile_selection
    'st0
    (Ghost.reveal 'credential_identity)));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));
  rewrite
    (S.connection_exactly d.server_driver_server 'st0)
    as
    (CR.connection_exactly d.server_driver_server 'st0);
  let snapshot =
    CQ.get_certificate_verify_signature_snapshot d.server_driver_server;
  rewrite
    (CR.connection_exactly d.server_driver_server 'st0)
    as
    (S.connection_exactly d.server_driver_server 'st0);
  assert (pure (SZ.v snapshot.CR.cv_signature_len <= IM.max_signature_len));
  assert_norm (IM.max_signature_len == 4096);
  assert (pure (SZ.fits (SZ.v snapshot.CR.cv_signature_len + 8)));
  let fragment_len = SZ.add snapshot.CR.cv_signature_len 8sz;
  assert (pure (SZ.v fragment_len == SZ.v snapshot.CR.cv_signature_len + 8));
  assert (pure (SZ.v fragment_len + 17 <= 16640));
  assert (pure (SZ.fits (SZ.v fragment_len + 22)));
  let expected_network_out_len = SZ.add fragment_len 22sz;
  assert (pure (SZ.v expected_network_out_len == SZ.v fragment_len + 22));
  assert_norm (driver_network_out_capacity == 20000sz);
  assert (pure (SZ.v expected_network_out_len <= SZ.v driver_network_out_capacity));
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  process_empty_local_event_exact_network_len_and_write_once
    d
    ST.LocalSendCertificateVerify
    expected_network_out_len
}

// Runtime non-emptiness check for the configured certificate chain.  The
// send helper process_send_certificate_exact_and_write_once (through
// SS.build_certificate_from_credentials / SS.mk_cert_witness) requires
// 1 <= |chain|, but no state invariant guarantees a non-empty chain, so we
// establish it at runtime here.  We copy the chain into a scratch buffer using
// O.copy_server_certificate_chain, which returns the exact chain length; a
// positive length yields 1 <= |chain|.  The None (buffer-too-small) case is
// impossible for a well-configured server (|chain| <= max_server_certificate_
// chain_len == 16610 < 32768) but is handled soundly by reporting ok = false.
fn check_certificate_chain_nonempty
  (d:server_driver)
  requires server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent
  returns ok:bool
  ensures server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent **
          pure (ok ==> 1 <= B.length (Ghost.reveal 'certificate_chain))
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
  assert_norm (IM.max_certificate_chain_bytes == 32768);
  let chain_bytes = V.alloc 0uy 32768sz;
  with old_chain_bytes. assert (V.pts_to chain_bytes old_chain_bytes);
  assert (pure (V.is_full_vec chain_bytes));
  assert (pure (B.length old_chain_bytes == 32768));
  V.to_array_pts_to chain_bytes;
  let copy_result =
    O.copy_server_certificate_chain
      d.server_driver_credentials
      (V.vec_to_array chain_bytes)
      32768sz;
  V.to_vec_pts_to chain_bytes;
  V.free chain_bytes;
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  match copy_result {
    None -> {
      false
    }
    Some written -> {
      let ok = SZ.gt written 0sz;
      ok
    }
  }
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
            | ServerDriverLocalProcessed
            | ServerDriverLocalStepFailed ->
              exists* st1 sent'.
                server_driver_connected
                  d
                  st1
                  'certificate_chain
                  'credential_identity
                  'received
                  sent' **
                pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config)
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
  assert (pure (server_driver_supported_profile_selection
    'st0
    (Ghost.reveal 'credential_identity)));
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
         let resp = start_server_once d;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
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
         let resp =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
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
         let resp =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
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
         let resp =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
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
         let resp =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
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
         let resp =
           process_empty_local_event_exact_network_len_and_write_once
             d
             action.ST.next_local_kind
             28sz;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
       }
       ST.LocalSendCertificate -> {
         // Establish the input-ready facts for the Certificate send from
         // next_local_action_sound (asserted above) plus the credential-matching
         // facts threaded through server_driver_connected / supported_profile_selection.
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         assert (pure (B.length (Ghost.reveal 'certificate_chain) <=
           Bounds.max_server_certificate_chain_len));
         // 1 <= |chain| is not carried by any invariant: check it at runtime.
         let nonempty = check_certificate_chain_nonempty d;
         if nonempty {
           assert (pure (1 <= B.length (Ghost.reveal 'certificate_chain)));
           // Serializer-length equation |serialize_handshake (Certificate
           // (mk_cert_witness chain))| == 13 + |chain|.
           SS.lemma_mk_cert_witness_bytesize (Ghost.reveal 'certificate_chain);
           assert (pure (B.length (W.serialize_handshake
             (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
             13 + B.length (Ghost.reveal 'certificate_chain)));
           let resp = process_send_certificate_exact_and_write_once d;
           if (resp.ST.status = ST.StepOk) {
             ServerDriverLocalProcessed
           } else {
             ServerDriverLocalStepFailed
           }
         } else {
           ServerDriverLocalStepFailed
         }
       }
       ST.LocalSignCertificateVerify -> {
         assert (pure (action.ST.next_local_payload == ST.LocalPayloadNone));
         assert (pure ('st0.CS.cs_model.CS.model_control ==
           CS.ControlHandshaking CS.HsServerEncryptedFlightSent));
         assert (pure ('st0.CS.cs_model.CS.model_config.CS.config_role ==
           CS.ServerEndpoint));
         assert (pure (
           'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate <> None));
         assert (pure (
           'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == None));
         assert (pure (
           'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input == None));
         assert (pure (Some?
           'st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection));
         assert (pure (ST.server_local_event_input_ready_with_credentials
           'st0
           action.ST.next_local_kind
           B.empty
           (Ghost.reveal 'certificate_chain)
           (Ghost.reveal 'credential_identity)));
         let resp =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
       }
       ST.LocalSendCertificateVerify -> {
         // input_ready facts for CertificateVerify come from next_local_action_sound
         // (asserted above); for LSCV input_ready_with_credentials == input_ready.
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
         assert (pure (Some?
           'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
         // Serializer-length equation |serialize_handshake (CertificateVerify cv)|
         // == 8 + |signature(cv)|; combined with the transcript bound restored in
         // next_local_action_sound this discharges the send helper's precondition.
         SS.lemma_serialize_handshake_certificate_verify_len
           (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
         assert (pure (
           B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript +
             B.length (W.serialize_handshake (M.CertificateVerify
               (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify))) <=
             Bounds.max_transcript_len));
         let resp = process_send_certificate_verify_exact_and_write_once d;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
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
         let resp =
           process_empty_local_event_exact_network_len_and_write_once
             d
             action.ST.next_local_kind
             58sz;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
       }
       ST.LocalVerifyClientFinished -> {
         // input_ready facts for VerifyClientFinished come from next_local_action_sound
         // (asserted above); for LVCF input_ready_with_credentials == input_ready.
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
         assert (pure (Some?
           'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished));
         // Bridge |transcript| + 36 <= max (restored in next_local_action_sound) to
         // the CM.can_verify_client_finished bound via |serialize_handshake
         // (Finished fin)| == 36.
         SS.lemma_serialize_handshake_finished_len
           (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
         assert (pure (CM.can_verify_client_finished 'st0
           (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)));
         let resp =
           process_empty_local_event_and_write_once
             d
             action.ST.next_local_kind;
         if (resp.ST.status = ST.StepOk) {
           ServerDriverLocalProcessed
         } else {
           ServerDriverLocalStepFailed
         }
       }
       _ -> {
         ServerDriverLocalUnsupported
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
             sent' **
           pure (st1.CS.cs_model.CS.model_config ==
             'st0.CS.cs_model.CS.model_config)
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    assert (pure ('st0.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
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
         assert (pure (st1.CS.cs_model.CS.model_config ==
           'st0.CS.cs_model.CS.model_config));
         let next_fuel = SZ.sub fuel 1sz;
         assert (pure (SZ.v next_fuel < SZ.v fuel));
         let result = drain_ready_empty_local_actions d next_fuel;
         with st2 sent2.
           assert (server_driver_connected
             d
             st2
             'certificate_chain
             'credential_identity
             'received
             sent2 **
           pure (st2.CS.cs_model.CS.model_config ==
             st1.CS.cs_model.CS.model_config));
         assert (pure (st2.CS.cs_model.CS.model_config ==
           'st0.CS.cs_model.CS.model_config));
         result
       }
       ServerDriverLocalStepFailed -> {
         with st1 sent'.
           assert (server_driver_connected
             d
             st1
             'certificate_chain
             'credential_identity
             'received
             sent' **
           pure (st1.CS.cs_model.CS.model_config ==
             'st0.CS.cs_model.CS.model_config));
         let result:server_driver_local_drain_result = {
          server_driver_local_drain_last = ServerDriverLocalStepFailed;
          server_driver_local_drain_exhausted = false;
         };
         result
       }
       ServerDriverLocalNotReady -> {
         assert (pure ('st0.CS.cs_model.CS.model_config ==
           'st0.CS.cs_model.CS.model_config));
         let result:server_driver_local_drain_result = {
           server_driver_local_drain_last = ServerDriverLocalNotReady;
           server_driver_local_drain_exhausted = false;
         };
         result
       }
       ServerDriverLocalUnsupported -> {
         assert (pure ('st0.CS.cs_model.CS.model_config ==
           'st0.CS.cs_model.CS.model_config));
         let result:server_driver_local_drain_result = {
           server_driver_local_drain_last = ServerDriverLocalUnsupported;
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
               sent' **
             pure (server_driver_local_write_correct
               'st0
               st1
               resp
               ST.LocalSendCloseNotify
               B.empty
               (Ghost.reveal 'sent)
               sent')
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
                (Ghost.reveal 'credential_identity) /\
                // TODO-A1: deleted lemma_serialize_certificate_from_single_chain_len.
                // The serializer-length equation |serialize_handshake (Certificate
                // (mk_cert_witness chain))| == 13 + |chain| and the chain bounds are a
                // caller obligation (recoverable from the serializer postcondition once
                // build-direction support lands).
                1 <= B.length (Ghost.reveal 'certificate_chain) /\
                B.length (Ghost.reveal 'certificate_chain) <= 32768 /\
                B.length (W.serialize_handshake
                  (M.Certificate (SS.mk_cert_witness (Ghost.reveal 'certificate_chain)))) ==
                  13 + B.length (Ghost.reveal 'certificate_chain))
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
                B.empty /\
                // TODO-A1: deleted lemma_serialize_finished_len.  The
                // CM.can_verify_client_finished transcript/serialized-Finished length
                // conjunct (transcript + 36 <= max_transcript_len together with
                // |W.serialize_handshake (M.Finished fin)| == 36) is a caller obligation
                // (recoverable from the serializer postcondition once build-direction lands).
                (Some? 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished ==>
                 B.length 'st0.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
                   Bounds.max_transcript_len /\
                 CM.can_verify_client_finished 'st0
                   (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_client_finished)))
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
