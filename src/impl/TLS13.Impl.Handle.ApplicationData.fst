module TLS13.Impl.Handle.ApplicationData

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CF = TLS13.Impl.ConnectionState.Fail
module CN = TLS13.Impl.ConnectionState.Network
module CQ = TLS13.Impl.ConnectionState.Queries
module CM = TLS13.Impl.ConnectionState.Model
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec

fn handle_unexpected_application_input
  (c:CR.connection_state)
  (content_type:U8.t)
  (lapp:L.application_data)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           (exists* m.
             L.is_valid_tls_message (L.LTlsApplicationData lapp) m **
             pure (CT.wire_parse_success content_type (Ghost.reveal 'fragment_bytes) m)) **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns resp: CT.client_response
  ensures CR.connection_exactly c (CM.local_fail_state 'st0 CM.tls_unexpected_message_error) **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (resp.CT.status == CT.IllegalTransition /\
                B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                CT.legal_network_response
                  'st0
                  (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out /\
                CT.some_legal_response
                  'st0
                  (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
                  resp
                  'old_network_out
                  'old_app_out /\
                (resp.CT.status == CT.NeedMoreInput ==> False))
{
  with m. assert (pure True);
  L.free_tls_message (L.LTlsApplicationData lapp);
  CF.mark_unexpected_message c;
  let resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.IllegalTransition;
  };
  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
  assert (pure (CT.unexpected_message_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    'old_network_out
    'old_app_out));
  CT.lemma_legal_network_response_unexpected_from_parse_success
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    content_type
    (Ghost.reveal 'fragment_bytes)
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out;
  assert (pure (CT.some_legal_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
    resp
    'old_network_out
    'old_app_out));
  resp
}

fn handle_application_data
  (c:CR.connection_state)
  (content_type:U8.t)
  (lapp:L.application_data)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           (exists* m.
             L.is_valid_tls_message (L.LTlsApplicationData lapp) m **
             pure (CT.wire_parse_success content_type (Ghost.reveal 'fragment_bytes) m)) **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len /\
                 CT.network_input_wf
                   'st0
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   (Ghost.reveal 'raw_bytes))
  returns resp: CT.client_response
  ensures exists* st1 app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out app_out_bytes **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.legal_network_response
                  'st0
                  st1
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  app_out_bytes /\
                CT.some_legal_response
                  'st0
                  st1
                  resp
                  'old_network_out
                  app_out_bytes /\
                (resp.CT.status == CT.StepOk ==>
                  exists bytes.
                    CT.legal_received_tls_response
                      'st0
                      st1
                      resp
                      (M.TlsApplicationData bytes)
                      (Ghost.reveal 'raw_bytes)
                      'old_network_out
                      app_out_bytes /\
                    Seq.equal bytes (CT.response_app_out resp app_out_bytes)) /\
                (resp.CT.status == CT.NeedMoreInput ==> False))
{
  let ready = CQ.can_receive_application_data c;
  if ready {
        with m. assert (pure True);
        unfold (L.is_valid_tls_message (L.LTlsApplicationData lapp) m);
        with mapp. _;
        assert (pure (m == M.TlsApplicationData mapp));
        unfold (L.is_valid_application_data lapp mapp);
        with app_bytes. _;
        let data_len = lapp.L.application_data_len;
        V.pts_to_len lapp.L.application_data_bytes;
        assert (pure (B.length app_bytes == L.max_record_fragment_len));
        assert (pure (SZ.v data_len <= B.length app_bytes));
        assert (pure (SZ.v data_len <= SZ.v app_out_len));
        assert (pure (CT.wire_parse_success
          content_type
          (Ghost.reveal 'fragment_bytes)
          (M.TlsApplicationData mapp)));
        assert (pure (CT.received_tls_raw_delta_legal
          'st0
          (M.TlsApplicationData mapp)
          (Ghost.reveal 'raw_bytes)));

        V.to_array_pts_to lapp.L.application_data_bytes;
        pts_to_len (V.vec_to_array lapp.L.application_data_bytes);
        pts_to_len app_out;
        Arr.memcpy_l data_len (V.vec_to_array lapp.L.application_data_bytes) app_out;
        V.to_vec_pts_to lapp.L.application_data_bytes;
        with app_out_bytes. assert (pts_to app_out app_out_bytes);
        assert (pure (B.length app_out_bytes == SZ.v app_out_len));
        assert (pure (Seq.equal mapp (Seq.slice app_bytes 0 (SZ.v data_len))));
        assert (pure (Seq.equal (Seq.slice app_out_bytes 0 (SZ.v data_len)) (Seq.slice app_bytes 0 (SZ.v data_len))));
        assert (pure (Seq.equal mapp (Seq.slice app_out_bytes 0 (SZ.v data_len))));

        V.free lapp.L.application_data_bytes;
        CN.mark_received_application_data c raw #mapp;
        let resp = {
          CT.network_out_len = 0sz;
          CT.app_out_len = data_len;
          CT.status = CT.StepOk;
        };
        Seq.lemma_len_slice 'old_network_out 0 0;
        Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
        assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
        assert (pure (CT.response_app_out resp app_out_bytes == Seq.slice app_out_bytes 0 (SZ.v data_len)));
        assert (pure (Seq.equal mapp (CT.response_app_out resp app_out_bytes)));
        CM.lemma_received_application_data_state_evolves
          'st0
          mapp
          (Ghost.reveal 'raw_bytes);
        assert (pure (CT.legal_received_tls_response
          'st0
          (CM.received_application_data_state 'st0 mapp (Ghost.reveal 'raw_bytes))
          resp
          (M.TlsApplicationData mapp)
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          app_out_bytes));
        assert (pure (CT.legal_handled_tls_response
          'st0
          (CM.received_application_data_state 'st0 mapp (Ghost.reveal 'raw_bytes))
          resp
          (M.TlsApplicationData mapp)
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          app_out_bytes));
        CT.lemma_legal_network_response_handled_from_parse_success
          'st0
          (CM.received_application_data_state 'st0 mapp (Ghost.reveal 'raw_bytes))
          resp
          content_type
          (Ghost.reveal 'fragment_bytes)
          (M.TlsApplicationData mapp)
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          app_out_bytes;
        assert (pure (CT.some_legal_response
          'st0
          (CM.received_application_data_state 'st0 mapp (Ghost.reveal 'raw_bytes))
          resp
          'old_network_out
          app_out_bytes));
        assert (pure (resp.CT.status == CT.StepOk ==>
          exists bytes.
            CT.legal_received_tls_response
              'st0
              (CM.received_application_data_state 'st0 mapp (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsApplicationData bytes)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              app_out_bytes /\
            Seq.equal bytes (CT.response_app_out resp app_out_bytes)));
    resp
  } else {
    let resp =
      handle_unexpected_application_input
      c
      content_type
      lapp
      raw
      raw_len
      fragment
      fragment_len
      network_out
      network_out_len
      app_out
      app_out_len;
    assert (pure (resp.CT.status == CT.StepOk ==>
      exists bytes.
        CT.legal_received_tls_response
          'st0
          (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
          resp
          (M.TlsApplicationData bytes)
          (Ghost.reveal 'raw_bytes)
          'old_network_out
          'old_app_out /\
        Seq.equal bytes (CT.response_app_out resp 'old_app_out)));
    resp
  }
}
