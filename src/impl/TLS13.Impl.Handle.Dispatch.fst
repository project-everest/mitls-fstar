module TLS13.Impl.Handle.Dispatch

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CF = TLS13.Impl.ConnectionState.Fail
module CN = TLS13.Impl.ConnectionState.Network
module CQ = TLS13.Impl.ConnectionState.Queries
module CM = TLS13.Impl.ConnectionState.Model
module CT = TLS13.Impl.Client.Types
module HAlert = TLS13.Impl.Handle.Alert
module HApplicationData = TLS13.Impl.Handle.ApplicationData
module HChangeCipherSpec = TLS13.Impl.Handle.ChangeCipherSpec
module HDecodeError = TLS13.Impl.Handle.DecodeError
module HHandshake = TLS13.Impl.Handle.Handshake
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

fn dispatch_network_event
  (c:CR.connection_state)
  (content_type:U8.t)
  (parsed:option L.tls_message)
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
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           (match parsed with
            | Some l ->
              (exists* m.
                L.is_valid_tls_message l m **
                pure (CT.parsed_message_wire_success_for
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  l
                  m)) **
              pure (exists ct msg.
                L.content_type_matches content_type ct /\
                WS.parse_tls_message ct 'fragment_bytes == Some msg) **
              pure (CT.parsed_message_wire_success
                content_type
                (Ghost.reveal 'fragment_bytes)
                l)
            | None ->
              pure (forall (ct:T.content_type).
                L.content_type_matches content_type ct ==>
                WS.parse_tls_message ct 'fragment_bytes == None)) **
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
  ensures exists* st1 network_out_bytes app_out_bytes.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.legal_network_response
                  'st0
                  st1
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  network_out_bytes
                  app_out_bytes /\
                CT.some_legal_response 'st0 st1 resp network_out_bytes app_out_bytes /\
                (resp.CT.status == CT.NeedMoreInput ==> False) /\
                (resp.CT.status == CT.IllegalTransition ==>
                  CT.unexpected_message_response
                    'st0
                    st1
                    resp
                    network_out_bytes
                    app_out_bytes) /\
                (SZ.v resp.CT.app_out_len > 0 ==>
                  resp.CT.status == CT.StepOk /\
                  resp.CT.network_out_len == 0sz) /\
                (resp.CT.status == CT.OutputBufferTooSmall ==> False))
{
  match parsed {
    None -> {
      let resp =
        HDecodeError.handle_decode_error
          c
          raw
          raw_len
          network_out
          network_out_len
          app_out
          app_out_len;
      CT.lemma_legal_network_response_decode_error
        'st0
        (CM.local_fail_state 'st0 CM.tls_decode_error)
        resp
        content_type
        (Ghost.reveal 'fragment_bytes)
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      assert (pure (resp.CT.status == CT.IllegalTransition ==> False));
      assert (pure (resp.CT.status == CT.OutputBufferTooSmall ==> False));
      resp
    }
    Some l -> {
      match l {
        L.LTlsHandshake lhs -> {
          with m. assert (pure True);
          let resp =
            HHandshake.handle_handshake_message
              c
              content_type
              (L.LTlsHandshake lhs)
              raw
              raw_len
              fragment
              fragment_len
              network_out
              network_out_len
              app_out
              app_out_len;
          resp
        }
        L.LTlsApplicationData lapp -> {
          let resp =
            HApplicationData.handle_application_data
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
          resp
        }
        L.LTlsAlert lalert -> {
          let resp =
            HAlert.handle_alert
              c
              content_type
              lalert
              raw
              raw_len
              fragment
              fragment_len
              network_out
              network_out_len
              app_out
              app_out_len;
          resp
        }
        L.LTlsChangeCipherSpec -> {
          assert (pure (CT.parsed_message_wire_success
            content_type
            (Ghost.reveal 'fragment_bytes)
            L.LTlsChangeCipherSpec));
          assert (pure (CT.wire_parse_success
            content_type
            (Ghost.reveal 'fragment_bytes)
            M.TlsChangeCipherSpec));
          assert (pure (CT.received_tls_raw_delta_legal
            'st0
            M.TlsChangeCipherSpec
            (Ghost.reveal 'raw_bytes)));
          let resp =
            HChangeCipherSpec.handle_change_cipher_spec
              c
              L.LTlsChangeCipherSpec
              raw
              raw_len
              network_out
              network_out_len
              app_out
              app_out_len;
          resp
        }
        L.LTlsKeyUpdate lreq -> {
          with m. assert (pure True);
          unfold (L.is_valid_tls_message (L.LTlsKeyUpdate lreq) m);
          with req. _;
          assert (pure (m == M.TlsKeyUpdate req));
          assert (pure (CT.parsed_message_wire_success_for
            content_type
            (Ghost.reveal 'fragment_bytes)
            (L.LTlsKeyUpdate lreq)
            (M.TlsKeyUpdate req)));
          assert (pure (CT.wire_parse_success
            content_type
            (Ghost.reveal 'fragment_bytes)
            (M.TlsKeyUpdate req)));
          assert (pure (CT.received_tls_raw_delta_legal
            'st0
            (M.TlsKeyUpdate req)
            (Ghost.reveal 'raw_bytes)));
          assert (pure (L.key_update_request_matches lreq req));
          let requested = lreq = 1uy;
          if requested {
            assert (pure (req == M.UpdateRequested));
          } else {
            assert (pure (requested == false));
            assert (pure (req == M.UpdateNotRequested));
          };
          let ready = CQ.can_receive_application_data c;
          if ready {
            CN.mark_received_key_update c raw requested #req;
            let resp = {
              CT.network_out_len = 0sz;
              CT.app_out_len = 0sz;
              CT.status = CT.StepOk;
            };
            Seq.lemma_len_slice 'old_network_out 0 0;
            Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
            assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
            CM.lemma_received_key_update_state_evolves
              'st0
              req
              (Ghost.reveal 'raw_bytes);
            assert (pure (CT.legal_received_tls_response
              'st0
              (CM.received_key_update_state 'st0 req (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsKeyUpdate req)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (CT.legal_handled_tls_response
              'st0
              (CM.received_key_update_state 'st0 req (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsKeyUpdate req)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            CT.lemma_legal_network_response_handled_from_parse_success
              'st0
              (CM.received_key_update_state 'st0 req (Ghost.reveal 'raw_bytes))
              resp
              content_type
              (Ghost.reveal 'fragment_bytes)
              (M.TlsKeyUpdate req)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out;
            assert (pure (CT.some_legal_response
              'st0
              (CM.received_key_update_state 'st0 req (Ghost.reveal 'raw_bytes))
              resp
              'old_network_out
              'old_app_out));
            assert (pure (resp.CT.status == CT.IllegalTransition ==> False));
            resp
          } else {
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
            assert (pure (resp.CT.status == CT.IllegalTransition ==>
              CT.unexpected_message_response
                'st0
                (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
                resp
                'old_network_out
                'old_app_out));
            resp
          }
        }
        L.LTlsIgnoredPostHandshake lignored -> {
          with m. assert (pure True);
          unfold (L.is_valid_tls_message (L.LTlsIgnoredPostHandshake lignored) m);
          with body. _;
          assert (pure (m == M.TlsIgnoredPostHandshake body));
          assert (pure (CT.parsed_message_wire_success_for
            content_type
            (Ghost.reveal 'fragment_bytes)
            (L.LTlsIgnoredPostHandshake lignored)
            (M.TlsIgnoredPostHandshake body)));
          assert (pure (CT.wire_parse_success
            content_type
            (Ghost.reveal 'fragment_bytes)
            (M.TlsIgnoredPostHandshake body)));
          assert (pure (CT.received_tls_raw_delta_legal
            'st0
            (M.TlsIgnoredPostHandshake body)
            (Ghost.reveal 'raw_bytes)));
          let ready = CQ.can_receive_application_data c;
          if ready {
            L.free_application_data lignored;
            CN.mark_received_ignored_post_handshake c raw #body;
            let resp = {
              CT.network_out_len = 0sz;
              CT.app_out_len = 0sz;
              CT.status = CT.StepOk;
            };
            Seq.lemma_len_slice 'old_network_out 0 0;
            Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
            assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
            CM.lemma_received_ignored_post_handshake_state_evolves
              'st0
              body
              (Ghost.reveal 'raw_bytes);
            assert (pure (CT.legal_received_tls_response
              'st0
              (CM.received_ignored_post_handshake_state 'st0 body (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsIgnoredPostHandshake body)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (CT.legal_handled_tls_response
              'st0
              (CM.received_ignored_post_handshake_state 'st0 body (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsIgnoredPostHandshake body)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            CT.lemma_legal_network_response_handled_from_parse_success
              'st0
              (CM.received_ignored_post_handshake_state 'st0 body (Ghost.reveal 'raw_bytes))
              resp
              content_type
              (Ghost.reveal 'fragment_bytes)
              (M.TlsIgnoredPostHandshake body)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out;
            assert (pure (CT.some_legal_response
              'st0
              (CM.received_ignored_post_handshake_state 'st0 body (Ghost.reveal 'raw_bytes))
              resp
              'old_network_out
              'old_app_out));
            assert (pure (resp.CT.status == CT.IllegalTransition ==> False));
            resp
          } else {
            L.free_application_data lignored;
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
            assert (pure (resp.CT.status == CT.IllegalTransition ==>
              CT.unexpected_message_response
                'st0
                (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
                resp
                'old_network_out
                'old_app_out));
            resp
          }
        }
      }
    }
  }
}
