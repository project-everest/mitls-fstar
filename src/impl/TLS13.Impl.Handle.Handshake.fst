module TLS13.Impl.Handle.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module C = TLS13.Impl.ConnectionState
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

fn handle_unexpected_handshake_input
  (c:C.connection_state)
  (content_type:U8.t)
  (l:L.tls_message)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           (exists* m. L.is_valid_tls_message l m) **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 (exists ct msg.
                   L.content_type_matches content_type ct /\
                   WS.parse_tls_message ct (Ghost.reveal 'fragment_bytes) == Some msg))
  returns resp: CT.client_response
  ensures C.connection_exactly c (C.local_fail_state 'st0 C.tls_unexpected_message_error) **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                CT.legal_network_response
                  'st0
                  (C.local_fail_state 'st0 C.tls_unexpected_message_error)
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out /\
                CT.some_legal_response
                  'st0
                  (C.local_fail_state 'st0 C.tls_unexpected_message_error)
                  resp
                  'old_network_out
                  'old_app_out)
{
  with m. assert (pure True);
  L.free_tls_message l;
  C.mark_unexpected_message c;
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
    (C.local_fail_state 'st0 C.tls_unexpected_message_error)
    resp
    'old_network_out
    'old_app_out));
  CT.lemma_legal_network_response_unexpected_from_parse_success
    'st0
    (C.local_fail_state 'st0 C.tls_unexpected_message_error)
    resp
    content_type
    (Ghost.reveal 'fragment_bytes)
    (Ghost.reveal 'raw_bytes)
    'old_network_out
    'old_app_out;
  assert (pure (CT.some_legal_response
    'st0
    (C.local_fail_state 'st0 C.tls_unexpected_message_error)
    resp
    'old_network_out
    'old_app_out));
  resp
}

fn handle_handshake_message
  (c:C.connection_state)
  (content_type:U8.t)
  (l:L.tls_message)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           (exists* m.
             L.is_valid_tls_message l m **
             pure (CT.parsed_message_wire_success_for
               content_type
               (Ghost.reveal 'fragment_bytes)
               l
               m)) **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.tls_message_is_handshake l /\
                 (exists ct msg.
                   L.content_type_matches content_type ct /\
                   WS.parse_tls_message ct (Ghost.reveal 'fragment_bytes) == Some msg) /\
                 CT.network_input_wf
                   'st0
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   (Ghost.reveal 'raw_bytes) /\
                 CT.parsed_message_wire_success
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   l)
  returns resp: CT.client_response
  ensures exists* st1.
          C.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                CT.legal_network_response
                  'st0
                  st1
                  resp
                  content_type
                  (Ghost.reveal 'fragment_bytes)
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out /\
                CT.some_legal_response
                  'st0
                  st1
                  resp
                  'old_network_out
                  'old_app_out)
{
  match l {
    L.LTlsHandshake lhs -> {
      match lhs {
        L.LHelloRetryRequest -> {
          assert (pure (CT.parsed_message_wire_success
            content_type
            (Ghost.reveal 'fragment_bytes)
            (L.LTlsHandshake L.LHelloRetryRequest)));
          assert (pure (CT.wire_parse_success
            content_type
            (Ghost.reveal 'fragment_bytes)
            (M.TlsHandshake M.HelloRetryRequest)));
          assert (pure (CT.received_tls_raw_delta_legal
            'st0
            (M.TlsHandshake M.HelloRetryRequest)
            (Ghost.reveal 'raw_bytes)));

          let waiting = C.is_waiting_server_hello c;
          if waiting {
            L.free_tls_message (L.LTlsHandshake L.LHelloRetryRequest);
            C.mark_received_hello_retry_request_rejected c raw;
            let resp = {
              CT.network_out_len = 0sz;
              CT.app_out_len = 0sz;
              CT.status = CT.ConnectionFailed;
            };
            Seq.lemma_len_slice 'old_network_out 0 0;
            Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
            assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
            C.lemma_received_hello_retry_request_rejected_state_evolves
              'st0
              (Ghost.reveal 'raw_bytes);
            assert (pure (CT.legal_received_tls_response
              'st0
              (C.received_hello_retry_request_rejected_state 'st0 (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsHandshake M.HelloRetryRequest)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            assert (pure (CT.legal_handled_tls_response
              'st0
              (C.received_hello_retry_request_rejected_state 'st0 (Ghost.reveal 'raw_bytes))
              resp
              (M.TlsHandshake M.HelloRetryRequest)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out));
            CT.lemma_legal_network_response_handled_from_parse_success
              'st0
              (C.received_hello_retry_request_rejected_state 'st0 (Ghost.reveal 'raw_bytes))
              resp
              content_type
              (Ghost.reveal 'fragment_bytes)
              (M.TlsHandshake M.HelloRetryRequest)
              (Ghost.reveal 'raw_bytes)
              'old_network_out
              'old_app_out;
            assert (pure (CT.some_legal_response
              'st0
              (C.received_hello_retry_request_rejected_state 'st0 (Ghost.reveal 'raw_bytes))
              resp
              'old_network_out
              'old_app_out));
            resp
          } else {
            handle_unexpected_handshake_input
              c
              content_type
              (L.LTlsHandshake L.LHelloRetryRequest)
              raw
              raw_len
              fragment
              fragment_len
              network_out
              network_out_len
              app_out
              app_out_len
          }
        }
        L.LClientHello lch -> {
          handle_unexpected_handshake_input
            c
            content_type
            (L.LTlsHandshake (L.LClientHello lch))
            raw
            raw_len
            fragment
            fragment_len
            network_out
            network_out_len
            app_out
            app_out_len
        }
        L.LServerHello lsh -> {
          handle_unexpected_handshake_input
            c
            content_type
            (L.LTlsHandshake (L.LServerHello lsh))
            raw
            raw_len
            fragment
            fragment_len
            network_out
            network_out_len
            app_out
            app_out_len
        }
        L.LEncryptedExtensions lee -> {
          handle_unexpected_handshake_input
            c
            content_type
            (L.LTlsHandshake (L.LEncryptedExtensions lee))
            raw
            raw_len
            fragment
            fragment_len
            network_out
            network_out_len
            app_out
            app_out_len
        }
        L.LCertificate lcert -> {
          handle_unexpected_handshake_input
            c
            content_type
            (L.LTlsHandshake (L.LCertificate lcert))
            raw
            raw_len
            fragment
            fragment_len
            network_out
            network_out_len
            app_out
            app_out_len
        }
        L.LCertificateVerify lcv -> {
          handle_unexpected_handshake_input
            c
            content_type
            (L.LTlsHandshake (L.LCertificateVerify lcv))
            raw
            raw_len
            fragment
            fragment_len
            network_out
            network_out_len
            app_out
            app_out_len
        }
        L.LFinished lfin -> {
          handle_unexpected_handshake_input
            c
            content_type
            (L.LTlsHandshake (L.LFinished lfin))
            raw
            raw_len
            fragment
            fragment_len
            network_out
            network_out_len
            app_out
            app_out_len
        }
      }
    }
    L.LTlsApplicationData lapp -> {
      handle_unexpected_handshake_input
        c
        content_type
        (L.LTlsApplicationData lapp)
        raw
        raw_len
        fragment
        fragment_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
    L.LTlsAlert lalert -> {
      handle_unexpected_handshake_input
        c
        content_type
        (L.LTlsAlert lalert)
        raw
        raw_len
        fragment
        fragment_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
    L.LTlsChangeCipherSpec -> {
      handle_unexpected_handshake_input
        c
        content_type
        L.LTlsChangeCipherSpec
        raw
        raw_len
        fragment
        fragment_len
        network_out
        network_out_len
        app_out
        app_out_len
    }
  }
}
