module TLS13.Impl.Handle.Dispatch

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.ConnectionState
module CT = TLS13.Impl.Client.Types
module HAlert = TLS13.Impl.Handle.Alert
module HApplicationData = TLS13.Impl.Handle.ApplicationData
module HChangeCipherSpec = TLS13.Impl.Handle.ChangeCipherSpec
module HDecodeError = TLS13.Impl.Handle.DecodeError
module HHandshake = TLS13.Impl.Handle.Handshake
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

fn dispatch_network_event
  (c:C.connection_state)
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
  requires C.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           (match parsed with
            | Some l ->
              (exists* ct m.
                L.is_valid_tls_message l m **
                pure (L.content_type_matches content_type ct /\
                      WS.parse_tls_message ct 'fragment_bytes == Some m)) **
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
                 CT.network_input_wf
                   'st0
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   (Ghost.reveal 'raw_bytes))
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          C.connection_exactly c st1 **
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
                CT.some_legal_response 'st0 st1 resp network_out_bytes app_out_bytes)
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
        (C.local_fail_state 'st0 C.tls_decode_error)
        resp
        content_type
        (Ghost.reveal 'fragment_bytes)
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      resp
    }
    Some l -> {
      match l {
        L.LTlsHandshake lhs -> {
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
              (L.LTlsApplicationData lapp)
              raw
              raw_len
              network_out
              network_out_len
              app_out
              app_out_len;
          CT.lemma_legal_network_response_unexpected_from_parse_success
            'st0
            (C.local_fail_state 'st0 C.tls_unexpected_message_error)
            resp
            content_type
            (Ghost.reveal 'fragment_bytes)
            (Ghost.reveal 'raw_bytes)
            'old_network_out
            'old_app_out;
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
      }
    }
  }
}
