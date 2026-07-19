module TLS13.Impl.Handle.ApplicationData

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

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
                (resp.CT.status == CT.NeedMoreInput ==> False) /\
                (resp.CT.status == CT.IllegalTransition ==>
                 CT.unexpected_message_response
                   'st0
                   st1
                   resp
                   'old_network_out
                   app_out_bytes) /\
                (SZ.v resp.CT.app_out_len > 0 ==>
                 resp.CT.status == CT.StepOk /\
                 resp.CT.network_out_len == 0sz) /\
                (resp.CT.status == CT.OutputBufferTooSmall ==> False))
