module TLS13.Impl.Handle.Handshake

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module CR = TLS13.Impl.ConnectionState.Repr
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

fn handle_handshake_message
  (c:CR.connection_state)
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
  requires CR.connection_exactly c 'st0 **
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
          CR.connection_exactly c st1 **
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
                 'old_app_out /\
               (resp.CT.status == CT.NeedMoreInput ==> False) /\
               (resp.CT.status == CT.IllegalTransition ==>
                 CT.unexpected_message_response
                   'st0
                   st1
                   resp
                   'old_network_out
                   'old_app_out) /\
               (resp.CT.status == CT.OutputBufferTooSmall ==> False))
