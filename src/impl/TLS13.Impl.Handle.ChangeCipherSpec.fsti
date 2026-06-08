module TLS13.Impl.Handle.ChangeCipherSpec

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn handle_change_cipher_spec
  (c:CR.connection_state)
  (l:L.tls_message)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           (exists* m. L.is_valid_tls_message l m) **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
           B.length 'old_network_out == SZ.v network_out_len /\
           B.length 'old_app_out == SZ.v app_out_len /\
           L.tls_message_is_change_cipher_spec l /\
           CT.received_tls_raw_delta_legal
                   'st0
                   M.TlsChangeCipherSpec
                   (Ghost.reveal 'raw_bytes))
  returns resp: CT.client_response
  ensures exists* st1.
          CR.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                CT.legal_handled_tls_response
                  'st0
                  st1
                  resp
                  M.TlsChangeCipherSpec
                  (Ghost.reveal 'raw_bytes)
                  'old_network_out
                  'old_app_out /\
                CT.some_legal_response
                  'st0
                  st1
                  resp
                  'old_network_out
                  'old_app_out /\
                (resp.CT.status == CT.NeedMoreInput ==> False))
