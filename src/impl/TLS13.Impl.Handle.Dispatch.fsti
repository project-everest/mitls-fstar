module TLS13.Impl.Handle.Dispatch

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.ConnectionState
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(**
  TCB boundary for the extraction-facing parsed-message dispatcher.

  This function consumes the parser success/failure evidence for `parsed`,
  matches on the parsed low-level TLS message, and routes to the
  corresponding per-message handler contract.
**)
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
              exists* ct m.
                L.is_valid_tls_message l m **
                pure (L.content_type_matches content_type ct /\
                      WS.parse_tls_message ct 'fragment_bytes == Some m)
            | None ->
              pure (forall (ct:T.content_type).
                L.content_type_matches content_type ct ==>
                WS.parse_tls_message ct 'fragment_bytes == None)) **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          C.connection_exactly c st1 **
          pts_to raw 'raw_bytes **
          pts_to fragment 'fragment_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.some_legal_response 'st0 st1 resp network_out_bytes app_out_bytes)
