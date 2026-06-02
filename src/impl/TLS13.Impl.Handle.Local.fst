module TLS13.Impl.Handle.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.ConnectionState
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn handle_local_event
  (c:C.connection_state)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns resp: CT.client_response
  ensures C.connection_exactly c (C.local_fail_state 'st0 C.tls_unexpected_message_error) **
          pts_to payload 'payload_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                CT.unexpected_message_response
                  'st0
                  (C.local_fail_state 'st0 C.tls_unexpected_message_error)
                  resp
                  'old_network_out
                  'old_app_out /\
                CT.some_legal_response
                  'st0
                  (C.local_fail_state 'st0 C.tls_unexpected_message_error)
                  resp
                  'old_network_out
                  'old_app_out)
{
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
  assert (pure (CT.some_legal_response
    'st0
    (C.local_fail_state 'st0 C.tls_unexpected_message_error)
    resp
    'old_network_out
    'old_app_out));
  resp
}

