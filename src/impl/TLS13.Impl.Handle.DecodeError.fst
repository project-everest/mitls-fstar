module TLS13.Impl.Handle.DecodeError

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CF = TLS13.Impl.ConnectionState.Fail
module CM = TLS13.Impl.ConnectionState.Model
module CT = TLS13.Impl.Client.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn handle_decode_error
  (c:CR.connection_state)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns resp: CT.client_response
  ensures CR.connection_exactly c (CM.local_fail_state 'st0 CM.tls_decode_error) **
          pts_to raw 'raw_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
          CT.decode_error_response
            'st0
            (CM.local_fail_state 'st0 CM.tls_decode_error)
            resp
            'old_network_out
            'old_app_out /\
          CT.some_legal_response
            'st0
            (CM.local_fail_state 'st0 CM.tls_decode_error)
            resp
            'old_network_out
            'old_app_out)
{
  CF.mark_decode_error c;
  let resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.DecodeError;
  };
  Seq.lemma_len_slice 'old_network_out 0 0;
  Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
  assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
  assert (pure (CT.decode_error_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_decode_error)
    resp
    'old_network_out
    'old_app_out));
  assert (pure (CT.some_legal_response
    'st0
    (CM.local_fail_state 'st0 CM.tls_decode_error)
    resp
    'old_network_out
    'old_app_out));
  resp
}
