module TLS13.Impl.Handle.ChangeCipherSpec

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
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
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
                  'old_app_out)
{
  let handshaking = CQ.is_handshaking c;
  if handshaking {
   with m. assert (pure True);
   L.free_tls_message l;
   CN.mark_received_change_cipher_spec c raw;
   let resp = {
     CT.network_out_len = 0sz;
     CT.app_out_len = 0sz;
     CT.status = CT.StepOk;
   };
   Seq.lemma_len_slice 'old_network_out 0 0;
   Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
   assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
   CM.lemma_received_change_cipher_spec_state_evolves 'st0 (Ghost.reveal 'raw_bytes);
   assert (pure (CT.legal_received_tls_response
     'st0
     (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))
     resp
     M.TlsChangeCipherSpec
     (Ghost.reveal 'raw_bytes)
     'old_network_out
     'old_app_out));
   assert (pure (CT.legal_handled_tls_response
     'st0
     (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))
     resp
     M.TlsChangeCipherSpec
     (Ghost.reveal 'raw_bytes)
     'old_network_out
     'old_app_out));
   assert (pure (CT.some_legal_response
     'st0
     (CM.received_change_cipher_spec_state 'st0 (Ghost.reveal 'raw_bytes))
     resp
     'old_network_out
     'old_app_out));
   resp
  } else {
   with m. assert (pure True);
   L.free_tls_message l;
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
   assert (pure (CT.legal_handled_tls_response
     'st0
     (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
     resp
     M.TlsChangeCipherSpec
     (Ghost.reveal 'raw_bytes)
     'old_network_out
     'old_app_out));
   assert (pure (CT.some_legal_response
     'st0
     (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
     resp
     'old_network_out
     'old_app_out));
   resp
  }
}
