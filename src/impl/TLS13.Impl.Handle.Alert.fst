module TLS13.Impl.Handle.Alert

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
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

fn handle_alert
  (c:CR.connection_state)
  (content_type:U8.t)
  (alert_wire:U8.t)
  (raw:array U8.t)
  (raw_len:SZ.t)
  (fragment:array U8.t)
  (fragment_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires CR.connection_exactly c 'st0 **
           (exists* m. L.is_valid_tls_message (L.LTlsAlert alert_wire) m) **
           pts_to raw 'raw_bytes **
           pts_to fragment 'fragment_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'raw_bytes == SZ.v raw_len /\
                 B.length 'fragment_bytes == SZ.v fragment_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.network_input_wf
                   'st0
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   (Ghost.reveal 'raw_bytes) /\
                 CT.parsed_message_wire_success
                   content_type
                   (Ghost.reveal 'fragment_bytes)
                   (L.LTlsAlert alert_wire))
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
{
  with m. unfold (L.is_valid_tls_message (L.LTlsAlert alert_wire) m);
  with malert. _;
  assert (pure (L.alert_description_matches alert_wire malert));
  assert (pure (m == M.TlsAlert malert));
  assert (pure (CT.wire_parse_success
    content_type
    (Ghost.reveal 'fragment_bytes)
    (M.TlsAlert malert)));
  assert (pure (CT.received_tls_raw_delta_legal_unbuffered
    'st0
    (M.TlsAlert malert)
    (Ghost.reveal 'raw_bytes)));
  let parsed_alert = Ghost.hide (L.alert_description_of_wire_or_unexpected alert_wire);
  L.lemma_alert_description_of_wire_matches alert_wire malert;
  assert (pure (Ghost.reveal parsed_alert == malert));
  assert (pure (L.alert_description_matches alert_wire (Ghost.reveal parsed_alert)));
  assert (pure (CT.wire_parse_success
    content_type
    (Ghost.reveal 'fragment_bytes)
    (M.TlsAlert (Ghost.reveal parsed_alert))));
  assert (pure (CT.received_tls_raw_delta_legal_unbuffered
    'st0
    (M.TlsAlert (Ghost.reveal parsed_alert))
    (Ghost.reveal 'raw_bytes)));

  let close_notify = alert_wire = 0uy;
  if close_notify {
    assert (pure (U8.v alert_wire == 0));
    assert (pure (Ghost.reveal parsed_alert == T.Close_notify));
    assert (pure (CT.received_tls_raw_delta_legal_unbuffered
      'st0
      (M.TlsAlert T.Close_notify)
      (Ghost.reveal 'raw_bytes)));
    let ready = CQ.can_receive_close_notify c;
    if ready {
      CN.mark_received_close_notify c raw;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      CM.lemma_received_close_notify_state_evolves 'st0 (Ghost.reveal 'raw_bytes);
      assert (pure (CT.legal_received_tls_response
        'st0
        (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
        resp
        (M.TlsAlert T.Close_notify)
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_tls_response
        'st0
        (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
        resp
        (M.TlsAlert T.Close_notify)
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out));
      CT.lemma_legal_network_response_handled_from_parse_success
        'st0
        (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
        resp
        content_type
        (Ghost.reveal 'fragment_bytes)
        (M.TlsAlert T.Close_notify)
        (Ghost.reveal 'raw_bytes)
        'old_network_out
        'old_app_out;
      assert (pure (CT.some_legal_response
        'st0
        (CM.received_close_notify_state 'st0 (Ghost.reveal 'raw_bytes))
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
  } else {
    assert (pure (U8.v alert_wire <> 0));
    L.lemma_alert_description_nonzero_not_close_notify alert_wire (Ghost.reveal parsed_alert);
    CN.mark_received_alert_failure c raw alert_wire #parsed_alert;
    let resp = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.ConnectionFailed;
    };
    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
    assert (pure (CT.wire_parse_success
      content_type
      (Ghost.reveal 'fragment_bytes)
      (M.TlsAlert (Ghost.reveal parsed_alert))));
    CM.lemma_received_alert_failure_state_evolves 'st0 (Ghost.reveal parsed_alert) (Ghost.reveal 'raw_bytes);
    assert (pure (CT.legal_received_tls_response
      'st0
      (CM.received_alert_failure_state 'st0 (Ghost.reveal parsed_alert) (Ghost.reveal 'raw_bytes))
      resp
      (M.TlsAlert (Ghost.reveal parsed_alert))
      (Ghost.reveal 'raw_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (CT.legal_handled_tls_response
      'st0
      (CM.received_alert_failure_state 'st0 (Ghost.reveal parsed_alert) (Ghost.reveal 'raw_bytes))
      resp
      (M.TlsAlert (Ghost.reveal parsed_alert))
      (Ghost.reveal 'raw_bytes)
      'old_network_out
      'old_app_out));
    CT.lemma_legal_network_response_handled_from_parse_success
      'st0
      (CM.received_alert_failure_state 'st0 (Ghost.reveal parsed_alert) (Ghost.reveal 'raw_bytes))
      resp
      content_type
      (Ghost.reveal 'fragment_bytes)
      (M.TlsAlert (Ghost.reveal parsed_alert))
      (Ghost.reveal 'raw_bytes)
      'old_network_out
      'old_app_out;
    assert (pure (CT.some_legal_response
      'st0
      (CM.received_alert_failure_state 'st0 (Ghost.reveal parsed_alert) (Ghost.reveal 'raw_bytes))
      resp
      'old_network_out
      'old_app_out));
    assert (pure (resp.CT.status == CT.IllegalTransition ==> False));
    resp
  }
}
