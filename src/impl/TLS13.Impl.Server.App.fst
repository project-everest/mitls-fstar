module TLS13.Impl.Server.App

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CF = TLS13.Impl.ConnectionState.Fail
module CLS = TLS13.Impl.ConnectionState.LocalSend
module CR = TLS13.Impl.ConnectionState.Repr
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8

fn process_send_application_data_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_app_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_application_data_state
                        'st0
                        (Ghost.reveal 'payload_bytes)
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  let ok =
    CLS.try_send_application_data
      s
      payload
      payload_len
      network_out
      network_out_len;
  if ok {
    with raw_sent network_out_bytes.
      assert (pts_to network_out network_out_bytes);
    assert (CR.connection_exactly
      s
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent));
    fold (connection_exactly
      s
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (SZ.v payload_len + 22 <= B.length network_out_bytes));
    assert (pure (CM.can_send_application_data
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent));
    assert (pure (Seq.equal
      raw_sent
      (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22))));
    assert (pure (SZ.fits (SZ.v payload_len + 22)));
    let written_len = SZ.add payload_len 22sz;
    assert (pure (SZ.v written_len == SZ.v payload_len + 22));
    let resp = {
      ST.network_out_len = written_len;
      ST.app_out_len = 0sz;
      ST.status = ST.StepOk;
    };
    Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_len);
    assert (pure (Seq.equal raw_sent (ST.response_network_out resp network_out_bytes)));
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_sent_application_data_state_evolves
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent;

    let ev = Ghost.hide (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
    });
    let delta = Ghost.hide {
      CS.delta_event = Ghost.reveal ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    };
    assert (pure (CS.legal_connection_delta
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent);
    CSL.lemma_event_raw_delta_legal_protected_segmented
      'st0.CS.cs_model
      (Ghost.reveal ev)
      raw_sent
      B.empty;
    assert (pure (CS.event_protected_raw_segmented_success
      (Ghost.reveal ev)
      raw_sent
      B.empty));
    assert (pure (CS.connection_state_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0));
    assert (pure (CS.model_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));
    assert (pure (CS.record_write_key_schedule_projection_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));

    assert (pure ((CM.sent_application_data_state
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.sent_application_data_state
      'st0
      (Ghost.reveal 'payload_bytes)
      raw_sent).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)));

    assert (pure (ST.legal_response_for_event
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_local_response
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.sent_application_data_state
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    resp
  } else {
    CF.mark_unexpected_message s;
    fold (connection_exactly s (CM.local_fail_state 'st0 CM.tls_unexpected_message_error));
    let resp = {
      ST.network_out_len = 0sz;
      ST.app_out_len = 0sz;
      ST.status = ST.IllegalTransition;
    };
    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_local_fail_state_evolves 'st0 CM.tls_unexpected_message_error;
    let delta = Ghost.hide {
      CS.delta_event =
        CS.ConnLocalEvent (CS.LocalFail CM.tls_unexpected_message_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    };
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.unexpected_message_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      'old_network_out
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    resp
  }
}

fn process_send_close_notify_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_app_local_event_input_ready
                   'st0
                   ST.LocalSendCloseNotify
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_close_notify_state
                        'st0
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCloseNotify
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  unfold (connection_exactly s 'st0);
  let ok =
    CLS.try_send_close_notify
      s
      network_out
      network_out_len;
  if ok {
    with raw_sent network_out_bytes.
      assert (pts_to network_out network_out_bytes);
    assert (CR.connection_exactly
      s
      (CM.sent_close_notify_state 'st0 raw_sent));
    fold (connection_exactly
      s
      (CM.sent_close_notify_state 'st0 raw_sent));
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (24 <= B.length network_out_bytes));
    assert (pure (CM.can_send_close_notify 'st0 raw_sent));
    assert (pure (Seq.equal raw_sent (Seq.slice network_out_bytes 0 24)));
    let resp = {
      ST.network_out_len = 24sz;
      ST.app_out_len = 0sz;
      ST.status = ST.StepOk;
    };
    Seq.lemma_len_slice network_out_bytes 0 24;
    assert (pure (Seq.equal raw_sent (ST.response_network_out resp network_out_bytes)));
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_sent_close_notify_state_evolves 'st0 raw_sent;

    let ev = Ghost.hide (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsAlert T.Close_notify;
    });
    let delta = Ghost.hide {
      CS.delta_event = Ghost.reveal ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
    };
    assert (pure (CS.legal_connection_delta
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent)));
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.sent_close_notify_state 'st0 raw_sent);
    CSL.lemma_event_raw_delta_legal_protected_segmented
      'st0.CS.cs_model
      (Ghost.reveal ev)
      raw_sent
      B.empty;
    assert (pure (CS.event_protected_raw_segmented_success
      (Ghost.reveal ev)
      raw_sent
      B.empty));
    assert (pure (CS.connection_state_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0));
    assert (pure (CS.model_record_keys_consistent_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));
    assert (pure (CS.record_write_key_schedule_projection_for_role
      CS.ServerEndpoint
      'st0.CS.cs_model));

    assert (pure ((CM.sent_close_notify_state 'st0 raw_sent).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.sent_close_notify_state 'st0 raw_sent).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.sent_close_notify_state 'st0 raw_sent).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.sent_close_notify_state 'st0 raw_sent)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.sent_close_notify_state 'st0 raw_sent)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.sent_close_notify_state 'st0 raw_sent)));

    assert (pure (ST.legal_response_for_event
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_local_response
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal ev)
      raw_sent
      B.empty
      network_out_bytes
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.sent_close_notify_state 'st0 raw_sent)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      network_out_bytes
      'old_app_out));
    resp
  } else {
    CF.mark_unexpected_message s;
    fold (connection_exactly s (CM.local_fail_state 'st0 CM.tls_unexpected_message_error));
    let resp = {
      ST.network_out_len = 0sz;
      ST.app_out_len = 0sz;
      ST.status = ST.IllegalTransition;
    };
    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    Seq.lemma_len_slice 'old_app_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
    CM.lemma_local_fail_state_evolves 'st0 CM.tls_unexpected_message_error;
    let delta = Ghost.hide {
      CS.delta_event =
        CS.ConnLocalEvent (CS.LocalFail CM.tls_unexpected_message_error);
      CS.delta_raw_sent = B.empty;
      CS.delta_raw_received = B.empty;
    };
    CSL.lemma_legal_connection_delta_full_log_consistent_for_role
      CS.ServerEndpoint
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_raw_event_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_connection_state_protected_raw_segmented_replay
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    CSL.lemma_legal_connection_delta_received_decode_replay_consistent
      'st0
      (Ghost.reveal delta)
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error);
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ((CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_role ==
      CS.ServerEndpoint));
    assert (pure (Some?
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error).CS.cs_model.CS.model_config.CS.config_server));
    assert (pure (ST.server_state_correct
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_raw_to_message_replay_consistent
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.server_end_to_end_invariant
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)));
    assert (pure (ST.unexpected_message_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      'old_network_out
      'old_app_out));
    assert (pure (ST.legal_handled_local_response
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (ST.server_local_event_end_to_end_correct
      'st0
      (CM.local_fail_state 'st0 CM.tls_unexpected_message_error)
      resp
      ST.LocalSendCloseNotify
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    resp
  }
}
