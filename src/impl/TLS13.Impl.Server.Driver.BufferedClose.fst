module TLS13.Impl.Server.Driver.BufferedClose

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BC = TLS13.Impl.Server.Driver.BufferedChannel
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module BR = TLS13.Impl.Server.Driver.BufferedReceive
module BS = TLS13.Impl.Server.Driver.BufferedSend
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module V = Pulse.Lib.Vec
module Box = Pulse.Lib.Box

let lemma_close_ready
  (st:CS.connection_state)
  (payload certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.server_end_to_end_invariant st /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        CS.application_record_keys_installed_for_role
          CS.ServerEndpoint st.CS.cs_model /\
        B.length payload == 0)
      (ensures
        BN.local_event_ready
          st
          ST.LocalSendCloseNotify
          payload
          certificate_chain
          credential_identity)
=
  assert (forall (i:nat{i < B.length payload}).
    Seq.index payload i == Seq.index B.empty i);
  Seq.lemma_eq_intro payload B.empty;
  assert (st.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint);
  match st.CS.cs_model.CS.model_handshake
    .CS.hs_keys.CS.ks_server_application_traffic with
  | Some _ -> ()
  | None -> assert False

let lemma_step_sent_close_control
  (model0 model1:CS.connection_model)
  : Lemma
      (requires
        model0.CS.model_control == CS.ControlApplicationData /\
        CS.step_tls_message
          model0 CL.Sent (M.TlsAlert T.Close_notify) == Some model1)
      (ensures model1.CS.model_control == CS.ControlClosing)
=
  ()

let lemma_local_send_close_control
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp ST.LocalSendCloseNotify payload network_out app_out /\
        resp.ST.status == ST.StepOk /\
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st1.CS.cs_model.CS.model_control == CS.ControlClosing /\
        ST.server_connection_control_not_failed st1)
=
  assert (ST.legal_handled_local_response
    st0 st1 resp ST.LocalSendCloseNotify payload network_out app_out);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        ST.legal_local_response
          st0 st1 resp ST.LocalSendCloseNotify payload ev
          raw_sent raw_received network_out app_out) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        ST.legal_local_response
          st0 st1 resp ST.LocalSendCloseNotify payload ev
          raw_sent raw_received network_out app_out) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        ST.legal_local_response
          st0 st1 resp ST.LocalSendCloseNotify payload ev
          raw_sent raw_received network_out app_out) in
  assert (ST.local_event_kind_matches
    ST.LocalSendCloseNotify payload ev);
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model);
  match ev with
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsAlert T.Close_notify ->
       assert (msg.CL.message_direction == CL.Sent);
       assert (CS.step_tls_message
         st0.CS.cs_model
         CL.Sent
         (M.TlsAlert T.Close_notify) == Some st1.CS.cs_model);
       lemma_step_sent_close_control st0.CS.cs_model st1.CS.cs_model
     | _ -> assert False)
  | _ -> assert False

fn abort_connected
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_connected
      d
      'st
      'certificate_chain
      'credential_identity
      'received
      'sent
  ensures
    DS.top_server_driver_closed
      d 'st 'certificate_chain 'credential_identity
{
  TLS13.Impl.Server.Driver.BufferedTransport.close_transport_once d
}

fn abort
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed
        d st certificate_chain credential_identity
{
  BC.open_channel_invariant
    d wire_received wire_sent pending app_log;
  abort_connected d
}

fn abort_terminal
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_terminal
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed
        d st certificate_chain credential_identity
{
  BC.open_terminal_invariant d wire_received wire_sent app_log;
  abort_connected d
}

fn run
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns status:close_status
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed
        d st certificate_chain credential_identity
{
  BC.open_channel_invariant
    d wire_received wire_sent pending app_log;
  with st0 certificate_chain credential_identity.
    assert (DS.top_server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  let ready = BS.query_application_ready d;
  if (ready = false) {
    abort_connected d;
    BufferedCloseClosed
  } else {
    unfold (DS.top_server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
    with channel model committed buffered_len.
      unfold (DS.top_server_driver_connected_indexed
        d st0 certificate_chain credential_identity
        (Ghost.reveal wire_received) (Ghost.reveal wire_sent)
        channel model committed buffered_len);
    let current_channel = Box.(!d.top_server_driver_channel);
    assert (pure (current_channel == Some channel));
    let concrete_channel = Some?.v current_channel;
    assert (pure (concrete_channel == channel));
    rewrite
      (DS.buffered_driver_indexed
        (DS.top_server_as_buffered d channel)
        st0 certificate_chain credential_identity
        (BT.pending model) buffered_len model
        (Ghost.reveal wire_received) committed
        (Ghost.reveal wire_sent))
      as
      (DS.buffered_driver_indexed
        (DS.top_server_as_buffered d concrete_channel)
        st0 certificate_chain credential_identity
        (BT.pending model) buffered_len model
        (Ghost.reveal wire_received) committed
        (Ghost.reveal wire_sent));
    unfold (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st0 certificate_chain credential_identity
      (BT.pending model) buffered_len model
      (Ghost.reveal wire_received) committed
      (Ghost.reveal wire_sent));
    let concrete_buffered_len = BT.pending_length concrete_channel;
    fold (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st0 certificate_chain credential_identity
      (BT.pending model) concrete_buffered_len model
      (Ghost.reveal wire_received) committed
      (Ghost.reveal wire_sent));
    unfold (DS.top_server_driver_buffers d);
    with empty_payload material network_out cv_input signature app_out local_app_out.
      assert (
        V.pts_to d.top_server_driver_empty_payload #1.0R empty_payload **
        V.pts_to d.top_server_driver_network_out #1.0R network_out **
        V.pts_to d.top_server_driver_app_out #1.0R app_out);
    lemma_close_ready
      st0 empty_payload certificate_chain credential_identity;
    V.to_array_pts_to d.top_server_driver_empty_payload;
    V.to_array_pts_to d.top_server_driver_network_out;
    V.to_array_pts_to d.top_server_driver_app_out;
    fold (DS.buffered_driver_exactly
      (DS.top_server_as_buffered d concrete_channel)
      st0 certificate_chain credential_identity
      (BT.pending model) concrete_buffered_len);
    let result =
      BN.process_local_event
        (DS.top_server_as_buffered d concrete_channel)
        ST.LocalSendCloseNotify
        (V.vec_to_array d.top_server_driver_empty_payload)
        0sz
        (V.vec_to_array d.top_server_driver_network_out)
        DS.driver_network_out_capacity
        (V.vec_to_array d.top_server_driver_app_out)
        DS.driver_app_out_capacity;
    with st1 empty_payload1 network_out1 app_out1.
      assert (
        DS.buffered_driver_exactly
          (DS.top_server_as_buffered d concrete_channel)
          st1 certificate_chain credential_identity
          (BT.pending model) concrete_buffered_len **
        pts_to
          (V.vec_to_array d.top_server_driver_empty_payload)
          empty_payload1 **
        pts_to
          (V.vec_to_array d.top_server_driver_network_out)
          network_out1 **
        pts_to
          (V.vec_to_array d.top_server_driver_app_out)
          app_out1);
    unfold (DS.buffered_driver_exactly
      (DS.top_server_as_buffered d concrete_channel)
      st1 certificate_chain credential_identity
      (BT.pending model) concrete_buffered_len);
    with model1 received1 committed1 sent1.
      unfold (DS.buffered_driver_indexed
        (DS.top_server_as_buffered d concrete_channel)
        st1 certificate_chain credential_identity
        (BT.pending model) concrete_buffered_len
        model1 received1 committed1 sent1);
    assert (pure (Seq.equal
      (BT.pending model1)
      (BT.pending model)));
    Seq.lemma_eq_elim (BT.pending model1) (BT.pending model);
    fold (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st1 certificate_chain credential_identity
      (BT.pending model1) concrete_buffered_len
      model1 received1 committed1 sent1);
    V.to_vec_pts_to d.top_server_driver_empty_payload;
    V.to_vec_pts_to d.top_server_driver_network_out;
    V.to_vec_pts_to d.top_server_driver_app_out;
    fold (DS.top_server_driver_buffers d);
    fold (DS.top_server_driver_connected_indexed
      d st1 certificate_chain credential_identity
      received1 sent1 concrete_channel model1
      committed1 concrete_buffered_len);
    fold (DS.top_server_driver_connected
      d st1 certificate_chain credential_identity received1 sent1);
    let ok = result.BN.local_write_resp.ST.status = ST.StepOk;
    if (ok = false) {
      abort_connected d;
      BufferedCloseFailed
    } else {
      lemma_local_send_close_control
        st0 st1 result.BN.local_write_resp
        empty_payload1 network_out1 app_out1;
      if wait_for_peer {
        let awaited = BR.await_peer_close d network_fuel;
        match awaited {
          BR.BufferedReceiveClosed -> {
            abort_connected d;
            BufferedCloseClosed
          }
          BR.BufferedReceiveExhausted -> {
            abort_connected d;
            BufferedCloseExhausted
          }
          BR.BufferedReceiveFailed -> {
            abort_connected d;
            BufferedCloseFailed
          }
          BR.BufferedReceiveOk -> {
            assert (pure False);
            abort_connected d;
            BufferedCloseFailed
          }
          BR.BufferedReceiveOutputBufferTooSmall -> {
            assert (pure False);
            abort_connected d;
            BufferedCloseFailed
          }
        }
      } else {
        abort_connected d;
        BufferedCloseClosed
      }
    }
  }
}
