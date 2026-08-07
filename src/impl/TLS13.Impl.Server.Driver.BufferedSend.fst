module TLS13.Impl.Server.Driver.BufferedSend

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BC = TLS13.Impl.Server.Driver.BufferedChannel
module BN = TLS13.Impl.Server.Driver.BufferedNetwork
module BT = Common.BufferedTCP
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module S = TLS13.Impl.Server
module Seq = FStar.Seq
module SM = TLS13.Spec.StateMachine.ClientTrace
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module Box = Pulse.Lib.Box

let lemma_control_snapshot_app_ready
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag == 2uy)
      (ensures
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
=
  assert_norm (U8.v 2uy == 2);
  assert (U8.v snapshot.CR.snapshot_control_tag == 2);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlApplicationData -> ()
  | _ -> assert False

let lemma_query_application_ready
  (snapshot:CR.control_snapshot)
  (keys:bool)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        (keys ==>
          CS.application_record_keys_installed_for_role
            CS.ServerEndpoint st.CS.cs_model))
      (ensures
        (snapshot.CR.snapshot_control_tag = 2uy && keys) ==>
          st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
          CS.application_record_keys_installed_for_role
            CS.ServerEndpoint st.CS.cs_model)
=
  if snapshot.CR.snapshot_control_tag = 2uy && keys
  then lemma_control_snapshot_app_ready snapshot st
  else ()

fn query_application_ready
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_connected
      d
      'st
      'certificate_chain
      'credential_identity
      'received
      'sent
  returns ready:bool
  ensures
    DS.top_server_driver_connected
      d
      'st
      'certificate_chain
      'credential_identity
      'received
      'sent **
    pure (
      ST.server_end_to_end_invariant 'st /\
      (ready ==>
        'st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        CS.application_record_keys_installed_for_role
          CS.ServerEndpoint
          'st.CS.cs_model))
{
  unfold (DS.top_server_driver_connected
    d 'st 'certificate_chain 'credential_identity 'received 'sent);
  with channel model committed buffered_len.
    unfold (DS.top_server_driver_connected_indexed
      d 'st 'certificate_chain 'credential_identity
      'received 'sent channel model committed buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    'st
    'certificate_chain
    'credential_identity
    (BT.pending model)
    buffered_len
    model
    'received
    committed
    'sent);
  rewrite
    (S.connection_exactly d.top_server_driver_server 'st)
    as
    (CR.connection_exactly d.top_server_driver_server 'st);
  let control = CQ.get_control_snapshot d.top_server_driver_server;
  let keys =
    CQ.server_application_record_keys_installed_runtime
      d.top_server_driver_server;
  rewrite
    (CR.connection_exactly d.top_server_driver_server 'st)
    as
    (S.connection_exactly d.top_server_driver_server 'st);
  let ready = control.CR.snapshot_control_tag = 2uy && keys;
  lemma_query_application_ready control keys 'st;
  fold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d channel)
    'st
    'certificate_chain
    'credential_identity
    (BT.pending model)
    buffered_len
    model
    'received
    committed
    'sent);
  fold (DS.top_server_driver_connected_indexed
    d 'st 'certificate_chain 'credential_identity
    'received 'sent channel model committed buffered_len);
  fold (DS.top_server_driver_connected
    d 'st 'certificate_chain 'credential_identity 'received 'sent);
  ready
}

let lemma_send_ready
  (st:CS.connection_state)
  (payload certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.server_end_to_end_invariant st /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        CS.application_record_keys_installed_for_role
          CS.ServerEndpoint st.CS.cs_model /\
        B.length payload <= SM.max_application_data_fragment_len)
      (ensures
        BN.local_event_ready
          st
          ST.LocalSendApplicationData
          payload
          certificate_chain
          credential_identity)
=
  assert (st.CS.cs_model.CS.model_config.CS.config_role ==
    CS.ServerEndpoint);
  assert_norm (CS.traffic_label_for_endpoint_direction
    CS.ServerEndpoint
    CS.TrafficWrite == CS.ServerTraffic);
  match st.CS.cs_model.CS.model_handshake
    .CS.hs_keys.CS.ks_server_application_traffic with
  | Some _ -> ()
  | None -> assert False

let lemma_step_sent_app_data_control
  (model0 model1:CS.connection_model)
  (bytes:B.bytes)
  : Lemma
      (requires
        model0.CS.model_control == CS.ControlApplicationData /\
        CS.step_tls_message model0 CL.Sent (M.TlsApplicationData bytes) ==
          Some model1)
      (ensures model1.CS.model_control == CS.ControlApplicationData)
=
  ()

let lemma_local_send_application_data_control
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0 st1 resp ST.LocalSendApplicationData payload network_out app_out /\
        resp.ST.status == ST.StepOk /\
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData)
=
  assert (ST.legal_handled_local_response
    st0 st1 resp ST.LocalSendApplicationData payload network_out app_out);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        ST.legal_local_response
          st0 st1 resp ST.LocalSendApplicationData payload ev
          raw_sent raw_received network_out app_out) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        ST.legal_local_response
          st0 st1 resp ST.LocalSendApplicationData payload ev
          raw_sent raw_received network_out app_out) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        ST.legal_local_response
          st0 st1 resp ST.LocalSendApplicationData payload ev
          raw_sent raw_received network_out app_out) in
  assert (ST.local_event_kind_matches
    ST.LocalSendApplicationData payload ev);
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
     | M.TlsApplicationData bytes ->
       assert (msg.CL.message_direction == CL.Sent);
       assert (CS.step_tls_message
         st0.CS.cs_model
         CL.Sent
         (M.TlsApplicationData bytes) == Some st1.CS.cs_model);
       lemma_step_sent_app_data_control
         st0.CS.cs_model st1.CS.cs_model bytes
     | _ -> assert False)
  | _ -> assert False

fn run
  (d:DS.top_server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to payload 'payload_bytes **
    pure (B.length 'payload_bytes == SZ.v payload_len)
  returns status:send_status
  ensures
    pts_to payload 'payload_bytes **
    (match status with
     | BufferedSendOk
     | BufferedSendPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
     | BufferedSendFailed ->
       exists* wire_received1 wire_sent1 app_log1.
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1)
{
  BC.open_channel_invariant
    d wire_received0 wire_sent0 pending0 app_log0;
  with st0 certificate_chain credential_identity.
    assert (DS.top_server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  assert_norm (SM.max_application_data_fragment_len == 16384);
  let too_large = SZ.gt payload_len 16384sz;
  if too_large {
    BC.pack_connected_channel
      d
      (Ghost.hide st0)
      (Ghost.hide certificate_chain)
      (Ghost.hide credential_identity)
      wire_received0
      wire_sent0;
    BufferedSendPayloadTooLarge
  } else {
    let ready = query_application_ready d;
    if (ready = false) {
      BC.pack_connected_channel_terminal
        d
        (Ghost.hide st0)
        (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity)
        wire_received0
        wire_sent0;
      BufferedSendFailed
    } else {
      lemma_send_ready
        st0
        (Ghost.reveal 'payload_bytes)
        certificate_chain
        credential_identity;
      unfold (DS.top_server_driver_connected
        d st0 certificate_chain credential_identity
        (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
      with channel model committed buffered_len.
        unfold (DS.top_server_driver_connected_indexed
          d st0 certificate_chain credential_identity
          (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
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
          (Ghost.reveal wire_received0) committed
          (Ghost.reveal wire_sent0))
        as
        (DS.buffered_driver_indexed
          (DS.top_server_as_buffered d concrete_channel)
          st0 certificate_chain credential_identity
          (BT.pending model) buffered_len model
          (Ghost.reveal wire_received0) committed
          (Ghost.reveal wire_sent0));
      unfold (DS.buffered_driver_indexed
        (DS.top_server_as_buffered d concrete_channel)
        st0 certificate_chain credential_identity
        (BT.pending model) buffered_len model
        (Ghost.reveal wire_received0) committed
        (Ghost.reveal wire_sent0));
      let concrete_buffered_len = BT.pending_length concrete_channel;
      fold (DS.buffered_driver_indexed
        (DS.top_server_as_buffered d concrete_channel)
        st0 certificate_chain credential_identity
        (BT.pending model) concrete_buffered_len model
        (Ghost.reveal wire_received0) committed
        (Ghost.reveal wire_sent0));
      unfold (DS.top_server_driver_buffers d);
      with empty_payload material network_out cv_input signature app_out local_app_out.
        assert (
          V.pts_to d.top_server_driver_network_out #1.0R network_out **
          V.pts_to d.top_server_driver_app_out #1.0R app_out);
      V.to_array_pts_to d.top_server_driver_network_out;
      V.to_array_pts_to d.top_server_driver_app_out;
      fold (DS.buffered_driver_exactly
        (DS.top_server_as_buffered d concrete_channel)
        st0 certificate_chain credential_identity
        (BT.pending model) concrete_buffered_len);
      let result =
        BN.process_local_event
          (DS.top_server_as_buffered d concrete_channel)
          ST.LocalSendApplicationData
          payload
          payload_len
          (V.vec_to_array d.top_server_driver_network_out)
          DS.driver_network_out_capacity
          (V.vec_to_array d.top_server_driver_app_out)
          DS.driver_app_out_capacity;
      with st1 network_out1 app_out1.
        assert (
          DS.buffered_driver_exactly
            (DS.top_server_as_buffered d concrete_channel)
            st1 certificate_chain credential_identity
            (BT.pending model) concrete_buffered_len **
          pts_to payload 'payload_bytes **
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
      if ok {
        lemma_local_send_application_data_control
          st0 st1 result.BN.local_write_resp
          (Ghost.reveal 'payload_bytes)
          network_out1
          app_out1;
        BC.pack_connected_channel
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        BufferedSendOk
      } else {
        BC.pack_connected_channel_terminal
          d
          (Ghost.hide st1)
          (Ghost.hide certificate_chain)
          (Ghost.hide credential_identity)
          (Ghost.hide received1)
          (Ghost.hide sent1);
        BufferedSendFailed
      }
    }
  }
}

let key_update_kind (request:bool) : ST.local_event_kind =
  if request then ST.LocalSendKeyUpdateRequested else ST.LocalSendKeyUpdate

let lemma_key_update_ready
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        (kind == ST.LocalSendKeyUpdate \/
         kind == ST.LocalSendKeyUpdateRequested) /\
        ST.server_end_to_end_invariant st /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        CS.application_record_keys_installed_for_role
          CS.ServerEndpoint st.CS.cs_model /\
        B.length payload == 0)
      (ensures
        BN.local_event_ready
          st
          kind
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

(* A sent KeyUpdate only rotates the write key; it leaves the control state in
   [ControlApplicationData], which is what keeps the channel invariant (rather
   than the terminal one) re-establishable after the send. *)
let lemma_step_sent_key_update_control
  (model0 model1:CS.connection_model)
  (req:M.key_update_request)
  : Lemma
      (requires
        model0.CS.model_control == CS.ControlApplicationData /\
        CS.step_tls_message
          model0 CL.Sent (M.TlsKeyUpdate req) == Some model1)
      (ensures model1.CS.model_control == CS.ControlApplicationData)
=
  ()

#push-options "--split_queries always"
let lemma_local_send_key_update_control
  (st0 st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        (kind == ST.LocalSendKeyUpdate \/
         kind == ST.LocalSendKeyUpdateRequested) /\
        ST.server_local_event_end_to_end_correct
          st0 st1 resp kind payload network_out app_out /\
        resp.ST.status == ST.StepOk /\
        st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures
        st1.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        ST.server_connection_control_not_failed st1)
=
  assert (ST.legal_handled_local_response
    st0 st1 resp kind payload network_out app_out);
  let ev =
    ID.indefinite_description_ghost
      CS.conn_event
      (fun ev -> exists raw_sent raw_received.
        ST.legal_local_response
          st0 st1 resp kind payload ev
          raw_sent raw_received network_out app_out) in
  let raw_sent =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_sent -> exists raw_received.
        ST.legal_local_response
          st0 st1 resp kind payload ev
          raw_sent raw_received network_out app_out) in
  let raw_received =
    ID.indefinite_description_ghost
      B.bytes
      (fun raw_received ->
        ST.legal_local_response
          st0 st1 resp kind payload ev
          raw_sent raw_received network_out app_out) in
  assert (ST.local_event_kind_matches kind payload ev);
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
     | M.TlsKeyUpdate req ->
       // [local_event_kind_matches] pins the direction for both KeyUpdate
       // kinds, but only after the kind itself is concrete.
       (match kind with
        | ST.LocalSendKeyUpdate -> assert (msg.CL.message_direction == CL.Sent)
        | ST.LocalSendKeyUpdateRequested ->
          assert (msg.CL.message_direction == CL.Sent));
       assert (CS.step_tls_message
         st0.CS.cs_model
         CL.Sent
         (M.TlsKeyUpdate req) == Some st1.CS.cs_model);
       lemma_step_sent_key_update_control
         st0.CS.cs_model st1.CS.cs_model req
     | _ ->
       (match kind with
        | ST.LocalSendKeyUpdate -> assert False
        | ST.LocalSendKeyUpdateRequested -> assert False))
  | _ ->
    (match kind with
     | ST.LocalSendKeyUpdate -> assert False
     | ST.LocalSendKeyUpdateRequested -> assert False)
#pop-options

fn run_key_update
  (d:DS.top_server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (request:bool)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0)
  returns status:send_status
  ensures
    (match status with
     | BufferedSendOk
     | BufferedSendPayloadTooLarge ->
       exists* wire_received1 wire_sent1 pending1 app_log1.
         DS.top_server_channel_inv
           d wire_received1 wire_sent1 pending1 app_log1
     | BufferedSendFailed ->
       exists* wire_received1 wire_sent1 app_log1.
         DS.top_server_channel_terminal
           d wire_received1 wire_sent1 app_log1)
{
  BC.open_channel_invariant
    d wire_received0 wire_sent0 pending0 app_log0;
  with st0 certificate_chain credential_identity.
    assert (DS.top_server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
  let ready = query_application_ready d;
  if (ready = false) {
    BC.pack_connected_channel_terminal
      d
      (Ghost.hide st0)
      (Ghost.hide certificate_chain)
      (Ghost.hide credential_identity)
      wire_received0
      wire_sent0;
    BufferedSendFailed
  } else {
    let kind = key_update_kind request;
    assert (pure (kind == ST.LocalSendKeyUpdate \/
                  kind == ST.LocalSendKeyUpdateRequested));
    unfold (DS.top_server_driver_connected
      d st0 certificate_chain credential_identity
      (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0));
    with channel model committed buffered_len.
      unfold (DS.top_server_driver_connected_indexed
        d st0 certificate_chain credential_identity
        (Ghost.reveal wire_received0) (Ghost.reveal wire_sent0)
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
        (Ghost.reveal wire_received0) committed
        (Ghost.reveal wire_sent0))
      as
      (DS.buffered_driver_indexed
        (DS.top_server_as_buffered d concrete_channel)
        st0 certificate_chain credential_identity
        (BT.pending model) buffered_len model
        (Ghost.reveal wire_received0) committed
        (Ghost.reveal wire_sent0));
    unfold (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st0 certificate_chain credential_identity
      (BT.pending model) buffered_len model
      (Ghost.reveal wire_received0) committed
      (Ghost.reveal wire_sent0));
    let concrete_buffered_len = BT.pending_length concrete_channel;
    fold (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      st0 certificate_chain credential_identity
      (BT.pending model) concrete_buffered_len model
      (Ghost.reveal wire_received0) committed
      (Ghost.reveal wire_sent0));
    unfold (DS.top_server_driver_buffers d);
    with empty_payload material network_out cv_input signature app_out local_app_out.
      assert (
        V.pts_to d.top_server_driver_empty_payload #1.0R empty_payload **
        V.pts_to d.top_server_driver_network_out #1.0R network_out **
        V.pts_to d.top_server_driver_app_out #1.0R app_out);
    lemma_key_update_ready
      st0 kind empty_payload certificate_chain credential_identity;
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
        kind
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
    if ok {
      lemma_local_send_key_update_control
        st0 st1 result.BN.local_write_resp
        kind
        empty_payload1
        network_out1
        app_out1;
      BC.pack_connected_channel
        d
        (Ghost.hide st1)
        (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity)
        (Ghost.hide received1)
        (Ghost.hide sent1);
      BufferedSendOk
    } else {
      BC.pack_connected_channel_terminal
        d
        (Ghost.hide st1)
        (Ghost.hide certificate_chain)
        (Ghost.hide credential_identity)
        (Ghost.hide received1)
        (Ghost.hide sent1);
      BufferedSendFailed
    }
  }
}
