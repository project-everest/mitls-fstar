module TLS13.Impl.Client.Driver.State

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module CP = TLS13.Impl.Client.CanonicalProtocol
module CPI = Common.ProtocolImplementation
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module EC = TLS13.Spec.Endpoint.Client
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module CI = Common.ChannelImplementation
module TChannel = TLS13.Impl.Channel
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Sem = TLS13.Wire.Semantics
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
noextract
let client_driver_application_ready
  (st:CS.connection_state)
  : prop =
  CT.client_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_record_keys_installed_for_role CS.ClientEndpoint st.CS.cs_model

noextract
let client_driver_sent_log_exact
  (st:CS.connection_state)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent

noextract
let client_driver_received_log_accounted
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
  (forall b.
    SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b received)

noextract
let client_driver_received_log_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  exists retained.
    Seq.equal received
      (B.append st.CS.cs_wire_log.CL.raw_received retained)

noextract
let client_driver_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length received == B.length st.CS.cs_wire_log.CL.raw_received

noextract
let client_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists network_out_bytes app_out_bytes.
    CT.local_event_end_to_end_correct
      st0
      st1
      resp
      kind
      payload
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append sent (CT.response_network_out resp network_out_bytes))

type driver_workflow_status =
  | DriverWorkflowOk
  | DriverWorkflowNeedMoreInput
  | DriverWorkflowStepFailed
  | DriverWorkflowExhausted
  | DriverWorkflowClosed
  | DriverWorkflowPayloadTooLarge
  | DriverWorkflowOutputBufferTooSmall

noextract
let client_driver_send_status_correct
  (status:driver_workflow_status)
  (resp:CT.client_response)
  : prop =
  if resp.CT.status == CT.StepOk
  then status == DriverWorkflowOk
  else status == DriverWorkflowStepFailed

(**
  TLS 1.3 bounds a single application-data record's plaintext at
  [SM.max_application_data_fragment_len] (2^14 = 16384) bytes.  [send]
  performs this authoritative length test itself, so any caller-supplied
  payload longer than the bound is unambiguously rejected up front without
  attempting to process it.
**)
noextract
let client_driver_payload_too_large
  (payload:B.bytes)
  : prop =
  B.length payload > SM.max_application_data_fragment_len

noextract
let client_driver_send_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (status:driver_workflow_status)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  (if status == DriverWorkflowPayloadTooLarge
   then
     st1 == st0 /\
     Seq.equal sent' sent /\
     client_driver_payload_too_large payload
   else
     exists resp.
       client_driver_local_write_correct
         st0
         st1
         resp
         CT.LocalSendApplicationData
         payload
         sent
         sent' /\
       client_driver_send_status_correct status resp) /\
  Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    st0.CS.cs_wire_log.CL.raw_received

noextract
let client_driver_close_status_correct
  (wait_for_peer:bool)
  (status:driver_workflow_status)
  (resp:CT.client_response)
  : prop =
  (resp.CT.status <> CT.StepOk ==> status == DriverWorkflowStepFailed) /\
  (resp.CT.status == CT.StepOk /\ wait_for_peer == false ==>
    status == DriverWorkflowClosed)

noextract
let client_driver_close_correct
  (st0:CS.connection_state)
  (st_close_notify:CS.connection_state)
  (status:driver_workflow_status)
  (wait_for_peer:bool)
  : prop =
  exists resp.
    client_driver_local_write_correct
      st0
      st_close_notify
      resp
      CT.LocalSendCloseNotify
      B.empty
      st0.CS.cs_wire_log.CL.raw_sent
      st_close_notify.CS.cs_wire_log.CL.raw_sent /\
    client_driver_close_status_correct wait_for_peer status resp

type client_receive_result = {
  client_receive_status: driver_workflow_status;
  client_receive_len: SZ.t;
}

noextract
noeq
type client_receive_observation = {
  client_receive_observed_status: driver_workflow_status;
  client_receive_observed_response: CT.client_buffer_response;
}

noextract
let client_receive_observation_network_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (obs:client_receive_observation)
  (app_out:B.bytes)
  : prop =
  obs.client_receive_observed_status <> DriverWorkflowExhausted ==>
    exists st_network st_before input old_network_out network_out old_app_out observed_app_out.
      CT.network_bytes_end_to_end_correct
        st_before
        st_network
        obs.client_receive_observed_response
        input
        old_network_out
        network_out
        old_app_out
        observed_app_out /\
      (obs.client_receive_observed_status == DriverWorkflowOk ==>
        st_network == st1 /\ Seq.equal observed_app_out app_out) /\
      (**
        A peer close_notify is detected as a StepOk network step that both
        produces zero application bytes and drives the connection to
        [CS.ControlClosed]. When [receive] reports [DriverWorkflowClosed], the
        final connection state is exactly that closed state and no
        application bytes were produced by this step, so callers can safely
        stop retrying and release the transport (e.g. via [abort]) instead of
        looping until fuel is exhausted.
      **)
      (obs.client_receive_observed_status == DriverWorkflowClosed ==>
        st_network == st1 /\
        st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
        obs.client_receive_observed_response.CT.response.CT.app_out_len == 0sz)

noextract
let client_driver_receive_status_correct
  (result:client_receive_result)
  (obs:client_receive_observation)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  let resp = obs.client_receive_observed_response.CT.response in
  if obs.client_receive_observed_status == DriverWorkflowOk then
    if SZ.v resp.CT.app_out_len <= B.length out_bytes /\
       SZ.v resp.CT.app_out_len <= B.length app_out
    then
      result.client_receive_status == DriverWorkflowOk /\
      result.client_receive_len == resp.CT.app_out_len
    else
      result.client_receive_status == DriverWorkflowStepFailed /\
      result.client_receive_len == 0sz
  else
    result.client_receive_status == obs.client_receive_observed_status /\
    result.client_receive_len == 0sz

noextract
let client_driver_receive_copyout_correct
  (result:client_receive_result)
  (resp:CT.client_response)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  if result.client_receive_status == DriverWorkflowOk then
    SZ.v result.client_receive_len <= B.length out_bytes /\
    result.client_receive_len == resp.CT.app_out_len /\
    (if SZ.v result.client_receive_len <= B.length out_bytes then
      Seq.equal
        (Seq.slice out_bytes 0 (SZ.v result.client_receive_len))
        (CT.response_app_out resp app_out)
     else False)
  else
    True

noextract
let client_driver_receive_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (result:client_receive_result)
  (obs:client_receive_observation)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  client_driver_receive_status_correct
    result
    obs
    app_out
    out_bytes /\
  client_receive_observation_network_correct st0 st1 obs app_out /\
  SZ.v result.client_receive_len <= B.length out_bytes /\
  (result.client_receive_status == DriverWorkflowOk ==>
    client_driver_receive_copyout_correct
      result
      obs.client_receive_observed_response.CT.response
      app_out
      out_bytes)

let driver_network_out_capacity : SZ.t = 20000sz
let driver_app_out_capacity : SZ.t = 16640sz
let driver_rx_capacity : SZ.t = 65535sz
let driver_public_key_payload_capacity : SZ.t = 4096sz
let driver_auth_leaf_der_capacity : SZ.t = 32768sz
let driver_certificate_verify_input_capacity : SZ.t = 256sz
let driver_signature_capacity : SZ.t = 4096sz
let driver_server_finished_payload_len : SZ.t = 36sz

let pending_after_consumed (buffered_len consumed_len:SZ.t) : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

noeq type client_driver = {
  client_driver_client: C.client;
  client_driver_progress: MR.mref (EC.client_progress_preorder #CTypes.client_local_event);
  client_driver_initial: Ghost.erased EC.client_initial_state;
  client_driver_auth: O.auth_context;
  client_driver_channel: Box.box (option IO.channel);
  client_driver_tcp_history: MR.mref CI.io_history_preorder;
  client_driver_buffered_len: Box.box SZ.t;
  client_driver_empty_payload: V.vec U8.t;
  client_driver_raw: V.vec U8.t;
  client_driver_network_out: V.vec U8.t;
  client_driver_auth_leaf_der: V.vec U8.t;
  client_driver_auth_payload: V.vec U8.t;
  client_driver_auth_cv_input: V.vec U8.t;
  client_driver_auth_signature: V.vec U8.t;
  client_driver_app_out: V.vec U8.t;
  client_driver_local_app_out: V.vec U8.t;
}

noextract
let client_driver_canonical (d:client_driver) : CP.canonical_client = {
  CP.canonical_client_state = d.client_driver_client;
  CP.canonical_client_progress = d.client_driver_progress;
  CP.canonical_client_initial = d.client_driver_initial;
}

noeq type driver = {
  driver_client: C.client;
  driver_channel: IO.channel;
  driver_tcp_history: MR.mref CI.io_history_preorder;
  driver_progress: MR.mref (EC.client_progress_preorder #CTypes.client_local_event);
  driver_initial: Ghost.erased EC.client_initial_state;
}

let lemma_rejoined_raw_mask_matches_old
  (old_raw raw_prefix:B.bytes)
  (raw_mask raw_prefix_mask raw_joined_mask:Seq.seq (option U8.t))
  (buffered_len:nat)
  : Lemma
    (requires
      Seq.length raw_mask == Seq.length old_raw /\
      Seq.length raw_joined_mask == Seq.length raw_mask /\
      Seq.length raw_prefix_mask == buffered_len /\
      buffered_len <= Seq.length old_raw /\
      Seq.equal raw_prefix (Seq.slice old_raw 0 buffered_len) /\
      (forall (i:nat). i < Seq.length raw_mask ==>
        Seq.index raw_mask i == Some (Seq.index old_raw i)) /\
      (forall (i:nat). i < Seq.length raw_prefix_mask ==>
        Seq.index raw_prefix_mask i == Some (Seq.index raw_prefix i)) /\
      (forall (i:nat). i < Seq.length raw_joined_mask ==>
        Seq.index raw_joined_mask i ==
          (if i < buffered_len
           then Seq.index raw_prefix_mask i
           else Seq.index raw_mask i)))
    (ensures
      forall (i:nat). i < Seq.length raw_joined_mask ==>
        Seq.index raw_joined_mask i == Some (Seq.index old_raw i))
=
  let index_proof
    (i:nat { i < Seq.length raw_joined_mask })
    : Lemma
      (Seq.index raw_joined_mask i == Some (Seq.index old_raw i))
  =
    if i < buffered_len then (
      Seq.lemma_eq_elim raw_prefix (Seq.slice old_raw 0 buffered_len);
      Seq.lemma_index_slice old_raw 0 buffered_len i
    ) else (
      assert (i < Seq.length raw_mask)
    )
  in
  FStar.Classical.forall_intro
    #(i:nat { i < Seq.length raw_joined_mask })
    #(fun i ->
      Seq.index raw_joined_mask i == Some (Seq.index old_raw i))
    index_proof

noextract
let logged_received_bytes_accounted
  (logged:B.bytes)
  (consumed:B.bytes)
  : prop =
  B.length logged <= B.length consumed /\
  (forall b. SeqP.count b logged <= SeqP.count b consumed)

let lemma_empty_received_bytes_accounted ()
  : Lemma (logged_received_bytes_accounted B.empty B.empty)
=
  ()

noextract
let client_driver_wire_logs_match_witness
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  B.length buffered == SZ.v buffered_len /\
  Seq.equal (B.append consumed buffered) received /\
  logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed /\
  (CT.connection_control_not_failed st ==>
    Seq.equal st.CS.cs_wire_log.CL.raw_received consumed)

noextract
let client_driver_wire_logs_match
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop =
  exists consumed.
    client_driver_wire_logs_match_witness
      st
      received
      sent
      consumed
      buffered
      buffered_len

let choose_wire_logs_match_witness
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Ghost (Ghost.erased B.bytes)
      (requires
        client_driver_wire_logs_match
          st received sent buffered buffered_len)
      (ensures fun consumed ->
        client_driver_wire_logs_match_witness
          st
          received
          sent
          (Ghost.reveal consumed)
          buffered
          buffered_len)
=
  assert_norm (
    client_driver_wire_logs_match
      st received sent buffered buffered_len ==
    (exists consumed.
      client_driver_wire_logs_match_witness
        st received sent consumed buffered buffered_len));
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          st received sent consumed buffered buffered_len) in
  Ghost.hide consumed

ghost fn establish_initial_wire_logs_match
  (cfg:CS.connection_config{
    cfg.CS.config_role == CS.ClientEndpoint
  })
  requires emp
  ensures pure (
    client_driver_wire_logs_match
      (CS.initial cfg)
      B.empty
      B.empty
      B.empty
      0sz /\
    CT.client_state_correct (CS.initial cfg) /\
    CT.client_end_to_end_invariant (CS.initial cfg))
{
  lemma_empty_received_bytes_accounted ();
  assert (pure (client_driver_wire_logs_match_witness
    (CS.initial cfg)
    B.empty
    B.empty
    B.empty
    B.empty
    0sz));
  CT.lemma_initial_client_end_to_end_invariant cfg;
  assert (pure (client_driver_wire_logs_match
    (CS.initial cfg)
    B.empty
    B.empty
    B.empty
    0sz));
  assert (pure (
    client_driver_wire_logs_match
      (CS.initial cfg)
      B.empty
      B.empty
      B.empty
      0sz /\
    CT.client_state_correct (CS.initial cfg) /\
    CT.client_end_to_end_invariant (CS.initial cfg)))
}

let lemma_logged_received_bytes_accounted_transport
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted st.CS.cs_wire_log.CL.raw_received consumed /\
        Seq.equal (B.append consumed buffered) received)
      (ensures
        B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
        (forall b.
          SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
          SeqP.count b received))
=
  Seq.lemma_len_append consumed buffered;
  Seq.lemma_eq_elim (B.append consumed buffered) received;
  SeqP.lemma_append_count consumed buffered

let lemma_client_driver_wire_logs_match_received_accounted
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires client_driver_wire_logs_match st received sent buffered buffered_len)
      (ensures
        B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
        (forall b.
          SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
          SeqP.count b received))
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          st
          received
          sent
          consumed
          buffered
          buffered_len) in
  assert (client_driver_wire_logs_match_witness
    st
    received
    sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  lemma_logged_received_bytes_accounted_transport st received (Ghost.reveal consumed) buffered

noextract
let wire_history (received sent:B.bytes) : IO.history =
  { IO.tcp_received = received; IO.tcp_sent = sent }

noextract
let channel_open
  (hist:MR.mref CI.io_history_preorder)
  (ch:IO.channel)
  (st:TLS13.Spec.StateMachine.connection_state)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  exists* received sent.
    IO.is_channel ch received sent **
    MR.pts_to hist #1.0R (wire_history received sent) **
    pure (client_driver_wire_logs_match st received sent buffered buffered_len)

(** After a physical [IO.read] appends [chunk] to the received history, the
    monotonic ghost TCP-history tracker advances accordingly. The step is
    justified because appending only extends the physical receive history. *)
ghost
fn tcp_history_note_read
  (hist:MR.mref CI.io_history_preorder)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (chunk:Ghost.erased B.bytes)
  requires MR.pts_to hist #1.0R (wire_history received sent)
  ensures MR.pts_to hist #1.0R (wire_history (Seq.append received chunk) sent)
{
  CPI.lemma_bytes_extends_append received chunk;
  CPI.lemma_bytes_extends_refl sent;
  CI.lemma_io_history_preorder_of_extends
    (wire_history received sent)
    (wire_history (Seq.append received chunk) sent);
  MR.update hist (wire_history (Seq.append received chunk) sent)
}

(** After a physical [IO.write] appends [chunk] to the sent history, the
    monotonic ghost TCP-history tracker advances accordingly. *)
ghost
fn tcp_history_note_write
  (hist:MR.mref CI.io_history_preorder)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (chunk:Ghost.erased B.bytes)
  requires MR.pts_to hist #1.0R (wire_history received sent)
  ensures MR.pts_to hist #1.0R (wire_history received (Seq.append sent chunk))
{
  CPI.lemma_bytes_extends_refl received;
  CPI.lemma_bytes_extends_append sent chunk;
  CI.lemma_io_history_preorder_of_extends
    (wire_history received sent)
    (wire_history received (Seq.append sent chunk));
  MR.update hist (wire_history received (Seq.append sent chunk))
}

noextract
let driver_canonical_progress
  (d:driver)
  (st:CS.connection_state)
  : slprop =
  MR.pts_to
    d.driver_progress
    #1.0R
    st **
  MR.snapshot
    d.driver_progress
    (Ghost.reveal d.driver_initial) **
  pure (
    CT.client_end_to_end_invariant st /\
    st.CS.cs_model.CS.model_config ==
      (Ghost.reveal d.driver_initial).CS.cs_model.CS.model_config /\
    CP.client_initial_wire_logs_empty (Ghost.reveal d.driver_initial))

noextract
let driver_exactly
  (d:driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  C.connection_exactly d.driver_client st **
  driver_canonical_progress d st **
  channel_open d.driver_tcp_history d.driver_channel st buffered buffered_len

noeq type top_driver = {
  top_driver_core: driver;
  top_driver_auth: O.auth_context;
}

let no_channel : option IO.channel = None

noextract
let top_driver_exactly
  (d:top_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  driver_exactly d.top_driver_core st buffered buffered_len **
  O.is_auth_context d.top_driver_auth

noextract
let client_driver_buffers
  (d:client_driver)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  Box.pts_to d.client_driver_buffered_len buffered_len **
  exists* empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
    V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.client_driver_raw #1.0R raw **
    V.pts_to d.client_driver_network_out #1.0R network_out **
    V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
    V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
    V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
    V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
    V.pts_to d.client_driver_app_out #1.0R app_out **
    V.pts_to d.client_driver_local_app_out #1.0R local_app_out **
    pure (
      B.length empty_payload == 0 /\
      B.length raw == SZ.v driver_rx_capacity /\
      B.length buffered == SZ.v buffered_len /\
      SZ.v buffered_len <= SZ.v driver_rx_capacity /\
      Seq.equal buffered (Seq.slice raw 0 (SZ.v buffered_len)) /\
      B.length network_out == SZ.v driver_network_out_capacity /\
      B.length auth_leaf_der == SZ.v driver_auth_leaf_der_capacity /\
      B.length auth_payload == SZ.v driver_public_key_payload_capacity /\
      B.length auth_cv_input == SZ.v driver_certificate_verify_input_capacity /\
      B.length auth_signature == SZ.v driver_signature_capacity /\
      B.length app_out == SZ.v driver_app_out_capacity /\
      B.length local_app_out == SZ.v driver_app_out_capacity /\
      Bounds.max_handshake_flight_len <= SZ.v driver_auth_leaf_der_capacity /\
      SZ.v driver_public_key_payload_capacity <= Bounds.max_public_key_len /\
      Bounds.max_certificate_verify_input_len <= SZ.v driver_certificate_verify_input_capacity /\
      L.max_signature_len <= SZ.v driver_signature_capacity /\
      L.max_record_fragment_len <= SZ.v driver_app_out_capacity /\
      V.is_full_vec d.client_driver_empty_payload /\
      V.is_full_vec d.client_driver_raw /\
      V.is_full_vec d.client_driver_network_out /\
      V.is_full_vec d.client_driver_auth_leaf_der /\
      V.is_full_vec d.client_driver_auth_payload /\
      V.is_full_vec d.client_driver_auth_cv_input /\
      V.is_full_vec d.client_driver_auth_signature /\
      V.is_full_vec d.client_driver_app_out /\
      V.is_full_vec d.client_driver_local_app_out)

noextract
let client_driver_canonical_progress
  (d:client_driver)
  (st:CS.connection_state)
  : slprop =
  MR.pts_to
    d.client_driver_progress
    #1.0R
    st **
  MR.snapshot
    d.client_driver_progress
    (Ghost.reveal d.client_driver_initial) **
  pure (
    CT.client_end_to_end_invariant st /\
    st.CS.cs_model.CS.model_config ==
      (Ghost.reveal d.client_driver_initial).CS.cs_model.CS.model_config /\
    CP.client_initial_wire_logs_empty
      (Ghost.reveal d.client_driver_initial))

noextract
let client_driver_live
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  client_driver_canonical_progress d st **
  O.is_auth_context d.client_driver_auth **
  Box.pts_to d.client_driver_channel no_channel **
  MR.pts_to d.client_driver_tcp_history #1.0R (wire_history B.empty B.empty) **
  client_driver_buffers d B.empty 0sz **
  pure (client_driver_wire_logs_match st B.empty B.empty B.empty 0sz /\
        st == Ghost.reveal d.client_driver_initial /\
        CP.client_invariant_pure
          (Ghost.reveal d.client_driver_initial)
          B.empty
          B.empty
          st /\
        CT.client_end_to_end_invariant st)

noextract
let client_driver_connected
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  client_driver_canonical_progress d st **
  O.is_auth_context d.client_driver_auth **
  exists* ch buffered buffered_len.
    Box.pts_to d.client_driver_channel (Some ch) **
    IO.is_channel ch received sent **
    MR.pts_to d.client_driver_tcp_history #1.0R (wire_history received sent) **
    client_driver_buffers d buffered buffered_len **
    pure (client_driver_wire_logs_match st received sent buffered buffered_len)

noextract
let client_channel_terminal
  (d:client_driver)
  (wire_received:B.bytes)
  (wire_sent:B.bytes)
  (app_log:CI.application_log B.bytes)
  : slprop =
  exists* st ch buffered buffered_len.
    CP.client_invariant
      (client_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st **
    O.is_auth_context d.client_driver_auth **
    Box.pts_to d.client_driver_channel (Some ch) **
    IO.is_channel ch wire_received wire_sent **
    MR.pts_to d.client_driver_tcp_history #1.0R (wire_history wire_received wire_sent) **
    client_driver_buffers d buffered buffered_len **
    pure (
      client_driver_wire_logs_match
        st
        wire_received
        wire_sent
        buffered
        buffered_len /\
      app_log == TChannel.application_log st)

let client_channel_inv
  (d:client_driver)
  (wire_received:B.bytes)
  (wire_sent:B.bytes)
  (pending:B.bytes)
  (app_log:CI.application_log B.bytes)
  : slprop =
  exists* st ch buffered buffered_len.
    CP.client_invariant
      (client_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st **
    O.is_auth_context d.client_driver_auth **
    Box.pts_to d.client_driver_channel (Some ch) **
    IO.is_channel ch wire_received wire_sent **
    MR.pts_to d.client_driver_tcp_history #1.0R (wire_history wire_received wire_sent) **
    client_driver_buffers d buffered buffered_len **
    pure (
      client_driver_wire_logs_match
        st
        wire_received
        wire_sent
        buffered
        buffered_len /\
      CT.connection_control_not_failed st /\
      Seq.equal pending buffered /\
      Seq.equal
        wire_received
        (B.append st.CS.cs_wire_log.CL.raw_received pending) /\
      Seq.equal wire_sent st.CS.cs_wire_log.CL.raw_sent /\
      app_log == TChannel.application_log st)

noextract
let client_channel_snapshot
  (d:client_driver)
  (wire_received:B.bytes)
  (wire_sent:B.bytes)
  (app_log:CI.application_log B.bytes)
  : slprop =
  exists* st.
    CP.client_snapshot
      (client_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st **
    MR.snapshot
      d.client_driver_tcp_history
      (wire_history wire_received wire_sent) **
    pure (app_log == TChannel.application_log st)

noextract
let client_driver_closed
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  client_driver_canonical_progress d st **
  (exists* h. MR.pts_to d.client_driver_tcp_history #1.0R h)

let lemma_client_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        client_driver_wire_logs_match st received sent buffered buffered_len /\
        CT.connection_control_not_failed st)
      (ensures client_driver_received_log_exact_prefix st received)
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          st
          received
          sent
          consumed
          buffered
          buffered_len) in
  assert (client_driver_wire_logs_match_witness
    st
    received
    sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (Seq.equal st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed));
  assert (Seq.equal (B.append (Ghost.reveal consumed) buffered) received);
  Seq.lemma_eq_elim st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed);
  Seq.lemma_eq_elim (B.append st.CS.cs_wire_log.CL.raw_received buffered) received;
  assert (Seq.equal received (B.append st.CS.cs_wire_log.CL.raw_received buffered));
  FStar.Classical.exists_intro
    (fun retained ->
      Seq.equal received
        (B.append st.CS.cs_wire_log.CL.raw_received retained))
    buffered

let lemma_client_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        client_driver_wire_logs_match st received sent buffered buffered_len /\
        CT.connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures client_driver_received_no_read_ahead st received)
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          st
          received
          sent
          consumed
          buffered
          buffered_len) in
  assert (client_driver_wire_logs_match_witness
    st
    received
    sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (Seq.equal st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed));
  assert (Seq.equal (B.append (Ghost.reveal consumed) buffered) received);
  Seq.lemma_len_append (Ghost.reveal consumed) buffered;
  Seq.lemma_eq_elim st.CS.cs_wire_log.CL.raw_received (Ghost.reveal consumed);
  Seq.lemma_eq_elim (B.append st.CS.cs_wire_log.CL.raw_received buffered) received;
  assert (B.length buffered == 0);
  Seq.lemma_eq_intro buffered B.empty;
  Seq.lemma_eq_elim buffered B.empty;
  Seq.append_empty_r st.CS.cs_wire_log.CL.raw_received;
  assert (B.length received == B.length st.CS.cs_wire_log.CL.raw_received)

type local_write_result = {
  local_write_resp: CT.client_response;
  local_write_written: SZ.t;
}

noeq type network_read_result = {
  network_read_len: SZ.t;
  network_read_buffer_resp: CT.client_buffer_response;
  network_read_written: SZ.t;
  network_read_prefix: Ghost.erased B.bytes;
}

noeq type buffered_network_result = {
  buffered_network_read: network_read_result;
  buffered_network_new_len: SZ.t;
}

noeq type buffered_network_io_result = {
  buffered_network_io_read_len: SZ.t;
  buffered_network_io_buffered: buffered_network_result;
}

noeq type buffered_network_loop_result = {
  buffered_network_loop_last: buffered_network_result;
  buffered_network_loop_exhausted: bool;
}

type ready_local_action_result = {
  ready_local_action: CT.next_local_action;
  ready_local_processed: bool;
  ready_local_resp: CT.client_response;
  ready_local_written: SZ.t;
}

let lemma_ready_local_action_result_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (result:ready_local_action_result)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        (result.ready_local_processed ==>
          CT.local_event_end_to_end_correct
            st0
            st1
            result.ready_local_resp
            result.ready_local_action.CT.next_local_kind
            payload
            network_out
            app_out) /\
        (result.ready_local_processed == false ==> st1 == st0))
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  if result.ready_local_processed then
    CT.lemma_local_event_end_to_end_correct_preserves_config
      st0
      st1
      result.ready_local_resp
      result.ready_local_action.CT.next_local_kind
      payload
      network_out
      app_out
  else
    assert (st1 == st0)

type driver_drain_result = {
  driver_drain_last: ready_local_action_result;
  driver_drain_exhausted: bool;
}

noeq type driver_workflow_result = {
  driver_workflow_status: driver_workflow_status;
  driver_workflow_rx_len: SZ.t;
  driver_workflow_local: driver_drain_result;
  driver_workflow_network: buffered_network_io_result;
}

noextract
let client_driver_workflow_observation
  (result:driver_workflow_result)
  : client_receive_observation =
  {
    client_receive_observed_status = result.driver_workflow_status;
    client_receive_observed_response =
      result.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp;
  }

noextract
let client_buffered_network_io_step_correct
  (st1:CS.connection_state)
  (result:buffered_network_io_result)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  : prop =
  exists st_before input old_network_out old_app_out.
    CT.network_bytes_end_to_end_correct
      st_before
      st1
      result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      input
      old_network_out
      network_out_bytes
      old_app_out
      app_out_bytes

let lemma_client_receive_observation_network_correct_from_buffered
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (st_network:CS.connection_state)
  (result:driver_workflow_result)
  (network_out_bytes:B.bytes)
  (observed_app_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  : Lemma
      (requires
        result.driver_workflow_status <> DriverWorkflowExhausted /\
        (result.driver_workflow_status == DriverWorkflowOk ==>
          st_network == st1 /\ Seq.equal observed_app_out_bytes app_out_bytes) /\
        (result.driver_workflow_status == DriverWorkflowClosed ==>
          st_network == st1 /\
          st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
          result.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len == 0sz) /\
        client_buffered_network_io_step_correct
          st_network
          result.driver_workflow_network
          network_out_bytes
          observed_app_out_bytes)
      (ensures
        client_receive_observation_network_correct
          st0
          st1
          (client_driver_workflow_observation result)
          app_out_bytes)
=
  let network = result.driver_workflow_network in
  assert (exists st_before input old_network_out old_app_out.
    CT.network_bytes_end_to_end_correct
      st_before
      st_network
      network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      input
      old_network_out
      network_out_bytes
      old_app_out
      observed_app_out_bytes);
  let st_before =
    ID.indefinite_description_ghost
      CS.connection_state
      (fun st_before -> exists input old_network_out old_app_out.
        CT.network_bytes_end_to_end_correct
          st_before
          st_network
          network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input
          old_network_out
          network_out_bytes
          old_app_out
          observed_app_out_bytes) in
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists old_network_out old_app_out.
        CT.network_bytes_end_to_end_correct
          st_before
          st_network
          network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input
          old_network_out
          network_out_bytes
          old_app_out
          observed_app_out_bytes) in
  let old_network_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun old_network_out -> exists old_app_out.
        CT.network_bytes_end_to_end_correct
          st_before
          st_network
          network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input
          old_network_out
          network_out_bytes
          old_app_out
          observed_app_out_bytes) in
  let old_app_out =
    ID.indefinite_description_ghost
      B.bytes
      (fun old_app_out ->
        CT.network_bytes_end_to_end_correct
          st_before
          st_network
          network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
          input
          old_network_out
          network_out_bytes
          old_app_out
          observed_app_out_bytes) in
  assert (CT.network_bytes_end_to_end_correct
    st_before
    st_network
    network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
    input
    old_network_out
    network_out_bytes
    old_app_out
    observed_app_out_bytes);
  assert ((client_driver_workflow_observation result).client_receive_observed_status ==
    result.driver_workflow_status);
  assert ((client_driver_workflow_observation result).client_receive_observed_response ==
    network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp);
  assert (exists st_network st_before input old_network_out network_out old_app_out observed_app_out.
    CT.network_bytes_end_to_end_correct
      st_before
      st_network
      (client_driver_workflow_observation result).client_receive_observed_response
      input
      old_network_out
      network_out
      old_app_out
      observed_app_out /\
    ((client_driver_workflow_observation result).client_receive_observed_status ==
      DriverWorkflowOk ==>
      st_network == st1 /\ Seq.equal observed_app_out app_out_bytes) /\
    ((client_driver_workflow_observation result).client_receive_observed_status ==
      DriverWorkflowClosed ==>
      st_network == st1 /\
      st1.CS.cs_model.CS.model_control == CS.ControlClosed /\
      (client_driver_workflow_observation result).client_receive_observed_response.CT.response.CT.app_out_len == 0sz))

noextract
let internal_local_action_kind
  (kind:CT.local_event_kind)
  : prop =
  match kind with
  | CT.LocalValidateCertificate
  | CT.LocalVerifyCertificateSignature ->
    False
  | _ ->
    True

let lemma_ready_internal_action_empty_payload_wf
  (st:TLS13.Spec.StateMachine.connection_state)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (action:CT.next_local_action)
  (payload:B.bytes)
  : Lemma
      (requires C.next_local_action_sound
                  st
                  network_out_len
                  certificate_public_key_len
                  server_finished_payload_len
                  action /\
                action.CT.next_local_ready == true /\
                internal_local_action_kind action.CT.next_local_kind /\
                Seq.equal payload B.empty)
      (ensures CT.local_input_wf st action.CT.next_local_kind payload)
=
  assert (C.next_local_action_internal_input_ready st action);
  match action.CT.next_local_kind with
  | CT.LocalValidateCertificate ->
    assert False
  | CT.LocalVerifyCertificateSignature ->
    assert False
  | CT.LocalVerifyFinished ->
    ()
  | CT.LocalDeliverApplicationData ->
    assert False
  | CT.LocalSendApplicationData ->
    assert False
  | CT.LocalSendCloseNotify ->
    assert False
  | CT.LocalFail ->
    assert False
  | _ ->
    ()

let lemma_response_network_out_len
  (resp:CT.client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires CT.response_wf resp network_out app_out)
      (ensures B.length (CT.response_network_out resp network_out) ==
        SZ.v resp.CT.network_out_len)
=
  assert (SZ.v resp.CT.network_out_len <= B.length network_out);
  Seq.lemma_len_slice network_out 0 (SZ.v resp.CT.network_out_len)

let lemma_logged_received_bytes_accounted_append_delta
  (old_logged:B.bytes)
  (old_consumed:B.bytes)
  (raw_delta:B.bytes)
  (consumed_delta:B.bytes)
  : Lemma
      (requires
        logged_received_bytes_accounted old_logged old_consumed /\
        (Seq.equal raw_delta B.empty \/ Seq.equal raw_delta consumed_delta))
      (ensures
        logged_received_bytes_accounted
          (B.append old_logged raw_delta)
          (B.append old_consumed consumed_delta))
=
  Seq.lemma_len_append old_logged raw_delta;
  Seq.lemma_len_append old_consumed consumed_delta;
  SeqP.lemma_append_count old_logged raw_delta;
  SeqP.lemma_append_count old_consumed consumed_delta;
  if Seq.equal raw_delta B.empty then (
    Seq.lemma_eq_elim raw_delta B.empty
  ) else (
    Seq.lemma_eq_elim raw_delta consumed_delta
  )

let lemma_slice_append_full
  (s:B.bytes)
  (n:nat)
  : Lemma
      (requires n <= B.length s)
      (ensures Seq.equal (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) s)
=
  Seq.lemma_len_slice s 0 n;
  Seq.lemma_len_slice s n (B.length s);
  Seq.lemma_len_append (Seq.slice s 0 n) (Seq.slice s n (B.length s));
  assert (B.length (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) == B.length s);
  assert (forall (i:nat). i < B.length (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) ==>
    Seq.index (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) i == Seq.index s i);
  Seq.lemma_eq_intro (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) s

let lemma_legal_response_for_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires CT.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + B.length raw_sent /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received + B.length raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          (B.append st0.CS.cs_wire_log.CL.raw_received raw_received))
=
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (st1.CS.cs_wire_log == {
    CL.raw_sent = B.append st0.CS.cs_wire_log.CL.raw_sent raw_sent;
    CL.raw_received = B.append st0.CS.cs_wire_log.CL.raw_received raw_received;
  });
  Seq.lemma_len_append st0.CS.cs_wire_log.CL.raw_sent raw_sent;
  Seq.lemma_len_append st0.CS.cs_wire_log.CL.raw_received raw_received

let lemma_local_event_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires CT.local_event_end_to_end_correct
        st0 st1 resp kind payload network_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent + SZ.v resp.CT.network_out_len /\
        B.length st1.CS.cs_wire_log.CL.raw_received ==
          B.length st0.CS.cs_wire_log.CL.raw_received /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (CT.response_network_out resp network_out)) /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received)
=
  assert (CT.local_event_step_correct st0 st1 resp kind payload network_out app_out);
  assert (CT.legal_handled_local_response st0 st1 resp kind payload network_out app_out);
  if (exists ev raw_sent raw_received.
        CT.legal_local_response
          st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) then (
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (CT.legal_local_response
      st0 st1 resp kind payload ev raw_sent raw_received network_out app_out);
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CS.event_raw_delta_legal st0.CS.cs_model ev raw_sent raw_received);
    assert (CT.local_event_kind_matches st0 kind payload ev);
    (match ev with
     | CS.ConnLocalEvent _ ->
       assert (Seq.equal raw_received B.empty)
     | CS.ConnNetworkEvent msg ->
       (match msg.CL.message_direction with
        | CL.Sent ->
          assert (Seq.equal raw_received B.empty)
        | CL.Received ->
          (match kind with
           | CT.LocalSendApplicationData
           | CT.LocalSendClientHello
           | CT.LocalSendClientFinished
           | CT.LocalSendCloseNotify
           | CT.LocalSendKeyUpdate ->
             assert (msg.CL.message_direction == CL.Sent);
             assert False
           | _ ->
             assert False)));
    assert (Seq.equal raw_received B.empty);
    Seq.lemma_eq_elim raw_received B.empty;
    lemma_response_network_out_len resp network_out app_out;
    assert (Seq.equal raw_sent (CT.response_network_out resp network_out));
    Seq.lemma_eq_elim raw_sent (CT.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out;
    lemma_response_network_out_len resp network_out app_out;
    assert (Seq.equal B.empty (CT.response_network_out resp network_out));
    Seq.lemma_eq_elim B.empty (CT.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  ) else (
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error))
      B.empty
      B.empty
      network_out
      app_out;
    lemma_response_network_out_len resp network_out app_out;
    assert (Seq.equal B.empty (CT.response_network_out resp network_out));
    Seq.lemma_eq_elim B.empty (CT.response_network_out resp network_out);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  )

let lemma_local_event_received_exact_when_nonfailed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:CT.client_response)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (received:B.bytes)
  (sent:B.bytes)
  (consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0 st1 resp kind payload network_out app_out /\
        client_driver_wire_logs_match_witness
          st0 received sent consumed buffered buffered_len)
      (ensures
        CT.connection_control_not_failed st1 ==>
          Seq.equal st1.CS.cs_wire_log.CL.raw_received consumed)
=
  if CT.connection_control_not_failed st1 then (
    assert (CT.local_event_step_correct st0 st1 resp kind payload network_out app_out);
    assert (CT.legal_handled_local_response st0 st1 resp kind payload network_out app_out);
    if (exists ev raw_sent raw_received.
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) then (
      let ev =
        ID.indefinite_description_ghost
          CS.conn_event
          (fun ev -> exists raw_sent raw_received.
            CT.legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      let raw_sent =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_sent -> exists raw_received.
            CT.legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      let raw_received =
        ID.indefinite_description_ghost
          B.bytes
          (fun raw_received ->
            CT.legal_local_response
              st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
      assert (CT.legal_response_for_event
        st0 st1 resp ev raw_sent raw_received network_out app_out);
      CT.lemma_legal_response_for_event_nonfailed_previous
        st0
        st1
        resp
        ev
        raw_sent
        raw_received
        network_out
        app_out;
      assert (CT.connection_control_not_failed st0);
      assert (Seq.equal st0.CS.cs_wire_log.CL.raw_received consumed);
      lemma_local_event_wire_lengths
        st0
        st1
        resp
        kind
        payload
        network_out
        app_out;
      Seq.lemma_eq_elim st1.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received
    ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
      CT.lemma_unexpected_message_response_control_failed
        st0
        st1
        resp
        network_out
        app_out;
      CT.lemma_connection_control_not_failed_contradicts_failed
        st1
        CT.tls_unexpected_message_error
    ) else (
      assert (CT.bad_finished_response st0 st1 resp network_out app_out);
      CT.lemma_bad_finished_response_control_failed
        st0
        st1
        resp
        network_out
        app_out;
      CT.lemma_connection_control_not_failed_contradicts_failed
        st1
        CT.tls_bad_finished_error
    )
  )

let lemma_network_bytes_wire_lengths
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires CT.network_bytes_end_to_end_correct
        st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out)
      (ensures
        B.length st1.CS.cs_wire_log.CL.raw_sent ==
          B.length st0.CS.cs_wire_log.CL.raw_sent +
          SZ.v buffer_resp.CT.response.CT.network_out_len /\
        B.length st1.CS.cs_wire_log.CL.raw_received <=
          B.length st0.CS.cs_wire_log.CL.raw_received +
          SZ.v buffer_resp.CT.consumed_len /\
        Seq.equal st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (CT.response_network_out buffer_resp.CT.response network_out)))
=
  let resp = buffer_resp.CT.response in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out);
  if CT.response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out then (
    assert (st1 == st0);
    assert (resp.CT.network_out_len == 0sz)
  ) else (
    assert (SZ.v buffer_resp.CT.consumed_len <= B.length network_input);
    assert (CT.some_legal_response_for_network_prefix
      st0 st1 resp network_input buffer_resp.CT.consumed_len network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (CT.raw_received_matches_network_input
      raw_received
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len));
    lemma_legal_response_for_event_wire_lengths
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    lemma_response_network_out_len resp network_out app_out;
    assert (Seq.equal raw_sent (CT.response_network_out resp network_out));
    Seq.lemma_eq_elim raw_sent (CT.response_network_out resp network_out);
    if Seq.equal raw_received B.empty then (
      Seq.lemma_eq_elim raw_received B.empty
    ) else (
      assert (Seq.equal raw_received
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len));
      Seq.lemma_eq_elim raw_received
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len);
      Seq.lemma_len_slice network_input 0 (SZ.v buffer_resp.CT.consumed_len)
    )
  )

let lemma_network_bytes_logged_received_accounted
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  (old_consumed:B.bytes)
  : Lemma
      (requires
        CT.network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out /\
        logged_received_bytes_accounted
          st0.CS.cs_wire_log.CL.raw_received
          old_consumed)
      (ensures
        logged_received_bytes_accounted
          st1.CS.cs_wire_log.CL.raw_received
          (B.append old_consumed
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)))
=
  let resp = buffer_resp.CT.response in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out);
  if CT.response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out then (
    assert (st1 == st0);
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received;
    lemma_logged_received_bytes_accounted_append_delta
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      B.empty
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
  ) else (
    assert (CT.some_legal_response_for_network_prefix
      st0 st1 resp network_input buffer_resp.CT.consumed_len network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (CT.raw_received_matches_network_input
      raw_received
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len));
    lemma_legal_response_for_event_wire_lengths
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    if Seq.equal raw_received B.empty then (
      Seq.lemma_eq_elim raw_received B.empty
    ) else (
      Seq.lemma_eq_elim raw_received
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
    );
    lemma_logged_received_bytes_accounted_append_delta
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      raw_received
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
  )

let lemma_network_bytes_zero_consumed_raw_received_unchanged
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        CT.network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          network_input
          old_network_out
          network_out
          old_app_out
          app_out /\
        buffer_resp.CT.consumed_len == 0sz)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received)
=
  let resp = buffer_resp.CT.response in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp network_input old_network_out network_out old_app_out app_out);
  if CT.response_stuttered st0 st1 resp old_network_out network_out old_app_out app_out then (
    assert (st1 == st0)
  ) else (
    assert (CT.some_legal_response_for_network_prefix
      st0 st1 resp network_input buffer_resp.CT.consumed_len network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out /\
          CT.raw_received_matches_network_input
            raw_received
            (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)) in
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    assert (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len ==
      Seq.slice network_input 0 0);
    Seq.lemma_len_slice network_input 0 0;
    Seq.lemma_eq_intro
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
      B.empty;
    assert (Seq.equal
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
      B.empty);
    assert (CT.raw_received_matches_network_input
      raw_received
      (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len));
    if Seq.equal raw_received B.empty then (
      Seq.lemma_eq_elim raw_received B.empty
    ) else (
      assert (Seq.equal raw_received
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len));
      Seq.lemma_eq_elim raw_received
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len);
      Seq.lemma_eq_elim
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
        B.empty
    );
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      ev
      raw_sent
      raw_received
      network_out
      app_out;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  )

let lemma_network_bytes_logged_received_exact_when_nonfailed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input:B.bytes)
  (old_network_out:B.bytes)
  (network_out:B.bytes)
  (old_app_out:B.bytes)
  (app_out:B.bytes)
  (received:B.bytes)
  (sent:B.bytes)
  (old_consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        client_driver_wire_logs_match_witness
          st0
          received
          sent
          old_consumed
          buffered
          buffered_len /\
        CT.network_bytes_end_to_end_correct
          st0
          st1
          buffer_resp
          network_input
          old_network_out
          network_out
          old_app_out
          app_out)
      (ensures
        CT.connection_control_not_failed st1 ==>
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_received
            (B.append old_consumed
              (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)))
=
  if CT.connection_control_not_failed st1 then (
    CT.lemma_network_bytes_end_to_end_nonfailed_previous
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out;
    assert (CT.connection_control_not_failed st0);
    assert (Seq.equal st0.CS.cs_wire_log.CL.raw_received old_consumed);
    CT.lemma_network_bytes_end_to_end_nonfailed_received_prefix_accepted
      st0
      st1
      buffer_resp
      network_input
      old_network_out
      network_out
      old_app_out
      app_out;
    if buffer_resp.CT.consumed_len == 0sz then (
      lemma_network_bytes_zero_consumed_raw_received_unchanged
        st0
        st1
        buffer_resp
        network_input
        old_network_out
        network_out
        old_app_out
        app_out;
      assert (Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        st0.CS.cs_wire_log.CL.raw_received);
      Seq.lemma_eq_elim st0.CS.cs_wire_log.CL.raw_received old_consumed;
      assert (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len ==
        Seq.slice network_input 0 0);
      Seq.lemma_len_slice network_input 0 0;
      Seq.lemma_eq_intro
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
        B.empty;
      Seq.lemma_eq_elim
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
        B.empty;
      Seq.append_empty_r old_consumed
    ) else (
      assert (exists msg.
        CT.legal_received_tls_response
          st0
          st1
          buffer_resp.CT.response
          msg
          (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
          network_out
          app_out);
      let msg =
        ID.indefinite_description_ghost
          M.tls_message
          (fun msg ->
            CT.legal_received_tls_response
              st0
              st1
              buffer_resp.CT.response
              msg
              (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
              network_out
              app_out) in
      let ev = CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = msg;
      } in
      assert (CT.legal_response_for_event
        st0
        st1
        buffer_resp.CT.response
        ev
        B.empty
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
        network_out
        app_out);
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        buffer_resp.CT.response
        ev
        B.empty
        (CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len)
        network_out
        app_out;
      Seq.lemma_eq_elim st0.CS.cs_wire_log.CL.raw_received old_consumed
    )
  )
