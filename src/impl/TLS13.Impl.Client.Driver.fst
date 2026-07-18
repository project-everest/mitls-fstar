module TLS13.Impl.Client.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module A = Pulse.Lib.Array
module C = TLS13.Impl.Client
module CPI = Common.ProtocolImplementation
module CP = TLS13.Impl.Client.CanonicalProtocol
module CQueries = TLS13.Impl.Client.CanonicalQueries
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CQ = TLS13.Impl.ConnectionState.Queries
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Spec.Endpoint.Wire
module EAPI = TLS13.Spec.Endpoint.API
module EC = TLS13.Spec.Endpoint.Client
module EP = TLS13.Impl.Client.Endpoint
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
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
module WFSM = Common.WireFormatStateMachine

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
let client_driver_canonical
  (d:client_driver)
  : CP.canonical_client =
  {
    CP.canonical_client_state = d.client_driver_client;
    CP.canonical_client_progress = d.client_driver_progress;
    CP.canonical_client_initial = d.client_driver_initial;
  }

noextract
let client_driver_endpoint_config
  (_d:client_driver)
  : CQueries.client_next_local_action_config =
  {
    CQueries.client_query_network_out_len = driver_network_out_capacity;
    CQueries.client_query_certificate_public_key_len =
      driver_public_key_payload_capacity;
    CQueries.client_query_server_finished_payload_len =
      driver_server_finished_payload_len;
  }

noextract
let client_driver_endpoint_frame
  (d:client_driver)
  (network_app_out:array U8.t)
  (network_app_out_len:SZ.t)
  (local_payload:array U8.t)
  (local_payload_len:SZ.t)
  (local_app_out:array U8.t)
  (local_app_out_len:SZ.t)
  : EP.client_endpoint_frame =
  {
    EP.client_ep_query = {
      CQueries.client_query_network_app_out = network_app_out;
      CQueries.client_query_network_app_out_len = network_app_out_len;
      CQueries.client_query_local_payload = local_payload;
      CQueries.client_query_local_payload_len = local_payload_len;
      CQueries.client_query_local_app_out = local_app_out;
      CQueries.client_query_local_app_out_len = local_app_out_len;
    };
    EP.client_ep_raw_len = driver_rx_capacity;
    EP.client_ep_raw = d.client_driver_raw;
    EP.client_ep_network_out_len = driver_network_out_capacity;
    EP.client_ep_network_out = d.client_driver_network_out;
    EP.client_ep_auth = d.client_driver_auth;
    EP.client_ep_auth_leaf_der_len = driver_auth_leaf_der_capacity;
    EP.client_ep_auth_leaf_der = d.client_driver_auth_leaf_der;
    EP.client_ep_auth_payload_len = driver_public_key_payload_capacity;
    EP.client_ep_auth_payload = d.client_driver_auth_payload;
    EP.client_ep_auth_cv_input_len =
      driver_certificate_verify_input_capacity;
    EP.client_ep_auth_cv_input = d.client_driver_auth_cv_input;
    EP.client_ep_auth_signature_len = driver_signature_capacity;
    EP.client_ep_auth_signature = d.client_driver_auth_signature;
  }

noextract
let client_driver_endpoint_workflow_frame
  (d:client_driver)
  : EP.client_endpoint_frame =
  client_driver_endpoint_frame
    d
    (V.vec_to_array d.client_driver_app_out)
    driver_app_out_capacity
    (V.vec_to_array d.client_driver_empty_payload)
    0sz
    (V.vec_to_array d.client_driver_local_app_out)
    driver_app_out_capacity

noeq type driver = {
  driver_client: C.client;
  driver_channel: IO.channel;
}

let lemma_read_append_buffer_matches_raw_prefix_index
  (raw_after_read raw raw_tail_after buffered read_chunk:B.bytes)
  (current_len read_len total_len:nat)
  (k:nat { k < total_len })
  : Lemma
    (requires
      B.length buffered == current_len /\
      B.length read_chunk == read_len /\
      B.length raw >= current_len /\
      B.length raw_tail_after >= read_len /\
      B.length raw_after_read >= total_len /\
      total_len == current_len + read_len /\
      Seq.equal buffered (Seq.slice raw 0 current_len) /\
      Seq.equal read_chunk (Seq.slice raw_tail_after 0 read_len) /\
      (forall (i:nat). i < current_len ==>
        Seq.index raw_after_read i == Seq.index raw i) /\
      (forall (i:nat). i < read_len ==>
        Seq.index raw_after_read (current_len + i) ==
        Seq.index raw_tail_after i))
    (ensures
      Seq.index (B.append buffered read_chunk) k ==
      Seq.index (Seq.slice raw_after_read 0 total_len) k)
  =
  Seq.lemma_eq_elim buffered (Seq.slice raw 0 current_len);
  Seq.lemma_eq_elim read_chunk (Seq.slice raw_tail_after 0 read_len);
  Seq.lemma_len_slice raw_after_read 0 total_len;
  if k < current_len then (
    Seq.lemma_index_app1 buffered read_chunk k;
    Seq.lemma_index_slice raw 0 current_len k;
    Seq.lemma_index_slice raw_after_read 0 total_len k
  ) else (
    assert (current_len <= k);
    assert (k - current_len < read_len);
    assert (current_len + (k - current_len) == k);
    Seq.lemma_index_app2 buffered read_chunk k;
    Seq.lemma_index_slice raw_tail_after 0 read_len (k - current_len);
    Seq.lemma_index_slice raw_after_read 0 total_len k
  )

let lemma_read_append_buffer_matches_raw_prefix
  (raw_after_read raw raw_tail_after buffered read_chunk:B.bytes)
  (current_len read_len total_len:nat)
  : Lemma
    (requires
      B.length buffered == current_len /\
      B.length read_chunk == read_len /\
      B.length raw >= current_len /\
      B.length raw_tail_after >= read_len /\
      B.length raw_after_read >= total_len /\
      total_len == current_len + read_len /\
      Seq.equal buffered (Seq.slice raw 0 current_len) /\
      Seq.equal read_chunk (Seq.slice raw_tail_after 0 read_len) /\
      (forall (i:nat). i < current_len ==>
        Seq.index raw_after_read i == Seq.index raw i) /\
      (forall (i:nat). i < read_len ==>
        Seq.index raw_after_read (current_len + i) ==
        Seq.index raw_tail_after i))
    (ensures
      Seq.equal (B.append buffered read_chunk)
        (Seq.slice raw_after_read 0 total_len))
  =
  Seq.lemma_len_append buffered read_chunk;
  Seq.lemma_len_slice raw_after_read 0 total_len;
  let index_proof (k:nat { k < Seq.length (B.append buffered read_chunk) })
    : Lemma
      (Seq.index (B.append buffered read_chunk) k ==
       Seq.index (Seq.slice raw_after_read 0 total_len) k)
    =
    lemma_read_append_buffer_matches_raw_prefix_index
      raw_after_read raw raw_tail_after buffered read_chunk
      current_len read_len total_len k
  in
  FStar.Classical.forall_intro
    #(k:nat { k < Seq.length (B.append buffered read_chunk) })
    #(fun k ->
      Seq.index (B.append buffered read_chunk) k ==
      Seq.index (Seq.slice raw_after_read 0 total_len) k)
    index_proof;
  Seq.lemma_eq_intro
    (B.append buffered read_chunk)
    (Seq.slice raw_after_read 0 total_len)

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
let channel_open
  (ch:IO.channel)
  (st:TLS13.Spec.StateMachine.connection_state)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  exists* received sent.
    IO.is_channel ch received sent **
    pure (client_driver_wire_logs_match st received sent buffered buffered_len)

noextract
let driver_exactly
  (d:driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : slprop =
  C.connection_exactly d.driver_client st **
  channel_open d.driver_channel st buffered buffered_len

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

(**
  Canonical seed carried by every public driver ownership predicate.

  This is deliberately only the initial canonical progress token/snapshot.  The
  existing public driver workflow below still calls the legacy low-level client
  operations directly, so it cannot soundly claim that the monotonic reference is
  at each post-state without routing that step through
  [TLS13.Impl.Client.Endpoint] (or proving the corresponding canonical progress
  lemma at the call site).  Keeping this seed in the public predicates preserves
  the current API resources while making the canonical client identity available
  for the endpoint-owned helpers below.
**)
noextract
let client_driver_canonical_seed
  (d:client_driver)
  : slprop =
  MR.pts_to
    d.client_driver_progress
    #1.0R
    (Ghost.reveal d.client_driver_initial) **
  MR.snapshot
    d.client_driver_progress
    (Ghost.reveal d.client_driver_initial)

noextract
let client_driver_live
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  client_driver_canonical_seed d **
  O.is_auth_context d.client_driver_auth **
  Box.pts_to d.client_driver_channel no_channel **
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
  client_driver_canonical_seed d **
  O.is_auth_context d.client_driver_auth **
  exists* ch buffered buffered_len.
    Box.pts_to d.client_driver_channel (Some ch) **
    IO.is_channel ch received sent **
    client_driver_buffers d buffered buffered_len **
    pure (client_driver_wire_logs_match st received sent buffered buffered_len)

noextract
let client_driver_endpoint_live
  (d:client_driver)
  (st:CS.connection_state)
  : slprop =
  CP.client_invariant (client_driver_canonical d) B.empty B.empty st **
  O.is_auth_context d.client_driver_auth **
  Box.pts_to d.client_driver_channel no_channel **
  client_driver_buffers d B.empty 0sz **
  pure (client_driver_wire_logs_match st B.empty B.empty B.empty 0sz /\
        st == Ghost.reveal d.client_driver_initial)

noextract
let client_driver_endpoint_connected
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (st:TLS13.Spec.StateMachine.connection_state)
  (canonical_received:B.bytes)
  (canonical_sent:B.bytes)
  : slprop =
  CP.client_invariant
    (client_driver_canonical d)
    canonical_received
    canonical_sent
    st **
  exists* ch buffered_len.
    Box.pts_to d.client_driver_channel (Some ch) **
    Box.pts_to d.client_driver_buffered_len buffered_len **
    EP.client_endpoint_frame_ready
      (client_driver_canonical d)
      cfg
      frame
      st **
    EP.client_endpoint_io_ready
      (client_driver_canonical d)
      ch
      frame
      canonical_received
      canonical_sent
      st **
    pure (SZ.v buffered_len <= SZ.v frame.EP.client_ep_raw_len)

noextract
ghost fn client_driver_endpoint_connected_valid_byte_trace
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (canonical_received:Ghost.erased B.bytes)
  (canonical_sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires client_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st)
             (Ghost.reveal canonical_received)
             (Ghost.reveal canonical_sent)
  ensures client_driver_endpoint_connected
            d
            cfg
            frame
            (Ghost.reveal st)
            (Ghost.reveal canonical_received)
            (Ghost.reveal canonical_sent) **
          pure (WFSM.valid_byte_trace
            (EC.client_system #CTypes.client_local_event
              (Ghost.reveal
                (client_driver_canonical d).CP.canonical_client_initial))
            (Ghost.reveal canonical_received)
            (Ghost.reveal st)
            (Ghost.reveal canonical_sent)
            Seq.empty)
{
  unfold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st)
    (Ghost.reveal canonical_received)
    (Ghost.reveal canonical_sent));
  with ch buffered_len. _;
  CP.client_invariant_valid
    (client_driver_canonical d)
    canonical_received
    canonical_sent
    st;
  with ch buffered_len.
  fold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st)
    (Ghost.reveal canonical_received)
    (Ghost.reveal canonical_sent))
}

let lemma_client_local_process_correct_received_unchanged
  (initial:EC.client_initial_state)
  (ev:CTypes.client_local_event)
  (old_out:B.bytes)
  (out_contents:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (result:CPI.process_result)
  (received1:B.bytes)
  (sent1:B.bytes)
  (st1:CS.connection_state)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        CPI.local_process_correct
          (EC.client_system #CTypes.client_local_event initial)
          ev
          old_out
          out_contents
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          wire_outputs
          local_outputs)
      (ensures Seq.equal received1 received0)
=
  match result.CPI.process_status with
  | CPI.StepOk -> ()
  | CPI.NeedMoreInput
  | CPI.ParseFailed ->
    assert False
  | CPI.OutputBufferTooSmall -> ()
  | CPI.DecodeError
  | CPI.IllegalTransition
  | CPI.ConnectionFailed -> ()

let lemma_client_driver_endpoint_local_wire_logs_match
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (canonical_received0:B.bytes)
  (canonical_sent0:B.bytes)
  (canonical_received1:B.bytes)
  (canonical_sent1:B.bytes)
  (transport_received:B.bytes)
  (transport_sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  (ev:CTypes.client_local_event)
  (old_out:B.bytes)
  (out_contents:B.bytes)
  (out_len:SZ.t)
  (result:CPI.process_result)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list EAPI.local_output)
  : Lemma
      (requires
        CP.client_invariant_pure
          initial
          canonical_received0
          canonical_sent0
          st0 /\
        CP.client_invariant_pure
          initial
          canonical_received1
          canonical_sent1
          st1 /\
        CT.connection_control_not_failed st0 /\
        client_driver_wire_logs_match
          st0
          transport_received
          transport_sent
          buffered
          buffered_len /\
        CPI.local_process_correct
          (EC.client_system #CTypes.client_local_event initial)
          ev
          old_out
          out_contents
          out_len
          canonical_received0
          canonical_sent0
          st0
          result
          canonical_received1
          canonical_sent1
          st1
          wire_outputs
          local_outputs)
      (ensures
        client_driver_wire_logs_match
          st1
          transport_received
          canonical_sent1
          buffered
          buffered_len)
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          st0
          transport_received
          transport_sent
          consumed
          buffered
          buffered_len) in
  assert (client_driver_wire_logs_match_witness
    st0
    transport_received
    transport_sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (Seq.equal
    st0.CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed));
  lemma_client_local_process_correct_received_unchanged
    initial
    ev
    old_out
    out_contents
    out_len
    canonical_received0
    canonical_sent0
    st0
    result
    canonical_received1
    canonical_sent1
    st1
    wire_outputs
    local_outputs;
  assert (Seq.equal canonical_received1 canonical_received0);
  assert (Seq.equal canonical_received0 st0.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal canonical_received1 st1.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received canonical_received1);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received);
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    st0.CS.cs_wire_log.CL.raw_received;
  assert (logged_received_bytes_accounted
    st1.CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed));
  assert (client_driver_wire_logs_match_witness
    st1
    transport_received
    canonical_sent1
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (exists consumed1.
    client_driver_wire_logs_match_witness
      st1
      transport_received
      canonical_sent1
      consumed1
      buffered
      buffered_len)

let lemma_client_driver_wire_logs_match_exists
  (st:CS.connection_state)
  (transport_received:B.bytes)
  (transport_sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        client_driver_wire_logs_match
          st
          transport_received
          transport_sent
          buffered
          buffered_len)
      (ensures
        exists buffered'.
          client_driver_wire_logs_match
            st
            transport_received
            transport_sent
            buffered'
            buffered_len)
=
  introduce exists (buffered':B.bytes).
    client_driver_wire_logs_match
      st
      transport_received
      transport_sent
      buffered'
      buffered_len
  with buffered
  and ()

ghost fn expose_client_invariant_pure
  (cc:CP.canonical_client)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
ensures
  CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  pure (CP.client_invariant_pure
    (Ghost.reveal cc.CP.canonical_client_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
{
  unfold (CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  assert (pure (CP.client_invariant_pure
    (Ghost.reveal cc.CP.canonical_client_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  fold (CP.client_invariant
    cc
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

noextract
let client_driver_closed
  (d:client_driver)
  (st:TLS13.Spec.StateMachine.connection_state)
  : slprop =
  C.connection_exactly d.client_driver_client st **
  client_driver_canonical_seed d

ghost fn client_driver_live_to_endpoint_live
  (d:client_driver)
  (st:Ghost.erased CS.connection_state)
  requires client_driver_live d (Ghost.reveal st)
  ensures client_driver_endpoint_live d (Ghost.reveal st)
{
  unfold (client_driver_live d (Ghost.reveal st));
  unfold (client_driver_canonical_seed d);
  assert (pure (Ghost.reveal st == Ghost.reveal d.client_driver_initial));
  fold (CP.client_invariant
    (client_driver_canonical d)
    B.empty
    B.empty
    (Ghost.reveal st));
  fold (client_driver_endpoint_live d (Ghost.reveal st))
}

ghost fn client_driver_endpoint_live_to_live
  (d:client_driver)
  (st:Ghost.erased CS.connection_state)
  requires client_driver_endpoint_live d (Ghost.reveal st)
  ensures client_driver_live d (Ghost.reveal st)
{
  unfold (client_driver_endpoint_live d (Ghost.reveal st));
  unfold (CP.client_invariant
    (client_driver_canonical d)
    B.empty
    B.empty
    (Ghost.reveal st));
  assert (pure (Ghost.reveal st == Ghost.reveal d.client_driver_initial));
  fold (client_driver_canonical_seed d);
  fold (client_driver_live d (Ghost.reveal st))
}

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

fn new_client
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: client_driver
  ensures pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          client_driver_live
            result
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) **
          pure (CT.client_state_correct
            (CR.configured_initial_state
              (Ghost.reveal 'server_name_bytes)
              (Ghost.reveal 'trust_anchors_bytes)
              validation_time_seconds) /\
                CT.client_end_to_end_invariant
                  (CR.configured_initial_state
                    (Ghost.reveal 'server_name_bytes)
                    (Ghost.reveal 'trust_anchors_bytes)
                    validation_time_seconds))
{
  let initial : Ghost.erased EC.client_initial_state = Ghost.hide (
    CR.configured_initial_state
      (Ghost.reveal 'server_name_bytes)
      (Ghost.reveal 'trust_anchors_bytes)
      validation_time_seconds);
  let auth =
    O.auth_context_new
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  let progress =
    MR.alloc #_ #(EC.client_progress_preorder #CTypes.client_local_event) (Ghost.reveal initial);
  MR.take_snapshot progress (Ghost.reveal initial);
  let c =
    C.new_client
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  rewrite
    (CR.connection_exactly
      c
      (Ghost.reveal initial))
    as
    (C.connection_exactly
      c
      (Ghost.reveal initial));
  let channel = Box.alloc no_channel;
  let buffered_len = Box.alloc 0sz;
  let empty_payload = V.alloc 0uy 0sz;
  let raw = V.alloc 0uy driver_rx_capacity;
  let network_out = V.alloc 0uy driver_network_out_capacity;
  let auth_leaf_der = V.alloc 0uy driver_auth_leaf_der_capacity;
  let auth_payload = V.alloc 0uy driver_public_key_payload_capacity;
  let auth_cv_input = V.alloc 0uy driver_certificate_verify_input_capacity;
  let auth_signature = V.alloc 0uy driver_signature_capacity;
  let app_out = V.alloc 0uy driver_app_out_capacity;
  let local_app_out = V.alloc 0uy driver_app_out_capacity;
  assert (pure (Bounds.max_handshake_flight_len <= SZ.v driver_auth_leaf_der_capacity));
  assert (pure (SZ.v driver_public_key_payload_capacity <= Bounds.max_public_key_len));
  assert (pure (Bounds.max_certificate_verify_input_len <= SZ.v driver_certificate_verify_input_capacity));
  assert (pure (L.max_signature_len <= SZ.v driver_signature_capacity));
  assert (pure (L.max_record_fragment_len <= SZ.v driver_app_out_capacity));
  let d = {
    client_driver_client = c;
    client_driver_progress = progress;
    client_driver_initial = initial;
    client_driver_auth = auth;
    client_driver_channel = channel;
    client_driver_buffered_len = buffered_len;
    client_driver_empty_payload = empty_payload;
    client_driver_raw = raw;
        client_driver_network_out = network_out;
        client_driver_auth_leaf_der = auth_leaf_der;
        client_driver_auth_payload = auth_payload;
        client_driver_auth_cv_input = auth_cv_input;
        client_driver_auth_signature = auth_signature;
        client_driver_app_out = app_out;
        client_driver_local_app_out = local_app_out;
      };
      rewrite
         (MR.pts_to progress #1.0R (Ghost.reveal initial))
         as
         (MR.pts_to d.client_driver_progress #1.0R (Ghost.reveal initial));
      rewrite
         (MR.snapshot progress (Ghost.reveal initial))
         as
         (MR.snapshot d.client_driver_progress (Ghost.reveal initial));
      assert (pure (Ghost.reveal d.client_driver_initial == Ghost.reveal initial));
      rewrite
         (MR.pts_to d.client_driver_progress #1.0R (Ghost.reveal initial))
         as
         (MR.pts_to
           d.client_driver_progress
           #1.0R
           (Ghost.reveal d.client_driver_initial));
      rewrite
         (MR.snapshot d.client_driver_progress (Ghost.reveal initial))
         as
         (MR.snapshot
           d.client_driver_progress
           (Ghost.reveal d.client_driver_initial));
      fold (client_driver_canonical_seed d);
      rewrite (Box.pts_to channel no_channel) as
         (Box.pts_to d.client_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.client_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.client_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy))
        as
        (V.pts_to d.client_driver_raw #1.0R (Seq.create (SZ.v driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_network_out #1.0R (Seq.create (SZ.v driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to auth_leaf_der #1.0R (Seq.create (SZ.v driver_auth_leaf_der_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_leaf_der #1.0R (Seq.create (SZ.v driver_auth_leaf_der_capacity) 0uy));
      rewrite
        (V.pts_to auth_payload #1.0R (Seq.create (SZ.v driver_public_key_payload_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_payload #1.0R (Seq.create (SZ.v driver_public_key_payload_capacity) 0uy));
      rewrite
        (V.pts_to auth_cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_cv_input #1.0R (Seq.create (SZ.v driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to auth_signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy))
        as
        (V.pts_to d.client_driver_auth_signature #1.0R (Seq.create (SZ.v driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (V.pts_to local_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.client_driver_local_app_out #1.0R (Seq.create (SZ.v driver_app_out_capacity) 0uy));
      rewrite
        (C.connection_exactly
          c
          (Ghost.reveal initial))
        as
        (C.connection_exactly
          d.client_driver_client
          (Ghost.reveal initial));
      rewrite (O.is_auth_context auth) as (O.is_auth_context d.client_driver_auth);
      fold (client_driver_buffers d B.empty 0sz);
      assert (pure (client_driver_wire_logs_match
        (Ghost.reveal initial)
        B.empty
        B.empty
        B.empty
        0sz));
      assert (pure (Seq.equal B.empty (Ghost.reveal initial).CS.cs_wire_log.CL.raw_received));
      assert (pure (Seq.equal B.empty (Ghost.reveal initial).CS.cs_wire_log.CL.raw_sent));
      assert (pure (CP.client_invariant_pure
        (Ghost.reveal initial)
        B.empty
        B.empty
        (Ghost.reveal initial)));
      fold
        (client_driver_live
          d
          (Ghost.reveal initial));
      rewrite
        (client_driver_live d (Ghost.reveal initial))
        as
        (client_driver_live
          d
          (CR.configured_initial_state
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds));
      d
}

fn driver_connect
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to connect_host 'connect_host_bytes **
           pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len /\
                 B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: option driver
  ensures pts_to connect_host 'connect_host_bytes **
          pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some d ->
             driver_exactly
               d
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds)
               B.empty
               0sz **
             pure (CT.client_state_correct
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds) /\
                   CT.client_end_to_end_invariant
                     (CR.configured_initial_state
                       (Ghost.reveal 'server_name_bytes)
                       (Ghost.reveal 'trust_anchors_bytes)
                       validation_time_seconds))
           | None ->
             emp)
{
  let ch_opt = IO.connect_tcp connect_host connect_host_len port;
  match ch_opt {
    None -> {
    None
  }
    Some ch -> {
    let c =
      C.new_client
        server_name
        server_name_len
        trust_anchors
        trust_anchors_len
        validation_time_seconds;
    rewrite
      (CR.connection_exactly
        c
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds))
      as
      (C.connection_exactly
        c
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds));
    assert (pure (client_driver_wire_logs_match
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds)
      B.empty
      B.empty
      B.empty
      0sz));
    fold (channel_open ch
      (CR.configured_initial_state
        (Ghost.reveal 'server_name_bytes)
        (Ghost.reveal 'trust_anchors_bytes)
        validation_time_seconds)
      B.empty
      0sz);
    fold
      (driver_exactly
        {
          driver_client = c;
          driver_channel = ch;
        }
        (CR.configured_initial_state
          (Ghost.reveal 'server_name_bytes)
          (Ghost.reveal 'trust_anchors_bytes)
          validation_time_seconds)
        B.empty
        0sz);
    Some {
      driver_client = c;
      driver_channel = ch;
    }
  }
  }
}

fn driver_open
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (server_name:array U8.t)
  (server_name_len:SZ.t)
  (trust_anchors:array U8.t)
  (trust_anchors_len:SZ.t)
  (validation_time_seconds:SZ.t)
  requires pts_to connect_host 'connect_host_bytes **
           pts_to server_name 'server_name_bytes **
           pts_to trust_anchors 'trust_anchors_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len /\
                 B.length 'server_name_bytes == SZ.v server_name_len /\
                 B.length 'trust_anchors_bytes == SZ.v trust_anchors_len /\
                 SZ.v server_name_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_hostname_len /\
                 SZ.v trust_anchors_len <=
                   TLS13.Impl.ConnectionState.Bounds.max_trust_anchors_len)
  returns result: option top_driver
  ensures pts_to connect_host 'connect_host_bytes **
          pts_to server_name 'server_name_bytes **
          pts_to trust_anchors 'trust_anchors_bytes **
          (match result with
           | Some d ->
             top_driver_exactly
               d
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds)
               B.empty
               0sz **
             pure (CT.client_state_correct
               (CR.configured_initial_state
                 (Ghost.reveal 'server_name_bytes)
                 (Ghost.reveal 'trust_anchors_bytes)
                 validation_time_seconds) /\
                   CT.client_end_to_end_invariant
                     (CR.configured_initial_state
                       (Ghost.reveal 'server_name_bytes)
                       (Ghost.reveal 'trust_anchors_bytes)
                       validation_time_seconds))
           | None ->
             emp)
{
  let auth =
    O.auth_context_new
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  let connected =
    driver_connect
      connect_host
      connect_host_len
      port
      server_name
      server_name_len
      trust_anchors
      trust_anchors_len
      validation_time_seconds;
  match connected {
    None -> {
      O.auth_context_free auth;
      None
    }
    Some d -> {
      fold
        (top_driver_exactly
          {
            top_driver_core = d;
            top_driver_auth = auth;
          }
          (CR.configured_initial_state
            (Ghost.reveal 'server_name_bytes)
            (Ghost.reveal 'trust_anchors_bytes)
            validation_time_seconds)
          B.empty
          0sz);
      Some {
        top_driver_core = d;
        top_driver_auth = auth;
      }
    }
  }
}

fn driver_control_snapshot
  (d:driver)
  requires driver_exactly d 'st0 'buffered 'pending_len
  returns snapshot:CR.control_snapshot
  ensures driver_exactly d 'st0 'buffered 'pending_len **
          pure (CR.control_snapshot_matches snapshot 'st0)
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot = C.control_snapshot d.driver_client;
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  snapshot
}

fn driver_copy_certificate_leaf_der
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_handshake_flight_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der with
                 | Some leaf ->
                   SZ.v copied_len == B.length leaf /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) leaf
                 | None -> False))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let copied_len =
    C.copy_certificate_leaf_der
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  copied_len
}

fn driver_copy_certificate_verify_input
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input)
  returns copied_len:SZ.t
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v copied_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input with
                 | Some input ->
                   SZ.v copied_len == B.length input /\
                   Seq.equal (Seq.slice out_bytes 0 (SZ.v copied_len)) input
                 | None -> False))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let copied_len =
    C.copy_certificate_verify_input
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  copied_len
}

fn driver_copy_certificate_verify_signature
  (d:driver)
  (out:array U8.t)
  (out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 L.max_signature_len <= SZ.v out_len /\
                 Some?
                   'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
  returns snapshot:CR.certificate_verify_signature_snapshot
  ensures exists* out_bytes.
          driver_exactly d 'st0 'buffered 'pending_len **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v snapshot.CR.cv_signature_len <= B.length out_bytes /\
                (match 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify with
                 | Some cv ->
                   L.signature_scheme_matches snapshot.CR.cv_signature_scheme (Sem.certificateVerify_scheme cv) /\
                   SZ.v snapshot.CR.cv_signature_len == B.length (Sem.certificateVerify_signature_bytes cv) /\
                   Seq.equal
                     (Seq.slice out_bytes 0 (SZ.v snapshot.CR.cv_signature_len))
                     (Sem.certificateVerify_signature_bytes cv)
                 | None -> False))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let snapshot =
    C.copy_certificate_verify_signature
      d.driver_client
      out
      out_len;
  with out_bytes.
    assert (CR.connection_exactly d.driver_client 'st0 **
            pts_to out out_bytes);
  rewrite (CR.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  snapshot
}

fn process_local_event_and_write_once
  (c:C.client)
  (ch:IO.channel)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           channel_open ch 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           channel_open ch st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   kind
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  rewrite (C.connection_exactly c 'st0) as (CR.connection_exactly c 'st0);
  let resp =
    C.process_local_event
      c
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (CR.connection_exactly c st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (CR.connection_exactly c st1) as (C.connection_exactly c st1);
  assert (pure (CT.local_event_end_to_end_correct
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes));
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  lemma_local_event_wire_lengths
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (CT.response_wf resp network_out_bytes app_out_bytes));
  assert (pure (SZ.v resp.CT.network_out_len <= B.length network_out_bytes));
  unfold (channel_open ch 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  with received sent.
    assert (IO.is_channel ch received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len)));
  let old_consumed =
    Ghost.hide (ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          'st0
          received
          sent
          consumed
          (Ghost.reveal 'buffered)
          (Ghost.reveal 'pending_len)));
  assert (pure (client_driver_wire_logs_match_witness
    'st0
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len)));
  let written = IO.write ch network_out resp.CT.network_out_len;
  assert (pure (written == resp.CT.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  Seq.lemma_len_append sent (Seq.slice network_out_bytes 0 (SZ.v written));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (CT.response_network_out resp network_out_bytes)));
  assert (pure (Seq.equal sent 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim sent 'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (CT.response_network_out resp network_out_bytes))));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received));
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    'st0.CS.cs_wire_log.CL.raw_received;
  lemma_local_event_received_exact_when_nonfailed
    'st0
    st1
    resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len);
  assert (pure (client_driver_wire_logs_match
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal 'buffered)
    (Ghost.reveal 'pending_len)));
  fold (channel_open ch st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  assert (pure (SZ.v written <= SZ.v resp.CT.network_out_len));
  assert (pure (resp.CT.status == CT.StepOk ==>
    SZ.v written <= SZ.v resp.CT.network_out_len));
  {
    local_write_resp = resp;
    local_write_written = written;
  }
}

fn driver_process_local_event
  (d:driver)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   kind
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let result =
    process_local_event_and_write_once
      d.driver_client
      d.driver_channel
      kind
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    kind
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn driver_process_buffered_network_bytes_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: network_read_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
             (pending_after_consumed
               buffered_len
               result.network_read_buffer_resp.CT.consumed_len) **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 Seq.equal raw_bytes (Ghost.reveal 'old_raw) /\
                 B.length (Ghost.reveal result.network_read_prefix) ==
                   SZ.v result.network_read_len /\
                 result.network_read_len == buffered_len /\
                 SZ.v result.network_read_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 B.length (Ghost.reveal 'buffered) == SZ.v buffered_len /\
                 SZ.v result.network_read_buffer_resp.CT.consumed_len <=
                   SZ.v buffered_len /\
                 Seq.equal buffered_after
                   (Seq.slice (Ghost.reveal 'buffered)
                     (SZ.v result.network_read_buffer_resp.CT.consumed_len)
                     (SZ.v buffered_len)) /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.network_read_buffer_resp
                  (Ghost.reveal result.network_read_prefix)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                  CT.NeedMoreInput ==>
                  result.network_read_buffer_resp.CT.consumed_len == 0sz) /\
                 (result.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.network_read_written <=
                 SZ.v result.network_read_buffer_resp.CT.response.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 'buffered buffered_len);
  A.pts_to_len raw;
  assert (pure (A.length raw == SZ.v raw_capacity));
  A.to_mask raw;
  with raw_mask.
    assert (A.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v raw_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index (Ghost.reveal 'old_raw) i)));
  let raw_prefix_array =
    A.sub raw #1.0R #(fun _ -> True) 0sz (SZ.v buffered_len);
  with raw_prefix_mask.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask ==>
    Some? (Seq.index raw_prefix_mask i)));
  A.from_mask raw_prefix_array;
  with raw_prefix.
    assert (pts_to raw_prefix_array raw_prefix);
  assert (pure (B.length raw_prefix == SZ.v buffered_len));
  assert (pure (Seq.equal raw_prefix
    (Seq.slice (Ghost.reveal 'old_raw) 0 (SZ.v buffered_len))));
  assert (pure (Seq.equal raw_prefix (Ghost.reveal 'buffered)));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (CR.connection_exactly d.driver_client 'st0);
  let buffer_resp =
    C.process_network_bytes
      d.driver_client
      raw_prefix_array
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (CR.connection_exactly d.driver_client st1 **
            pts_to raw_prefix_array raw_prefix **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  rewrite (CR.connection_exactly d.driver_client st1)
    as (C.connection_exactly d.driver_client st1);
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
    buffer_resp.CT.consumed_len == 0sz));
  lemma_network_bytes_wire_lengths
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes;
  assert (pure (SZ.v buffer_resp.CT.consumed_len <= B.length raw_prefix));
  assert (pure (SZ.v buffer_resp.CT.consumed_len <= SZ.v buffered_len));
  let new_pending = pending_after_consumed buffered_len buffer_resp.CT.consumed_len;
  assert (pure (SZ.v new_pending ==
    SZ.v buffered_len - SZ.v buffer_resp.CT.consumed_len));
  A.to_mask raw_prefix_array;
  with raw_prefix_mask_after.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True));
  assert (pure (Seq.length raw_prefix_mask_after == SZ.v buffered_len));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Some? (Seq.index raw_prefix_mask_after i)));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Seq.index raw_prefix_mask_after i == Some (Seq.index raw_prefix i)));
  rewrite
    (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True))
    as
    (A.pts_to_mask (A.gsub raw 0 (SZ.v buffered_len)) #1.0R raw_prefix_mask_after (fun _ -> True));
  A.return_sub
    raw
    #1.0R
    #raw_mask
    #raw_prefix_mask_after
    #(fun k -> True /\ ~(0 <= k /\ k < SZ.v buffered_len))
    #(fun _ -> True)
    #0
    #(SZ.v buffered_len);
  with raw_joined_mask.
    assert (A.pts_to_mask raw #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(0 <= k /\ k < SZ.v buffered_len)) \/
        (0 <= k /\ k < SZ.v buffered_len /\ True)));
  assert (pure (Seq.length raw_joined_mask == Seq.length raw_mask));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i ==
      (if 0 <= i && i < SZ.v buffered_len
       then Seq.index raw_prefix_mask_after (i - 0)
       else Seq.index raw_mask i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i ==
      (if i < SZ.v buffered_len
       then Seq.index raw_prefix_mask_after i
       else Seq.index raw_mask i)));
  lemma_rejoined_raw_mask_matches_old
    (Ghost.reveal 'old_raw)
    raw_prefix
    raw_mask
    raw_prefix_mask_after
    raw_joined_mask
    (SZ.v buffered_len);
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v buffered_len)) \/
     (0 <= i /\ i < SZ.v buffered_len /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i == Some (Seq.index (Ghost.reveal 'old_raw) i)));
  A.from_mask raw;
  with raw_bytes.
    assert (pts_to raw raw_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  assert (pure (Seq.equal raw_bytes (Ghost.reveal 'old_raw)));
  assert (pure (CT.response_wf buffer_resp.CT.response network_out_bytes app_out_bytes));
  assert (pure (SZ.v buffer_resp.CT.response.CT.network_out_len <= B.length network_out_bytes));
  unfold (channel_open d.driver_channel 'st0 'buffered buffered_len);
  with received sent.
    assert (IO.is_channel d.driver_channel received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) buffered_len));
  let old_consumed =
    Ghost.hide (ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          'st0
          received
          sent
          consumed
          (Ghost.reveal 'buffered)
          buffered_len));
  assert (pure (client_driver_wire_logs_match_witness
    'st0
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    buffered_len));
  let consumed_prefix =
    Ghost.hide (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len);
  let new_buffered =
    Ghost.hide (Seq.slice (Ghost.reveal 'buffered)
      (SZ.v buffer_resp.CT.consumed_len)
      (SZ.v buffered_len));
  Seq.lemma_len_slice
    (Ghost.reveal 'buffered)
    (SZ.v buffer_resp.CT.consumed_len)
    (SZ.v buffered_len);
  assert (pure (B.length (Ghost.reveal new_buffered) == SZ.v new_pending));
  assert (pure (Seq.equal (Ghost.reveal consumed_prefix)
    (Seq.slice (Ghost.reveal 'buffered) 0 (SZ.v buffer_resp.CT.consumed_len))));
  assert (pure (Seq.equal
    (Ghost.reveal consumed_prefix)
    (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len)));
  lemma_slice_append_full
    (Ghost.reveal 'buffered)
    (SZ.v buffer_resp.CT.consumed_len);
  assert (pure (Seq.equal
    (B.append (Ghost.reveal consumed_prefix) (Ghost.reveal new_buffered))
    (Ghost.reveal 'buffered)));
  lemma_network_bytes_logged_received_accounted
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes
    (Ghost.reveal old_consumed);
  Seq.append_assoc (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix) (Ghost.reveal new_buffered);
  assert (pure (Seq.equal
    (B.append (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix)) (Ghost.reveal new_buffered))
    received));
  let written = IO.write d.driver_channel network_out buffer_resp.CT.response.CT.network_out_len;
  assert (pure (written == buffer_resp.CT.response.CT.network_out_len));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  Seq.lemma_len_append sent (Seq.slice network_out_bytes 0 (SZ.v written));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (CT.response_network_out buffer_resp.CT.response network_out_bytes)));
  assert (pure (Seq.equal sent 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim sent 'st0.CS.cs_wire_log.CL.raw_sent;
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (CT.response_network_out buffer_resp.CT.response network_out_bytes))));
  lemma_network_bytes_logged_received_exact_when_nonfailed
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    buffered_len;
  assert (pure (CT.connection_control_not_failed st1 ==>
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append (Ghost.reveal old_consumed)
        (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len))));
  Seq.lemma_eq_elim
    (Ghost.reveal consumed_prefix)
    (CT.network_consumed_prefix raw_prefix buffer_resp.CT.consumed_len);
  assert (pure (client_driver_wire_logs_match_witness
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
    (Ghost.reveal new_buffered)
    new_pending));
  assert (pure (client_driver_wire_logs_match
    st1
    received
    (B.append sent
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal new_buffered)
    new_pending));
  fold (channel_open d.driver_channel st1 (Ghost.reveal new_buffered) new_pending);
  assert (pure (SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
  assert (pure (buffer_resp.CT.response.CT.status == CT.StepOk ==>
    SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len));
  fold (driver_exactly d st1 (Ghost.reveal new_buffered) new_pending);
  assert (pure (B.length raw_prefix == SZ.v buffered_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    raw_prefix
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (B.length raw_bytes == SZ.v raw_capacity /\
    B.length raw_prefix == SZ.v buffered_len /\
    buffered_len == buffered_len /\
    SZ.v buffered_len <= SZ.v raw_capacity /\
    B.length network_out_bytes == SZ.v network_out_len /\
    B.length app_out_bytes == SZ.v app_out_len /\
    CT.network_bytes_end_to_end_correct
      'st0
      st1
      buffer_resp
      raw_prefix
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes /\
    (buffer_resp.CT.response.CT.status == CT.NeedMoreInput ==>
     buffer_resp.CT.consumed_len == 0sz) /\
    (buffer_resp.CT.response.CT.status == CT.StepOk ==>
     SZ.v written <= SZ.v buffer_resp.CT.response.CT.network_out_len)));
  assert (pure (new_pending ==
    pending_after_consumed buffered_len buffer_resp.CT.consumed_len));
  let result = {
    network_read_len = buffered_len;
    network_read_buffer_resp = buffer_resp;
    network_read_written = written;
    network_read_prefix = Ghost.hide raw_prefix;
  };
  assert (pure (pending_after_consumed buffered_len
    result.network_read_buffer_resp.CT.consumed_len == new_pending));
  rewrite (driver_exactly d st1 (Ghost.reveal new_buffered) new_pending) as
    (driver_exactly d st1 (Ghost.reveal new_buffered)
      (pending_after_consumed buffered_len
        result.network_read_buffer_resp.CT.consumed_len));
  result
}

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (new_len == pending_after_consumed buffered_len consumed_len));
  assert (pure (SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  let no_shift = consumed_len = 0sz;
  if no_shift {
    assert (pure (new_len == buffered_len));
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'raw_bytes) 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes)
        (SZ.v consumed_len)
        (SZ.v buffered_len))));
    new_len
  } else {
    let mut i = 0sz;
    while ((R.read i) `SZ.lt` new_len)
      invariant live i
      invariant exists* raw_loop.
        pts_to raw raw_loop **
        pure (B.length raw_loop == SZ.v raw_capacity /\
              SZ.v (R.read i) <= SZ.v new_len /\
              SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
              SZ.v new_len <= SZ.v buffered_len /\
              SZ.v consumed_len <= SZ.v buffered_len /\
              SZ.v buffered_len <= SZ.v raw_capacity /\
              (forall (k:nat). k < SZ.v (R.read i) ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)) /\
              (forall (k:nat). SZ.v (R.read i) <= k /\ k < SZ.v buffered_len ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) k))
    {
      let vi = R.read i;
      assert (pure (SZ.v vi < SZ.v new_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v buffered_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v raw_capacity));
      SZ.fits_lte (SZ.v vi + SZ.v consumed_len) (SZ.v raw_capacity);
      let src_idx = vi `SZ.add` consumed_len;
      assert (pure (SZ.v src_idx < SZ.v raw_capacity));
      with raw_before_read.
        assert (pts_to raw raw_before_read);
      assert (pure (B.length raw_before_read == SZ.v raw_capacity));
      let b = raw.(src_idx);
      assert (pure (b == Seq.index (Ghost.reveal 'raw_bytes)
        (SZ.v vi + SZ.v consumed_len)));
      assert (pure (SZ.v vi < SZ.v raw_capacity));
      raw.(vi) <- b;
      with raw_after_write.
        assert (pts_to raw raw_after_write);
      assert (pure (B.length raw_after_write == SZ.v raw_capacity));
      assert (pure (Seq.index raw_after_write (SZ.v vi) == b));
      assert (pure (forall (k:nat). k < SZ.v vi ==>
        Seq.index raw_after_write k == Seq.index raw_before_read k));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k == Seq.index raw_before_read k));
      assert (pure (forall (k:nat). k < SZ.v vi + 1 ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) k));
      assert (pure (SZ.v vi + 1 <= SZ.v new_len));
      SZ.fits_lte (SZ.v vi + 1) (SZ.v new_len);
      let next_i = vi `SZ.add` 1sz;
      R.write i next_i;
    };
    with raw_done.
      assert (pts_to raw raw_done);
    assert (pure (B.length raw_done == SZ.v raw_capacity));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index raw_done k ==
      Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
    Seq.lemma_len_slice raw_done 0 (SZ.v new_len);
    Seq.lemma_len_slice (Ghost.reveal 'raw_bytes)
      (SZ.v consumed_len)
      (SZ.v buffered_len);
    assert (pure (forall (k:nat). k < B.length (Seq.slice raw_done 0 (SZ.v new_len)) ==>
      Seq.index (Seq.slice raw_done 0 (SZ.v new_len)) k ==
      Seq.index
        (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
        k));
    Seq.lemma_eq_intro
      (Seq.slice raw_done 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len));
    new_len
  }
}

fn driver_process_buffered_network_bytes_compact_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after result.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes ==
                   SZ.v raw_capacity /\
                 B.length (Ghost.reveal result.buffered_network_read.network_read_prefix) ==
                   SZ.v result.buffered_network_read.network_read_len /\
                 result.buffered_network_read.network_read_len == buffered_len /\
                 SZ.v result.buffered_network_new_len <= SZ.v buffered_len /\
                 SZ.v result.buffered_network_new_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.buffered_network_new_len)) /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.buffered_network_read.network_read_buffer_resp
                  (Ghost.reveal result.buffered_network_read.network_read_prefix)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes /\
                 (result.buffered_network_read.network_read_buffer_resp.CT.response.CT.status ==
                 CT.StepOk ==>
                 SZ.v result.buffered_network_read.network_read_written <=
                 SZ.v result.buffered_network_read.network_read_buffer_resp.CT.response.CT.network_out_len))
{
  let read_result =
    driver_process_buffered_network_bytes_once
      d
      raw
      raw_capacity
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
    assert (driver_exactly d st1 buffered_after
              (pending_after_consumed
                buffered_len
                read_result.network_read_buffer_resp.CT.consumed_len) **
            pts_to raw raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  assert (pure (B.length (Ghost.reveal read_result.network_read_prefix) ==
    SZ.v read_result.network_read_len));
  assert (pure (read_result.network_read_len == buffered_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    read_result.network_read_buffer_resp
    (Ghost.reveal read_result.network_read_prefix)
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  assert (pure (SZ.v read_result.network_read_buffer_resp.CT.consumed_len <=
    B.length (Ghost.reveal read_result.network_read_prefix)));
  assert (pure (SZ.v read_result.network_read_buffer_resp.CT.consumed_len <=
    SZ.v buffered_len));
  let consumed_zero =
    read_result.network_read_buffer_resp.CT.consumed_len = 0sz;
  if consumed_zero {
    assert (pure (SZ.v buffered_len <= SZ.v buffered_len));
    assert (pure (
      pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len == buffered_len));
    assert (pure (Seq.equal buffered_after
      (Seq.slice (Ghost.reveal 'buffered) 0 (SZ.v buffered_len))));
    SeqP.slice_length (Ghost.reveal 'buffered);
    Seq.lemma_eq_elim
      buffered_after
      (Seq.slice (Ghost.reveal 'buffered) 0 (SZ.v buffered_len));
    Seq.lemma_eq_elim
      (Ghost.reveal 'buffered)
      (Seq.slice (Ghost.reveal 'old_raw) 0 (SZ.v buffered_len));
    Seq.lemma_eq_elim raw_bytes (Ghost.reveal 'old_raw);
    assert (pure (Seq.equal buffered_after
      (Seq.slice raw_bytes 0 (SZ.v buffered_len))));
    rewrite (driver_exactly d st1 buffered_after
      (pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len)) as
      (driver_exactly d st1 buffered_after buffered_len);
    {
      buffered_network_read = read_result;
      buffered_network_new_len = buffered_len;
    }
  } else {
    let new_len =
      compact_buffer_suffix
        raw
        raw_capacity
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len;
    with compacted_raw.
      assert (pts_to raw compacted_raw);
    assert (pure (B.length compacted_raw == SZ.v raw_capacity));
    assert (pure (SZ.v new_len <= SZ.v buffered_len));
    assert (pure (Seq.equal buffered_after
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))));
    assert (pure (Seq.equal
      (Seq.slice compacted_raw 0 (SZ.v new_len))
      (Seq.slice raw_bytes
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))));
    SeqP.slice_slice
      (Ghost.reveal 'old_raw)
      0
      (SZ.v buffered_len)
      (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
      (SZ.v buffered_len);
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))
      (Seq.slice (Ghost.reveal 'old_raw)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))));
    Seq.lemma_eq_elim
      buffered_after
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len));
    Seq.lemma_eq_elim
      (Seq.slice (Ghost.reveal 'buffered)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len))
      (Seq.slice (Ghost.reveal 'old_raw)
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len));
    Seq.lemma_eq_elim
      (Seq.slice compacted_raw 0 (SZ.v new_len))
      (Seq.slice raw_bytes
        (SZ.v read_result.network_read_buffer_resp.CT.consumed_len)
        (SZ.v buffered_len));
    Seq.lemma_eq_elim raw_bytes (Ghost.reveal 'old_raw);
    assert (pure (buffered_after == Seq.slice compacted_raw 0 (SZ.v new_len)));
    assert (pure (Seq.equal buffered_after (Seq.slice compacted_raw 0 (SZ.v new_len))));
    assert (pure (
      pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len == new_len));
    rewrite (driver_exactly d st1 buffered_after
      (pending_after_consumed
        buffered_len
        read_result.network_read_buffer_resp.CT.consumed_len)) as
      (driver_exactly d st1 buffered_after new_len);
    {
      buffered_network_read = read_result;
      buffered_network_new_len = new_len;
    }
  }
}

fn driver_read_buffered_network_bytes_compact_once
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
            result.buffered_network_io_buffered.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_read_len <=
                  SZ.v raw_capacity - SZ.v buffered_len /\
                 B.length
                  (Ghost.reveal
                    result.buffered_network_io_buffered.buffered_network_read.network_read_prefix) ==
                  SZ.v
                    result.buffered_network_io_buffered.buffered_network_read.network_read_len /\
                 SZ.v
                  result.buffered_network_io_buffered.buffered_network_read.network_read_len <=
                  SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_buffered.buffered_network_new_len <=
                  SZ.v result.buffered_network_io_buffered.buffered_network_read.network_read_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0
                     (SZ.v result.buffered_network_io_buffered.buffered_network_new_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.network_bytes_end_to_end_correct
                  'st0
                  st1
                  result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
                  (Ghost.reveal
                    result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
                  (Ghost.reveal 'old_network_out)
                  network_out_bytes
                  (Ghost.reveal 'old_app_out)
                  app_out_bytes)
{
  unfold (driver_exactly d 'st0 'buffered buffered_len);
  A.pts_to_len raw;
  assert (pure (A.length raw == SZ.v raw_capacity));
  A.to_mask raw;
  with raw_mask.
    assert (A.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v raw_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index (Ghost.reveal 'old_raw) i)));
  let available = SZ.sub raw_capacity buffered_len;
  assert (pure (SZ.v available == SZ.v raw_capacity - SZ.v buffered_len));
  let raw_tail_array =
    A.sub raw #1.0R #(fun _ -> True) buffered_len (SZ.v raw_capacity);
  with raw_tail_mask.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask (fun _ -> True));
  assert (pure (Seq.length raw_tail_mask == SZ.v available));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask ==>
    Some? (Seq.index raw_tail_mask i)));
  A.from_mask raw_tail_array;
  with raw_tail.
    assert (pts_to raw_tail_array raw_tail);
  assert (pure (B.length raw_tail == SZ.v available));
  unfold (channel_open d.driver_channel 'st0 'buffered buffered_len);
  with received sent.
    assert (IO.is_channel d.driver_channel received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) buffered_len));
  let old_consumed =
    Ghost.hide (ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        client_driver_wire_logs_match_witness
          'st0
          received
          sent
          consumed
          (Ghost.reveal 'buffered)
          buffered_len));
  assert (pure (client_driver_wire_logs_match_witness
    'st0
    received
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal 'buffered)
    buffered_len));
  let read_len = IO.read d.driver_channel raw_tail_array available;
  with raw_tail_after read_chunk.
    assert (IO.is_channel d.driver_channel (B.append received read_chunk) sent **
            pts_to raw_tail_array raw_tail_after);
  Seq.lemma_len_append received read_chunk;
  assert (pure (B.length read_chunk == SZ.v read_len));
  assert (pure (SZ.v buffered_len + SZ.v read_len <= SZ.v raw_capacity));
  SZ.fits_lte (SZ.v buffered_len + SZ.v read_len) (SZ.v raw_capacity);
  let total_len = buffered_len `SZ.add` read_len;
  assert (pure (SZ.v total_len == SZ.v buffered_len + SZ.v read_len));
  assert (pure (SZ.v total_len <= SZ.v raw_capacity));
  let new_buffered =
    Ghost.hide (B.append (Ghost.reveal 'buffered) read_chunk);
  Seq.lemma_len_append (Ghost.reveal 'buffered) read_chunk;
  Seq.append_assoc (Ghost.reveal old_consumed) (Ghost.reveal 'buffered) read_chunk;
  assert (pure (client_driver_wire_logs_match_witness
    'st0
    (B.append received read_chunk)
    sent
    (Ghost.reveal old_consumed)
    (Ghost.reveal new_buffered)
    total_len));
  assert (pure (client_driver_wire_logs_match
    'st0
    (B.append received read_chunk)
    sent
    (Ghost.reveal new_buffered)
    total_len));
  fold (channel_open d.driver_channel 'st0 (Ghost.reveal new_buffered) total_len);
  assert (pure (B.length raw_tail_after == SZ.v available));
  assert (pure (SZ.v read_len <= SZ.v available));
  A.to_mask raw_tail_array;
  with raw_tail_mask_after.
    assert (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True));
  assert (pure (Seq.length raw_tail_mask_after == B.length raw_tail_after));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask_after ==>
    Seq.index raw_tail_mask_after i == Some (Seq.index raw_tail_after i)));
  assert (pure (forall (i:nat). i < Seq.length raw_tail_mask_after ==>
    Some? (Seq.index raw_tail_mask_after i)));
  rewrite
    (A.pts_to_mask raw_tail_array #1.0R raw_tail_mask_after (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub raw (SZ.v buffered_len) (SZ.v raw_capacity))
      #1.0R
      raw_tail_mask_after
      (fun _ -> True));
  A.return_sub
    raw
    #1.0R
    #raw_mask
    #raw_tail_mask_after
    #(fun k -> True /\ ~(SZ.v buffered_len <= k /\ k < SZ.v raw_capacity))
    #(fun _ -> True)
    #(SZ.v buffered_len)
    #(SZ.v raw_capacity);
  with raw_joined_mask.
    assert (A.pts_to_mask raw #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(SZ.v buffered_len <= k /\ k < SZ.v raw_capacity)) \/
        (SZ.v buffered_len <= k /\ k < SZ.v raw_capacity /\ True)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(SZ.v buffered_len <= i /\ i < SZ.v raw_capacity)) \/
     (SZ.v buffered_len <= i /\ i < SZ.v raw_capacity /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  A.from_mask raw;
  with raw_after_read.
    assert (pts_to raw raw_after_read);
  assert (pure (B.length raw_after_read == SZ.v raw_capacity));
  assert (pure (Seq.equal (Ghost.reveal 'buffered)
    (Seq.slice (Ghost.reveal 'old_raw) 0 (SZ.v buffered_len))));
  assert (pure (Seq.equal read_chunk
    (Seq.slice raw_tail_after 0 (SZ.v read_len))));
  assert (pure (forall (i:nat). i < B.length raw_after_read ==>
    Some (Seq.index raw_after_read i) == Seq.index raw_joined_mask i));
  assert (pure (forall (i:nat). i < SZ.v buffered_len ==>
    Seq.index raw_after_read i == Seq.index (Ghost.reveal 'old_raw) i));
  assert (pure (forall (i:nat). i < SZ.v read_len ==>
    Seq.index raw_after_read (SZ.v buffered_len + i) ==
    Seq.index raw_tail_after i));
  lemma_read_append_buffer_matches_raw_prefix
    raw_after_read
    (Ghost.reveal 'old_raw)
    raw_tail_after
    (Ghost.reveal 'buffered)
    read_chunk
    (SZ.v buffered_len)
    (SZ.v read_len)
    (SZ.v total_len);
  Seq.lemma_eq_elim
    (B.append (Ghost.reveal 'buffered) read_chunk)
    (Seq.slice raw_after_read 0 (SZ.v total_len));
  assert (pure (Seq.equal (Ghost.reveal new_buffered)
    (Seq.slice raw_after_read 0 (SZ.v total_len))));
  rewrite (C.connection_exactly d.driver_client 'st0)
    as (C.connection_exactly d.driver_client 'st0);
  fold (driver_exactly d 'st0 (Ghost.reveal new_buffered) total_len);
  let buffered_result =
    driver_process_buffered_network_bytes_compact_once
      d
      raw
      raw_capacity
      total_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
    assert (driver_exactly d st1 buffered_after buffered_result.buffered_network_new_len **
            pts_to raw raw_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length raw_bytes == SZ.v raw_capacity));
  assert (pure (SZ.v read_len <= SZ.v raw_capacity - SZ.v buffered_len));
  assert (pure (B.length (Ghost.reveal
    buffered_result.buffered_network_read.network_read_prefix) ==
    SZ.v buffered_result.buffered_network_read.network_read_len));
  assert (pure (buffered_result.buffered_network_read.network_read_len == total_len));
  assert (pure (SZ.v buffered_result.buffered_network_read.network_read_len <=
    SZ.v raw_capacity));
  assert (pure (SZ.v buffered_result.buffered_network_new_len <=
    SZ.v buffered_result.buffered_network_read.network_read_len));
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  assert (pure (CT.network_bytes_end_to_end_correct
    'st0
    st1
    buffered_result.buffered_network_read.network_read_buffer_resp
    (Ghost.reveal buffered_result.buffered_network_read.network_read_prefix)
    (Ghost.reveal 'old_network_out)
    network_out_bytes
    (Ghost.reveal 'old_app_out)
    app_out_bytes));
  {
    buffered_network_io_read_len = read_len;
    buffered_network_io_buffered = buffered_result;
  }
}

fn rec driver_process_buffered_network_records
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_loop_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
            result.buffered_network_loop_last.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_loop_last.buffered_network_new_len <=
                  SZ.v buffered_len /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len)
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  if (fuel = 0sz) {
    assert (pure (no_op.buffered_network_new_len == buffered_len));
    rewrite (driver_exactly d 'st0 'buffered buffered_len) as
      (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len);
    let result = {
      buffered_network_loop_last = no_op;
      buffered_network_loop_exhausted = true;
    };
    assert (pure (result.buffered_network_loop_last.buffered_network_new_len ==
      no_op.buffered_network_new_len));
    rewrite (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len) as
      (driver_exactly d 'st0 'buffered
        result.buffered_network_loop_last.buffered_network_new_len);
    result
  } else {
    assert (pure (0 < SZ.v fuel));
    let empty_buffer = buffered_len = 0sz;
    if empty_buffer {
      assert (pure (no_op.buffered_network_new_len == buffered_len));
      rewrite (driver_exactly d 'st0 'buffered buffered_len) as
        (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len);
      let result = {
        buffered_network_loop_last = no_op;
        buffered_network_loop_exhausted = false;
      };
      assert (pure (result.buffered_network_loop_last.buffered_network_new_len ==
        no_op.buffered_network_new_len));
      rewrite (driver_exactly d 'st0 'buffered no_op.buffered_network_new_len) as
        (driver_exactly d 'st0 'buffered
          result.buffered_network_loop_last.buffered_network_new_len);
      result
    } else {
      let step =
        driver_process_buffered_network_bytes_compact_once
          d
          raw
          raw_capacity
          buffered_len
          network_out
          network_out_len
          app_out
          app_out_len;
      with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
        assert (driver_exactly d st1 buffered_after step.buffered_network_new_len **
                pts_to raw raw_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      assert (pure (B.length raw_bytes == SZ.v raw_capacity));
      assert (pure (SZ.v step.buffered_network_new_len <= SZ.v buffered_len));
      assert (pure (SZ.v step.buffered_network_new_len <= SZ.v raw_capacity));
      let ok =
        step.buffered_network_read.network_read_buffer_resp.CT.response.CT.status =
        CT.StepOk;
      let no_app =
        step.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len =
        0sz;
      let consumed_zero =
        step.buffered_network_read.network_read_buffer_resp.CT.consumed_len = 0sz;
      let empty_after = step.buffered_network_new_len = 0sz;
      let continue_loop =
        ok && no_app && (consumed_zero = false) && (empty_after = false);
      if continue_loop {
        assert (pure (0 < SZ.v fuel));
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        assert (pure (Seq.equal buffered_after
          (Seq.slice raw_bytes 0 (SZ.v step.buffered_network_new_len))));
        driver_process_buffered_network_records
          d
          raw
          raw_capacity
          step.buffered_network_new_len
          network_out
          network_out_len
          app_out
          app_out_len
          next_fuel
      } else {
        {
          buffered_network_loop_last = step;
          buffered_network_loop_exhausted = false;
        }
      }
    }
  }
}

fn process_ready_internal_local_action_once
  (c:C.client)
  (ch:IO.channel)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           channel_open ch 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           channel_open ch st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v                   result.ready_local_resp.CT.network_out_len) /\
                  True) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  rewrite (C.connection_exactly c 'st0) as (CR.connection_exactly c 'st0);
  let action =
    C.next_local_action
      c
      network_out_len
      certificate_public_key_len
      server_finished_payload_len;
  rewrite (CR.connection_exactly c 'st0) as (C.connection_exactly c 'st0);
  assert (pure (C.next_local_action_sound
    'st0
    network_out_len
    certificate_public_key_len
    server_finished_payload_len
    action));
  assert (pure (forall (i:nat{i < B.length (Ghost.reveal 'empty_payload_bytes)}).
    Seq.index (Ghost.reveal 'empty_payload_bytes) i == Seq.index B.empty i));
  Seq.lemma_eq_intro (Ghost.reveal 'empty_payload_bytes) B.empty;
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let ready = action.CT.next_local_ready;
  if ready {
    assert (pure (action.CT.next_local_ready == true));
    let needs_external_payload =
      action.CT.next_local_kind = CT.LocalValidateCertificate ||
      action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
    if needs_external_payload {
      assert (pure ('st0.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure ('st0 == 'st0));
      {
        ready_local_action = action;
        ready_local_processed = false;
        ready_local_resp = no_op_resp;
        ready_local_written = 0sz;
      }
    } else {
      assert (pure (C.next_local_action_internal_input_ready 'st0 action));
      assert (pure (internal_local_action_kind action.CT.next_local_kind));
      lemma_ready_internal_action_empty_payload_wf
        'st0
        network_out_len
        certificate_public_key_len
        server_finished_payload_len
        action
        (Ghost.reveal 'empty_payload_bytes);
      assert (pure (CT.local_input_wf
        'st0
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)));
      let write_result =
        process_local_event_and_write_once
          c
          ch
          action.CT.next_local_kind
          empty_payload
          0sz
          network_out
          network_out_len
          app_out
          app_out_len;
      with st1 network_out_bytes app_out_bytes.
        assert (C.connection_exactly c st1 **
                pts_to empty_payload 'empty_payload_bytes **
                pts_to network_out network_out_bytes **
                pts_to app_out app_out_bytes);
      assert (pure (CT.local_event_end_to_end_correct
        'st0
        st1
        write_result.local_write_resp
        action.CT.next_local_kind
        (Ghost.reveal 'empty_payload_bytes)
        network_out_bytes
        app_out_bytes));
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (write_result.local_write_resp.CT.status == CT.StepOk ==>
        SZ.v write_result.local_write_written <=
        SZ.v write_result.local_write_resp.CT.network_out_len));
      {
        ready_local_action = action;
        ready_local_processed = true;
        ready_local_resp = write_result.local_write_resp;
        ready_local_written = write_result.local_write_written;
      }
    }
  } else {
    assert (pure ('st0.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    assert (pure ('st0 == 'st0));
    {
      ready_local_action = action;
      ready_local_processed = false;
      ready_local_resp = no_op_resp;
      ready_local_written = 0sz;
    }
  }
}

fn driver_handshake_step
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 C.next_local_action_sound
                   'st0
                   network_out_len
                   certificate_public_key_len
                   server_finished_payload_len
                   result.ready_local_action /\
                 (result.ready_local_processed ==>
                  result.ready_local_action.CT.next_local_ready == true /\
                  CT.local_event_end_to_end_correct
                    'st0
                    st1
                    result.ready_local_resp
                    result.ready_local_action.CT.next_local_kind
                    (Ghost.reveal 'empty_payload_bytes)
                    network_out_bytes
                    app_out_bytes /\
                  (result.ready_local_resp.CT.status == CT.StepOk ==>
                   SZ.v result.ready_local_written <=
                   SZ.v                   result.ready_local_resp.CT.network_out_len) /\
                  True) /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let result =
    process_ready_internal_local_action_once
      d.driver_client
      d.driver_channel
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            channel_open d.driver_channel st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  lemma_ready_local_action_result_preserves_config
    'st0
    st1
    result
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn rec driver_drain_local_actions
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: driver_drain_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 (result.driver_drain_last.ready_local_processed \/
                  result.driver_drain_last.ready_local_written == 0sz) /\
                 (result.driver_drain_exhausted ==>
                  result.driver_drain_last.ready_local_processed == false /\
                  result.driver_drain_last.ready_local_written == 0sz))
  decreases (SZ.v fuel)
{
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_last = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    assert (pure (false == false /\ 0sz == 0sz));
    {
      driver_drain_last = no_op_last;
      driver_drain_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step =
      driver_handshake_step
        d
        empty_payload
        network_out
        network_out_len
        certificate_public_key_len
        server_finished_payload_len
        app_out
        app_out_len;
    with st1 network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
              pts_to empty_payload 'empty_payload_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (B.length network_out_bytes == SZ.v network_out_len));
    assert (pure (B.length app_out_bytes == SZ.v app_out_len));
    assert (pure (step.ready_local_processed \/
      step.ready_local_written == 0sz));
    let proceed =
      step.ready_local_processed &&
      step.ready_local_resp.CT.status = CT.StepOk;
    if proceed {
      let next_fuel = SZ.sub fuel 1sz;
      assert (pure (SZ.v next_fuel < SZ.v fuel));
      let result =
        driver_drain_local_actions
          d
          empty_payload
          network_out
          network_out_len
          certificate_public_key_len
          server_finished_payload_len
          app_out
          app_out_len
          next_fuel;
      result
    } else {
      {
        driver_drain_last = step;
        driver_drain_exhausted = false;
      }
    }
  }
}

fn driver_progress_buffered_network_step
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: buffered_network_io_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after
             result.buffered_network_io_buffered.buffered_network_new_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.buffered_network_io_buffered.buffered_network_new_len <=
                  SZ.v raw_capacity /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0
                     (SZ.v result.buffered_network_io_buffered.buffered_network_new_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 client_buffered_network_io_step_correct
                   st1
                   result
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1))
{
  let empty_buffer = buffered_len = 0sz;
  if empty_buffer {
    let read_result =
      driver_read_buffered_network_bytes_compact_once
      d
      raw
      raw_capacity
      buffered_len
      network_out
      network_out_len
      app_out
      app_out_len;
    with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 buffered_after
                read_result.buffered_network_io_buffered.buffered_network_new_len **
              pts_to raw raw_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (CT.network_bytes_end_to_end_correct
      'st0
      st1
      read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes));
    CT.lemma_network_bytes_end_to_end_correct_preserves_config
      'st0
      st1
      read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    assert (pure (client_buffered_network_io_step_correct
      st1
      read_result
      network_out_bytes
      app_out_bytes));
    assert (pure (CT.client_end_to_end_invariant 'st0 ==>
      CT.client_end_to_end_invariant st1));
    read_result
  } else {
    let processed =
      driver_process_buffered_network_bytes_compact_once
        d
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len;
    with st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
      assert (driver_exactly d st1 buffered_after processed.buffered_network_new_len **
              pts_to raw raw_bytes **
              pts_to network_out network_out_bytes **
              pts_to app_out app_out_bytes);
    assert (pure (CT.network_bytes_end_to_end_correct
      'st0
      st1
      processed.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal processed.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes));
    CT.lemma_network_bytes_end_to_end_correct_preserves_config
      'st0
      st1
      processed.buffered_network_read.network_read_buffer_resp
      (Ghost.reveal processed.buffered_network_read.network_read_prefix)
      (Ghost.reveal 'old_network_out)
      network_out_bytes
      (Ghost.reveal 'old_app_out)
      app_out_bytes;
    assert (pure (CT.client_end_to_end_invariant 'st0 ==>
      CT.client_end_to_end_invariant st1));
    assert (pure (B.length raw_bytes == SZ.v raw_capacity));
    assert (pure (SZ.v processed.buffered_network_new_len <= SZ.v buffered_len));
    assert (pure (SZ.v processed.buffered_network_new_len <= SZ.v raw_capacity));
    let need_more =
      processed.buffered_network_read.network_read_buffer_resp.CT.response.CT.status =
      CT.NeedMoreInput;
    if need_more {
      assert (pure (Seq.equal buffered_after
        (Seq.slice raw_bytes 0 (SZ.v processed.buffered_network_new_len))));
      let read_result =
        driver_read_buffered_network_bytes_compact_once
        d
        raw
        raw_capacity
        processed.buffered_network_new_len
        network_out
        network_out_len
        app_out
        app_out_len;
      with st2 buffered_after2 raw_bytes2 network_out_bytes2 app_out_bytes2.
        assert (driver_exactly d st2 buffered_after2
                  read_result.buffered_network_io_buffered.buffered_network_new_len **
                pts_to raw raw_bytes2 **
                pts_to network_out network_out_bytes2 **
                pts_to app_out app_out_bytes2);
      assert (pure (CT.network_bytes_end_to_end_correct
        st1
        st2
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        (Ghost.reveal
          read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
        network_out_bytes
        network_out_bytes2
        app_out_bytes
        app_out_bytes2));
      CT.lemma_network_bytes_end_to_end_correct_preserves_config
        st1
        st2
        read_result.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp
        (Ghost.reveal
          read_result.buffered_network_io_buffered.buffered_network_read.network_read_prefix)
        network_out_bytes
        network_out_bytes2
        app_out_bytes
        app_out_bytes2;
      assert (pure (st2.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (client_buffered_network_io_step_correct
        st2
        read_result
        network_out_bytes2
        app_out_bytes2));
      assert (pure (CT.client_end_to_end_invariant st1 ==>
        CT.client_end_to_end_invariant st2));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st2));
      read_result
    } else {
      assert (pure (Seq.equal buffered_after
        (Seq.slice raw_bytes 0 (SZ.v processed.buffered_network_new_len))));
      let result = {
        buffered_network_io_read_len = 0sz;
        buffered_network_io_buffered = processed;
      };
      assert (pure (
        result.buffered_network_io_buffered.buffered_network_new_len ==
        processed.buffered_network_new_len));
      assert (pure (client_buffered_network_io_step_correct
        st1
        result
        network_out_bytes
        app_out_bytes));
      rewrite (driver_exactly d st1 buffered_after processed.buffered_network_new_len) as
        (driver_exactly d st1 buffered_after
          result.buffered_network_io_buffered.buffered_network_new_len);
      result
    }
  }
}

fn top_driver_process_one_local_action
  (d:top_driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (certificate_public_key_len:SZ.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: ready_local_action_result
  ensures exists* st1 network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (result.ready_local_processed \/
                  result.ready_local_written == 0sz) /\
                 (result.ready_local_processed ==>
                  (CT.client_end_to_end_invariant 'st0 ==>
                   CT.client_end_to_end_invariant st1)) /\
                 (result.ready_local_processed == false ==> st1 == 'st0))
{
  unfold (top_driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let step =
    driver_handshake_step
      d.top_driver_core
      empty_payload
      network_out
      network_out_len
      certificate_public_key_len
      server_finished_payload_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v network_out_len));
  assert (pure (B.length app_out_bytes == SZ.v app_out_len));
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (step.ready_local_processed ==>
    (CT.client_end_to_end_invariant 'st0 ==>
     CT.client_end_to_end_invariant st1)));
  assert (pure (step.ready_local_processed == false ==> st1 == 'st0));
  if step.ready_local_processed {
    fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
    step
  } else {
    assert (pure (step.ready_local_written == 0sz));
    assert (pure (st1 == 'st0));
    let ready = step.ready_local_action.CT.next_local_ready;
    if ready {
      let validate =
        step.ready_local_action.CT.next_local_kind = CT.LocalValidateCertificate;
      if validate {
        assert (pure (C.next_local_action_sound
          'st0
          network_out_len
          certificate_public_key_len
          server_finished_payload_len
          step.ready_local_action));
        assert (pure (Some?
          'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
        assert (pure (Some?
          st1.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_leaf_der));
        let leaf_len =
          driver_copy_certificate_leaf_der
            d.top_driver_core
            auth_leaf_der
            auth_leaf_der_len;
        with auth_leaf_der_bytes.
          assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                  pts_to auth_leaf_der auth_leaf_der_bytes);
        let leaf_fits = SZ.lte leaf_len certificate_public_key_len;
        if leaf_fits {
          assert (pure (SZ.v leaf_len <= SZ.v certificate_public_key_len));
          A.pts_to_len auth_payload;
          assert (pure (A.length auth_payload == SZ.v certificate_public_key_len));
          A.to_mask auth_payload;
          with auth_payload_mask.
            assert (A.pts_to_mask auth_payload #1.0R auth_payload_mask (fun _ -> True));
          assert (pure (Seq.length auth_payload_mask == SZ.v certificate_public_key_len));
          assert (pure (forall (i:nat). i < Seq.length auth_payload_mask ==>
            Some? (Seq.index auth_payload_mask i)));
          let auth_payload_prefix =
            A.sub auth_payload #1.0R #(fun _ -> True) 0sz (SZ.v leaf_len);
          with auth_payload_prefix_mask.
            assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask (fun _ -> True));
          assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask ==>
            Some? (Seq.index auth_payload_prefix_mask i)));
          A.from_mask auth_payload_prefix;
          with auth_payload_prefix_bytes_before.
            assert (pts_to auth_payload_prefix auth_payload_prefix_bytes_before);
          assert (pure (B.length auth_payload_prefix_bytes_before == SZ.v leaf_len));
          let ok =
            O.validate_certificate_for_local_event
              d.top_driver_auth
              #(st1)
              auth_leaf_der
              auth_leaf_der_len
              leaf_len
              auth_payload_prefix
              leaf_len;
          with auth_payload_prefix_bytes.
            assert (O.is_auth_context d.top_driver_auth **
                    pts_to auth_payload_prefix auth_payload_prefix_bytes);
          assert (pure (B.length auth_payload_prefix_bytes == SZ.v leaf_len));
          if ok {
            assert (pure (CT.local_input_wf
              st1
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes));
            let write_result =
              driver_process_local_event
                d.top_driver_core
                CT.LocalValidateCertificate
                auth_payload_prefix
                leaf_len
                network_out
                network_out_len
                app_out
                app_out_len;
            with st2 network_out_bytes2 app_out_bytes2.
              assert (driver_exactly d.top_driver_core st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                      pts_to auth_payload_prefix auth_payload_prefix_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            assert (pure (CT.local_event_end_to_end_correct
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2));
            CT.lemma_local_event_end_to_end_correct_preserves_config
              st1
              st2
              write_result.local_write_resp
              CT.LocalValidateCertificate
              auth_payload_prefix_bytes
              network_out_bytes2
              app_out_bytes2;
            assert (pure (st2.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant st1 ==>
              CT.client_end_to_end_invariant st2));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st2));
            A.to_mask auth_payload_prefix;
            with auth_payload_prefix_mask_after.
              assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask_after ==>
              Some? (Seq.index auth_payload_prefix_mask_after i)));
            rewrite
              (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True))
              as
              (A.pts_to_mask (A.gsub auth_payload 0 (SZ.v leaf_len)) #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            A.return_sub
              auth_payload
              #1.0R
              #auth_payload_mask
              #auth_payload_prefix_mask_after
              #(fun k -> True /\ ~(0 <= k /\ k < SZ.v leaf_len))
              #(fun _ -> True)
              #0
              #(SZ.v leaf_len);
            with auth_payload_joined_mask.
              assert (A.pts_to_mask auth_payload #1.0R auth_payload_joined_mask
                (fun k ->
                  (True /\ ~(0 <= k /\ k < SZ.v leaf_len)) \/
                  (0 <= k /\ k < SZ.v leaf_len /\ True)));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_joined_mask ==>
              Some? (Seq.index auth_payload_joined_mask i)));
            A.from_mask auth_payload;
            with auth_payload_bytes.
              assert (pts_to auth_payload auth_payload_bytes);
            assert (pure (B.length auth_payload_bytes == SZ.v certificate_public_key_len));
            fold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            A.to_mask auth_payload_prefix;
            with auth_payload_prefix_mask_after.
              assert (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_prefix_mask_after ==>
              Some? (Seq.index auth_payload_prefix_mask_after i)));
            rewrite
              (A.pts_to_mask auth_payload_prefix #1.0R auth_payload_prefix_mask_after (fun _ -> True))
              as
              (A.pts_to_mask (A.gsub auth_payload 0 (SZ.v leaf_len)) #1.0R auth_payload_prefix_mask_after (fun _ -> True));
            A.return_sub
              auth_payload
              #1.0R
              #auth_payload_mask
              #auth_payload_prefix_mask_after
              #(fun k -> True /\ ~(0 <= k /\ k < SZ.v leaf_len))
              #(fun _ -> True)
              #0
              #(SZ.v leaf_len);
            with auth_payload_joined_mask.
              assert (A.pts_to_mask auth_payload #1.0R auth_payload_joined_mask
                (fun k ->
                  (True /\ ~(0 <= k /\ k < SZ.v leaf_len)) \/
                  (0 <= k /\ k < SZ.v leaf_len /\ True)));
            assert (pure (forall (i:nat). i < Seq.length auth_payload_joined_mask ==>
              Some? (Seq.index auth_payload_joined_mask i)));
            A.from_mask auth_payload;
            with auth_payload_bytes.
              assert (pts_to auth_payload auth_payload_bytes);
            assert (pure (B.length auth_payload_bytes == SZ.v certificate_public_key_len));
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            step
          }
        } else {
          fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
          step
        }
      } else {
        let verify =
          step.ready_local_action.CT.next_local_kind = CT.LocalVerifyCertificateSignature;
        if verify {
          assert (pure (C.next_local_action_sound
            'st0
            network_out_len
            certificate_public_key_len
            server_finished_payload_len
            step.ready_local_action));
          assert (pure (Some?
            'st0.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
          assert (pure (Some?
            st1.CS.cs_model.CS.model_handshake.CS.hs_buffers.CS.hb_certificate_verify_input));
          assert (pure (Some?
            'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          assert (pure (Some?
            st1.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify));
          let input_len =
            driver_copy_certificate_verify_input
              d.top_driver_core
              auth_cv_input
              auth_cv_input_len;
          with auth_cv_input_bytes.
            assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                    pts_to auth_cv_input auth_cv_input_bytes);
          let signature_snapshot =
            driver_copy_certificate_verify_signature
              d.top_driver_core
              auth_signature
              auth_signature_len;
          with auth_signature_bytes.
            assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                    pts_to auth_signature auth_signature_bytes);
          let ok =
            O.verify_certificate_signature_for_local_event
              d.top_driver_auth
              #(st1)
              auth_cv_input
              auth_cv_input_len
              input_len
              signature_snapshot.CR.cv_signature_scheme
              auth_signature
              auth_signature_len
              signature_snapshot.CR.cv_signature_len;
          if ok {
            assert (pure (CT.local_input_wf
              st1
              CT.LocalVerifyCertificateSignature
              B.empty));
            let write_result =
              driver_process_local_event
                d.top_driver_core
                CT.LocalVerifyCertificateSignature
                empty_payload
                0sz
                network_out
                network_out_len
                app_out
                app_out_len;
            with st2 network_out_bytes2 app_out_bytes2.
              assert (driver_exactly d.top_driver_core st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
                      pts_to empty_payload 'empty_payload_bytes **
                      pts_to network_out network_out_bytes2 **
                      pts_to app_out app_out_bytes2);
            assert (pure (CT.local_event_end_to_end_correct
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2));
            CT.lemma_local_event_end_to_end_correct_preserves_config
              st1
              st2
              write_result.local_write_resp
              CT.LocalVerifyCertificateSignature
              (Ghost.reveal 'empty_payload_bytes)
              network_out_bytes2
              app_out_bytes2;
            assert (pure (st2.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            assert (pure (CT.client_end_to_end_invariant st1 ==>
              CT.client_end_to_end_invariant st2));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st2));
            fold (top_driver_exactly d st2 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            {
              ready_local_action = step.ready_local_action;
              ready_local_processed = true;
              ready_local_resp = write_result.local_write_resp;
              ready_local_written = write_result.local_write_written;
            }
          } else {
            fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
            step
          }
        } else {
          fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
          step
        }
      }
    } else {
      fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
      step
    }
  }
}

fn rec driver_handshake
  (d:top_driver)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.driver_workflow_rx_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1) /\
                 (result.driver_workflow_status == DriverWorkflowOk ==>
                  st1.CS.cs_model.CS.model_control == CS.ControlApplicationData))
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    {
      driver_workflow_status = DriverWorkflowExhausted;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    unfold (top_driver_exactly d 'st0 'buffered buffered_len);
    let snapshot = driver_control_snapshot d.top_driver_core;
    with st_snapshot.
      assert (driver_exactly d.top_driver_core st_snapshot 'buffered buffered_len);
    assert (pure (st_snapshot.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    fold (top_driver_exactly d st_snapshot 'buffered buffered_len);
    let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
    if app_ready {
      assert (pure (CR.control_snapshot_matches snapshot st_snapshot));
      assert (pure (st_snapshot.CS.cs_model.CS.model_control == CS.ControlApplicationData));
      {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len = buffered_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = no_op_io;
      }
    } else {
      let failed = snapshot.CR.snapshot_control_tag = 5uy;
      if failed {
        {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len = buffered_len;
          driver_workflow_local = {
            driver_drain_last = no_op_local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = no_op_io;
        }
      } else {
        let local =
          top_driver_process_one_local_action
            d
            empty_payload
            network_out
            network_out_len
            auth_leaf_der
            auth_leaf_der_len
            auth_payload
            certificate_public_key_len
            auth_cv_input
            auth_cv_input_len
            auth_signature
            auth_signature_len
            server_finished_payload_len
            app_out
            app_out_len;
        with st_local network_out_local auth_leaf_der_local auth_payload_local auth_cv_input_local auth_signature_local app_out_local.
          assert (top_driver_exactly d st_local 'buffered buffered_len **
                  pts_to network_out network_out_local **
                  pts_to auth_leaf_der auth_leaf_der_local **
                  pts_to auth_payload auth_payload_local **
                  pts_to auth_cv_input auth_cv_input_local **
                  pts_to auth_signature auth_signature_local **
                  pts_to app_out app_out_local);
        assert (pure (st_local.CS.cs_model.CS.model_config ==
          st_snapshot.CS.cs_model.CS.model_config));
        assert (pure (st_local.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
        if local.ready_local_processed {
          assert (pure (local.ready_local_processed == true));
          assert (pure (local.ready_local_processed == true ==>
            (CT.client_end_to_end_invariant 'st0 ==>
             CT.client_end_to_end_invariant st_local)));
          assert (pure (CT.client_end_to_end_invariant 'st0 ==>
            CT.client_end_to_end_invariant st_local))
        } else {
          assert (pure (st_local == 'st0));
          assert (pure (CT.client_end_to_end_invariant 'st0 ==>
            CT.client_end_to_end_invariant st_local))
        };
        if local.ready_local_processed {
          let ok = local.ready_local_resp.CT.status = CT.StepOk;
          let wrote_all =
            local.ready_local_written = local.ready_local_resp.CT.network_out_len;
          if (ok && wrote_all) {
            let next_fuel = SZ.sub fuel 1sz;
            assert (pure (SZ.v next_fuel < SZ.v fuel));
            driver_handshake
              d
              empty_payload
              raw
              raw_capacity
              buffered_len
              network_out
              network_out_len
              auth_leaf_der
              auth_leaf_der_len
              auth_payload
              auth_cv_input
              auth_cv_input_len
              auth_signature
              auth_signature_len
              certificate_public_key_len
              server_finished_payload_len
              app_out
              app_out_len
              local_fuel
              next_fuel
          } else {
            {
              driver_workflow_status = DriverWorkflowStepFailed;
              driver_workflow_rx_len = buffered_len;
              driver_workflow_local = {
                driver_drain_last = local;
                driver_drain_exhausted = false;
              };
              driver_workflow_network = no_op_io;
            }
          }
        } else {
          let still_ready = local.ready_local_action.CT.next_local_ready;
          if still_ready {
            {
              driver_workflow_status = DriverWorkflowStepFailed;
              driver_workflow_rx_len = buffered_len;
              driver_workflow_local = {
                driver_drain_last = local;
                driver_drain_exhausted = false;
              };
              driver_workflow_network = no_op_io;
            }
          } else {
            assert (pure (B.length 'old_raw == SZ.v raw_capacity));
            assert (pure (SZ.v buffered_len <= SZ.v raw_capacity));
            assert (pure (Seq.equal 'buffered
              (Seq.slice 'old_raw 0 (SZ.v buffered_len))));
            assert (pure (B.length network_out_local == SZ.v network_out_len));
            assert (pure (B.length app_out_local == SZ.v app_out_len));
            assert (pure (L.max_record_fragment_len <= SZ.v app_out_len));
            assert (pure (st_local == 'st0));
            unfold (top_driver_exactly d st_local 'buffered buffered_len);
            let network =
              driver_progress_buffered_network_step
                d.top_driver_core
                raw
                raw_capacity
                buffered_len
                network_out
                network_out_len
                app_out
                app_out_len;
            with st_network buffered_network raw_network network_out_network app_out_network.
              assert (driver_exactly d.top_driver_core st_network
                        buffered_network
                        network.buffered_network_io_buffered.buffered_network_new_len **
                      pts_to raw raw_network **
                      pts_to network_out network_out_network **
                      pts_to app_out app_out_network);
            assert (pure (st_network.CS.cs_model.CS.model_config ==
              st_local.CS.cs_model.CS.model_config));
            assert (pure (st_network.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            fold (top_driver_exactly d st_network
              buffered_network
              network.buffered_network_io_buffered.buffered_network_new_len);
            assert (pure (CT.client_end_to_end_invariant st_local ==>
              CT.client_end_to_end_invariant st_network));
            assert (pure (CT.client_end_to_end_invariant 'st0 ==>
              CT.client_end_to_end_invariant st_network));
            let net_read =
              network.buffered_network_io_buffered.buffered_network_read;
            let net_resp = net_read.network_read_buffer_resp.CT.response;
            let net_ok = net_resp.CT.status = CT.StepOk;
            let net_need_more = net_resp.CT.status = CT.NeedMoreInput;
            let net_bad_status = (net_ok || net_need_more) = false;
            let net_wrote_all =
              net_read.network_read_written = net_resp.CT.network_out_len;
            let net_short_write = net_ok && (net_wrote_all = false);
            let net_failed = net_bad_status || net_short_write;
            if net_failed {
              let result = {
                driver_workflow_status = DriverWorkflowStepFailed;
                driver_workflow_rx_len =
                  network.buffered_network_io_buffered.buffered_network_new_len;
                driver_workflow_local = {
                  driver_drain_last = local;
                  driver_drain_exhausted = false;
                };
                driver_workflow_network = network;
              };
              assert (pure (result.driver_workflow_status == DriverWorkflowStepFailed));
              assert (pure (result.driver_workflow_rx_len ==
                network.buffered_network_io_buffered.buffered_network_new_len));
              assert (pure (B.length raw_network == SZ.v raw_capacity));
              assert (pure (B.length auth_leaf_der_local == SZ.v auth_leaf_der_len));
              assert (pure (B.length auth_payload_local == SZ.v certificate_public_key_len));
              assert (pure (B.length auth_cv_input_local == SZ.v auth_cv_input_len));
              assert (pure (B.length auth_signature_local == SZ.v auth_signature_len));
              assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
              assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
              assert (pure (Seq.equal buffered_network
                (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
              assert (pure (B.length network_out_network == SZ.v network_out_len));
              assert (pure (B.length app_out_network == SZ.v app_out_len));
              assert (pure (CT.client_end_to_end_invariant 'st0 ==>
                CT.client_end_to_end_invariant st_network));
              assert (pure (result.driver_workflow_status == DriverWorkflowOk ==>
                st_network.CS.cs_model.CS.model_control == CS.ControlApplicationData));
              rewrite (top_driver_exactly
                d
                st_network
                buffered_network
                network.buffered_network_io_buffered.buffered_network_new_len) as
                (top_driver_exactly
                  d
                  st_network
                  buffered_network
                  result.driver_workflow_rx_len);
              result
            } else {
              assert (pure (0 < SZ.v fuel));
              let next_fuel = SZ.sub fuel 1sz;
              assert (pure (SZ.v next_fuel < SZ.v fuel));
              driver_handshake
                d
                empty_payload
                raw
                raw_capacity
                network.buffered_network_io_buffered.buffered_network_new_len
                network_out
                network_out_len
                auth_leaf_der
                auth_leaf_der_len
                auth_payload
                auth_cv_input
                auth_cv_input_len
                auth_signature
                auth_signature_len
                certificate_public_key_len
                server_finished_payload_len
                app_out
                app_out_len
                local_fuel
                next_fuel
            }
          }
        }
      }
    }
  }
}

#push-options "--z3refresh --z3rlimit 10 --split_queries always --z3seed 17"
fn rec driver_receive_application_data
  (d:top_driver)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (auth_leaf_der:array U8.t)
  (auth_leaf_der_len:SZ.t)
  (auth_payload:array U8.t)
  (auth_cv_input:array U8.t)
  (auth_cv_input_len:SZ.t)
  (auth_signature:array U8.t)
  (auth_signature_len:SZ.t)
  (certificate_public_key_len:SZ.t)
  (server_finished_payload_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to auth_leaf_der 'old_auth_leaf_der **
           pts_to auth_payload 'old_auth_payload **
           pts_to auth_cv_input 'old_auth_cv_input **
           pts_to auth_signature 'old_auth_signature **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len /\
                 B.length 'old_auth_payload == SZ.v certificate_public_key_len /\
                 B.length 'old_auth_cv_input == SZ.v auth_cv_input_len /\
                 B.length 'old_auth_signature == SZ.v auth_signature_len /\
                 Bounds.max_handshake_flight_len <= SZ.v auth_leaf_der_len /\
                 SZ.v certificate_public_key_len <= Bounds.max_public_key_len /\
                 Bounds.max_certificate_verify_input_len <= SZ.v auth_cv_input_len /\
                 L.max_signature_len <= SZ.v auth_signature_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
           top_driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to auth_leaf_der auth_leaf_der_bytes **
           pts_to auth_payload auth_payload_bytes **
           pts_to auth_cv_input auth_cv_input_bytes **
           pts_to auth_signature auth_signature_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 B.length auth_leaf_der_bytes == SZ.v auth_leaf_der_len /\
                 B.length auth_payload_bytes == SZ.v certificate_public_key_len /\
                 B.length auth_cv_input_bytes == SZ.v auth_cv_input_len /\
                 B.length auth_signature_bytes == SZ.v auth_signature_len /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.driver_workflow_rx_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 client_receive_observation_network_correct
                   'st0
                   st1
                   (client_driver_workflow_observation result)
                   app_out_bytes /\
                 (CT.client_end_to_end_invariant 'st0 ==>
                  CT.client_end_to_end_invariant st1))
  decreases (SZ.v fuel)
{
  if (fuel = 0sz) {
    let no_op_resp = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.NeedMoreInput;
    };
    let no_op_buffer_resp = {
      CT.response = no_op_resp;
      CT.consumed_len = 0sz;
    };
    let no_op_read = {
      network_read_len = 0sz;
      network_read_buffer_resp = no_op_buffer_resp;
      network_read_written = 0sz;
      network_read_prefix = Ghost.hide B.empty;
    };
    let no_op_buffered = {
      buffered_network_read = no_op_read;
      buffered_network_new_len = buffered_len;
    };
    let no_op_io = {
      buffered_network_io_read_len = 0sz;
      buffered_network_io_buffered = no_op_buffered;
    };
    let no_op_action = {
      CT.next_local_ready = false;
      CT.next_local_kind = CT.LocalFail;
      CT.next_local_payload = CT.LocalPayloadNone;
    };
    let no_op_local = {
      ready_local_action = no_op_action;
      ready_local_processed = false;
      ready_local_resp = no_op_resp;
      ready_local_written = 0sz;
    };
    {
      driver_workflow_status = DriverWorkflowExhausted;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    unfold (top_driver_exactly d 'st0 'buffered buffered_len);
    let network =
      driver_progress_buffered_network_step
        d.top_driver_core
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len;
    with st_network buffered_network raw_network network_out_network app_out_network.
      assert (driver_exactly d.top_driver_core st_network
                buffered_network
                network.buffered_network_io_buffered.buffered_network_new_len **
              pts_to raw raw_network **
              pts_to network_out network_out_network **
              pts_to app_out app_out_network);
    assert (pure (st_network.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    (* Take a control-state snapshot of the post-network-step state while the
       underlying driver resource is still directly available, so that the
       peer close_notify (ControlClosed) case can be detected below without
       recursing to fuel exhaustion. *)
    let snapshot = driver_control_snapshot d.top_driver_core;
    assert (pure (CR.control_snapshot_matches snapshot st_network));
    let net_closed = snapshot.CR.snapshot_control_tag = 4uy;
    fold (top_driver_exactly d st_network
      buffered_network
      network.buffered_network_io_buffered.buffered_network_new_len);
    assert (pure (CT.client_end_to_end_invariant 'st0 ==>
      CT.client_end_to_end_invariant st_network));
    let no_op_resp = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.NeedMoreInput;
    };
    let no_op_action = {
      CT.next_local_ready = false;
      CT.next_local_kind = CT.LocalFail;
      CT.next_local_payload = CT.LocalPayloadNone;
    };
    let no_op_local = {
      ready_local_action = no_op_action;
      ready_local_processed = false;
      ready_local_resp = no_op_resp;
      ready_local_written = 0sz;
    };
    let net_read =
      network.buffered_network_io_buffered.buffered_network_read;
    let net_resp = net_read.network_read_buffer_resp.CT.response;
    let net_ok = net_resp.CT.status = CT.StepOk;
    let net_need_more = net_resp.CT.status = CT.NeedMoreInput;
    let net_bad_status = (net_ok || net_need_more) = false;
    let net_wrote_all =
      net_read.network_read_written = net_resp.CT.network_out_len;
    let net_short_write = net_ok && (net_wrote_all = false);
    let net_failed = net_bad_status || net_short_write;
    if net_failed {
      let result = {
        driver_workflow_status = DriverWorkflowStepFailed;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
      };
      assert (pure (result.driver_workflow_status == DriverWorkflowStepFailed));
      assert (pure (result.driver_workflow_status <> DriverWorkflowExhausted));
      assert (pure (result.driver_workflow_network == network));
      assert (pure (result.driver_workflow_rx_len ==
        network.buffered_network_io_buffered.buffered_network_new_len));
      assert (pure (client_buffered_network_io_step_correct
        st_network
        network
        network_out_network
        app_out_network));
      lemma_client_receive_observation_network_correct_from_buffered
        'st0
        st_network
        st_network
        result
        network_out_network
        app_out_network
        app_out_network;
      assert (pure (B.length raw_network == SZ.v raw_capacity));
      assert (pure (B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len));
      assert (pure (B.length 'old_auth_payload == SZ.v certificate_public_key_len));
      assert (pure (B.length 'old_auth_cv_input == SZ.v auth_cv_input_len));
      assert (pure (B.length 'old_auth_signature == SZ.v auth_signature_len));
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
      assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
      assert (pure (Seq.equal buffered_network
        (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
      assert (pure (B.length network_out_network == SZ.v network_out_len));
      assert (pure (B.length app_out_network == SZ.v app_out_len));
      assert (pure (client_receive_observation_network_correct
        'st0
        st_network
        (client_driver_workflow_observation result)
        app_out_network));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st_network));
      rewrite (top_driver_exactly
        d
        st_network
        buffered_network
        network.buffered_network_io_buffered.buffered_network_new_len) as
        (top_driver_exactly
          d
          st_network
          buffered_network
          result.driver_workflow_rx_len);
      result
    } else {
    let app_ready =
      network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len =
      0sz;
    if (app_ready = false) {
      assert (pure (client_buffered_network_io_step_correct
        st_network
        network
        network_out_network
        app_out_network));
      let result = {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
      };
      assert (pure (result.driver_workflow_status == DriverWorkflowOk));
      assert (pure (result.driver_workflow_network == network));
      lemma_client_receive_observation_network_correct_from_buffered
        'st0
        st_network
        st_network
        result
        network_out_network
        app_out_network
        app_out_network;
      assert (pure (client_receive_observation_network_correct
        'st0
        st_network
        (client_driver_workflow_observation result)
        app_out_network));
      assert (pure (result.driver_workflow_rx_len ==
        network.buffered_network_io_buffered.buffered_network_new_len));
      assert (pure (B.length raw_network == SZ.v raw_capacity));
      assert (pure (B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len));
      assert (pure (B.length 'old_auth_payload == SZ.v certificate_public_key_len));
      assert (pure (B.length 'old_auth_cv_input == SZ.v auth_cv_input_len));
      assert (pure (B.length 'old_auth_signature == SZ.v auth_signature_len));
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
      assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
      assert (pure (Seq.equal buffered_network
        (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
      assert (pure (B.length network_out_network == SZ.v network_out_len));
      assert (pure (B.length app_out_network == SZ.v app_out_len));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st_network));
      rewrite (top_driver_exactly
        d
        st_network
        buffered_network
        network.buffered_network_io_buffered.buffered_network_new_len) as
        (top_driver_exactly
          d
          st_network
          buffered_network
          result.driver_workflow_rx_len);
      result
    } else if (net_ok && net_closed) {
      (* A StepOk network step produced zero application bytes and the
         connection control state is ControlClosed: the peer sent
         close_notify. Report this to the caller directly instead of
         draining local actions (none is legal once ControlClosed) and
         recursing until [fuel] is exhausted. *)
      assert (pure (st_network.CS.cs_model.CS.model_control == CS.ControlClosed));
      assert (pure (client_buffered_network_io_step_correct
        st_network
        network
        network_out_network
        app_out_network));
      let result = {
        driver_workflow_status = DriverWorkflowClosed;
        driver_workflow_rx_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = network;
      };
      assert (pure (result.driver_workflow_status == DriverWorkflowClosed));
      assert (pure (result.driver_workflow_status <> DriverWorkflowExhausted));
      assert (pure (result.driver_workflow_network == network));
      assert (pure (result.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response.CT.app_out_len == 0sz));
      lemma_client_receive_observation_network_correct_from_buffered
        'st0
        st_network
        st_network
        result
        network_out_network
        app_out_network
        app_out_network;
      assert (pure (client_receive_observation_network_correct
        'st0
        st_network
        (client_driver_workflow_observation result)
        app_out_network));
      assert (pure (result.driver_workflow_rx_len ==
        network.buffered_network_io_buffered.buffered_network_new_len));
      assert (pure (B.length raw_network == SZ.v raw_capacity));
      assert (pure (B.length 'old_auth_leaf_der == SZ.v auth_leaf_der_len));
      assert (pure (B.length 'old_auth_payload == SZ.v certificate_public_key_len));
      assert (pure (B.length 'old_auth_cv_input == SZ.v auth_cv_input_len));
      assert (pure (B.length 'old_auth_signature == SZ.v auth_signature_len));
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
      assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
      assert (pure (Seq.equal buffered_network
        (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
      assert (pure (B.length network_out_network == SZ.v network_out_len));
      assert (pure (B.length app_out_network == SZ.v app_out_len));
      assert (pure (CT.client_end_to_end_invariant 'st0 ==>
        CT.client_end_to_end_invariant st_network));
      rewrite (top_driver_exactly
        d
        st_network
        buffered_network
        network.buffered_network_io_buffered.buffered_network_new_len) as
        (top_driver_exactly
          d
          st_network
          buffered_network
          result.driver_workflow_rx_len);
      result
    } else {
      let local =
        top_driver_process_one_local_action
          d
          empty_payload
          network_out
          network_out_len
          auth_leaf_der
          auth_leaf_der_len
          auth_payload
          certificate_public_key_len
          auth_cv_input
          auth_cv_input_len
          auth_signature
          auth_signature_len
          server_finished_payload_len
          app_out
          app_out_len;
      with st_local network_out_local auth_leaf_der_local auth_payload_local auth_cv_input_local auth_signature_local app_out_local.
        assert (top_driver_exactly d st_local
                  buffered_network
                  network.buffered_network_io_buffered.buffered_network_new_len **
                pts_to network_out network_out_local **
                pts_to auth_leaf_der auth_leaf_der_local **
                pts_to auth_payload auth_payload_local **
                pts_to auth_cv_input auth_cv_input_local **
                pts_to auth_signature auth_signature_local **
                pts_to app_out app_out_local);
      assert (pure (st_local.CS.cs_model.CS.model_config ==
        st_network.CS.cs_model.CS.model_config));
      assert (pure (st_local.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      if local.ready_local_processed {
        assert (pure (local.ready_local_processed == true));
        assert (pure (local.ready_local_processed == true ==>
          (CT.client_end_to_end_invariant st_network ==>
           CT.client_end_to_end_invariant st_local)));
        assert (pure (CT.client_end_to_end_invariant st_network ==>
          CT.client_end_to_end_invariant st_local));
        assert (pure (CT.client_end_to_end_invariant 'st0 ==>
          CT.client_end_to_end_invariant st_local))
      } else {
        assert (pure (st_local == st_network));
        assert (pure (CT.client_end_to_end_invariant 'st0 ==>
          CT.client_end_to_end_invariant st_local))
      };
      let local_processed = local.ready_local_processed;
      let local_ready = local.ready_local_action.CT.next_local_ready;
      let local_ok = local.ready_local_resp.CT.status = CT.StepOk;
      let local_wrote_all =
        local.ready_local_written = local.ready_local_resp.CT.network_out_len;
      let local_short_write = local_processed && local_ok && (local_wrote_all = false);
      let local_failed =
        (local_processed && ((local_ok = false) || local_short_write)) ||
        ((local_processed = false) && local_ready);
      if local_failed {
        let result = {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len =
            network.buffered_network_io_buffered.buffered_network_new_len;
          driver_workflow_local = {
            driver_drain_last = local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = network;
        };
        assert (pure (result.driver_workflow_status == DriverWorkflowStepFailed));
        assert (pure (result.driver_workflow_status <> DriverWorkflowExhausted));
        assert (pure (result.driver_workflow_network == network));
        assert (pure (result.driver_workflow_rx_len ==
          network.buffered_network_io_buffered.buffered_network_new_len));
        assert (pure (result.driver_workflow_status == DriverWorkflowOk ==>
          st_network == st_local /\ Seq.equal app_out_network app_out_local));
        assert (pure (client_buffered_network_io_step_correct
          st_network
          network
          network_out_network
          app_out_network));
        lemma_client_receive_observation_network_correct_from_buffered
          'st0
          st_local
          st_network
          result
          network_out_network
          app_out_network
          app_out_local;
        assert (pure (client_receive_observation_network_correct
          'st0
          st_local
          (client_driver_workflow_observation result)
          app_out_local));
        assert (pure (B.length raw_network == SZ.v raw_capacity));
        assert (pure (B.length auth_leaf_der_local == SZ.v auth_leaf_der_len));
        assert (pure (B.length auth_payload_local == SZ.v certificate_public_key_len));
        assert (pure (B.length auth_cv_input_local == SZ.v auth_cv_input_len));
        assert (pure (B.length auth_signature_local == SZ.v auth_signature_len));
        assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
        assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
        assert (pure (Seq.equal buffered_network
          (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
        assert (pure (B.length network_out_local == SZ.v network_out_len));
        assert (pure (B.length app_out_local == SZ.v app_out_len));
        assert (pure (CT.client_end_to_end_invariant 'st0 ==>
          CT.client_end_to_end_invariant st_local));
        rewrite (top_driver_exactly
          d
          st_local
          buffered_network
          network.buffered_network_io_buffered.buffered_network_new_len) as
          (top_driver_exactly
            d
            st_local
            buffered_network
            result.driver_workflow_rx_len);
        result
      } else {
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        driver_receive_application_data
          d
          empty_payload
          raw
          raw_capacity
          network.buffered_network_io_buffered.buffered_network_new_len
          network_out
          network_out_len
          auth_leaf_der
          auth_leaf_der_len
          auth_payload
          auth_cv_input
          auth_cv_input_len
          auth_signature
          auth_signature_len
          certificate_public_key_len
          server_finished_payload_len
          app_out
          app_out_len
          local_fuel
          next_fuel
      }
    }
    }
  }
}
#pop-options

fn rec driver_await_peer_close_notify
  (d:driver)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires driver_exactly d 'st0 'buffered buffered_len **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 buffered_after raw_bytes network_out_bytes app_out_bytes.
           driver_exactly d st1 buffered_after result.driver_workflow_rx_len **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length buffered_after == SZ.v result.driver_workflow_rx_len /\
                 Seq.equal buffered_after
                   (Seq.slice raw_bytes 0 (SZ.v result.driver_workflow_rx_len)) /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config)
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = no_op_resp;
    ready_local_written = 0sz;
  };
  if (fuel = 0sz) {
    {
      driver_workflow_status = DriverWorkflowExhausted;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let snapshot = driver_control_snapshot d;
    with st_snapshot.
      assert (driver_exactly d st_snapshot 'buffered buffered_len);
    assert (pure (st_snapshot.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    let closed = snapshot.CR.snapshot_control_tag = 4uy;
    if closed {
      {
        driver_workflow_status = DriverWorkflowOk;
        driver_workflow_rx_len = buffered_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = no_op_io;
      }
    } else {
      let network =
        driver_progress_buffered_network_step
          d
          raw
          raw_capacity
          buffered_len
          network_out
          network_out_len
          app_out
          app_out_len;
      with st_network buffered_network raw_network network_out_network app_out_network.
        assert (driver_exactly d st_network
                  buffered_network
                  network.buffered_network_io_buffered.buffered_network_new_len **
                pts_to raw raw_network **
                pts_to network_out network_out_network **
                pts_to app_out app_out_network);
      assert (pure (st_network.CS.cs_model.CS.model_config ==
        st_snapshot.CS.cs_model.CS.model_config));
      assert (pure (st_network.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      let net_read =
        network.buffered_network_io_buffered.buffered_network_read;
      let net_resp = net_read.network_read_buffer_resp.CT.response;
      let net_ok = net_resp.CT.status = CT.StepOk;
      let net_need_more = net_resp.CT.status = CT.NeedMoreInput;
      let net_bad_status = (net_ok || net_need_more) = false;
      let net_wrote_all =
        net_read.network_read_written = net_resp.CT.network_out_len;
      let net_short_write = net_ok && (net_wrote_all = false);
      let net_failed = net_bad_status || net_short_write;
      if net_failed {
        let result = {
          driver_workflow_status = DriverWorkflowStepFailed;
          driver_workflow_rx_len =
            network.buffered_network_io_buffered.buffered_network_new_len;
          driver_workflow_local = {
            driver_drain_last = no_op_local;
            driver_drain_exhausted = false;
          };
          driver_workflow_network = network;
        };
        assert (pure (result.driver_workflow_rx_len ==
          network.buffered_network_io_buffered.buffered_network_new_len));
        assert (pure (B.length raw_network == SZ.v raw_capacity));
        assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity));
        assert (pure (B.length buffered_network == SZ.v result.driver_workflow_rx_len));
        assert (pure (Seq.equal buffered_network
          (Seq.slice raw_network 0 (SZ.v result.driver_workflow_rx_len))));
        assert (pure (B.length network_out_network == SZ.v network_out_len));
        assert (pure (B.length app_out_network == SZ.v app_out_len));
        rewrite (driver_exactly
          d
          st_network
          buffered_network
          network.buffered_network_io_buffered.buffered_network_new_len) as
          (driver_exactly
            d
            st_network
            buffered_network
            result.driver_workflow_rx_len);
        result
      } else {
        assert (pure (0 < SZ.v fuel));
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        let next_buffered_len =
          network.buffered_network_io_buffered.buffered_network_new_len;
        assert (pure (B.length raw_network == SZ.v raw_capacity));
        assert (pure (SZ.v next_buffered_len <= SZ.v raw_capacity));
        assert (pure (B.length buffered_network == SZ.v next_buffered_len));
        assert (pure (Seq.equal buffered_network
          (Seq.slice raw_network 0 (SZ.v next_buffered_len))));
        assert (pure (B.length network_out_network == SZ.v network_out_len));
        assert (pure (B.length app_out_network == SZ.v app_out_len));
        assert (pure (L.max_record_fragment_len <= SZ.v app_out_len));
        rewrite (driver_exactly
          d
          st_network
          buffered_network
          network.buffered_network_io_buffered.buffered_network_new_len) as
          (driver_exactly
            d
            st_network
            buffered_network
            next_buffered_len);
        driver_await_peer_close_notify
          d
          raw
          raw_capacity
          next_buffered_len
          network_out
          network_out_len
          app_out
          app_out_len
          next_fuel
      }
    }
  }
}

fn send_application_data_once
  (c:C.client)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           channel_open ch 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           C.connection_exactly c st1 **
           channel_open ch st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  process_local_event_and_write_once
    c
    ch
    CT.LocalSendApplicationData
    payload
    payload_len
    network_out
    network_out_len
    app_out
    app_out_len
}

fn driver_send_application_data
  (d:driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let result =
    send_application_data_once
      d.driver_client
      d.driver_channel
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            channel_open d.driver_channel st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    CT.LocalSendApplicationData
    (Ghost.reveal 'payload_bytes)
    network_out_bytes
    app_out_bytes;
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn top_driver_send_application_data
  (d:top_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires top_driver_exactly d 'st0 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                  'st0
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes))
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           top_driver_exactly d st1 'buffered 'pending_len **
           pts_to payload 'payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                  'st0
                  st1
                  result.local_write_resp
                  CT.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                 SZ.v result.local_write_written <=
                 SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (top_driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  let result =
    driver_send_application_data
      d.top_driver_core
      payload
      payload_len
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (driver_exactly d.top_driver_core st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to payload 'payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  fold (top_driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn driver_send_close_notify
  (d:driver)
  (empty_payload:array U8.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires driver_exactly d 'st0 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns result: local_write_result
  ensures exists* st1 network_out_bytes app_out_bytes.
           driver_exactly d st1 'buffered 'pending_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 CT.local_event_end_to_end_correct
                   'st0
                   st1
                   result.local_write_resp
                   CT.LocalSendCloseNotify
                   (Ghost.reveal 'empty_payload_bytes)
                   network_out_bytes
                   app_out_bytes /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 result.local_write_written ==
                   result.local_write_resp.CT.network_out_len /\
                 (result.local_write_resp.CT.status == CT.StepOk ==>
                  SZ.v result.local_write_written <=
                  SZ.v result.local_write_resp.CT.network_out_len))
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  assert (pure (CT.local_input_wf
    'st0
    CT.LocalSendCloseNotify
    (Ghost.reveal 'empty_payload_bytes)));
  let result =
    process_local_event_and_write_once
      d.driver_client
      d.driver_channel
      CT.LocalSendCloseNotify
      empty_payload
      0sz
      network_out
      network_out_len
      app_out
      app_out_len;
  with st1 network_out_bytes app_out_bytes.
    assert (C.connection_exactly d.driver_client st1 **
            channel_open d.driver_channel st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len) **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_bytes **
            pts_to app_out app_out_bytes);
  CT.lemma_local_event_end_to_end_correct_preserves_config
    'st0
    st1
    result.local_write_resp
    CT.LocalSendCloseNotify
    (Ghost.reveal 'empty_payload_bytes)
    network_out_bytes
    app_out_bytes;
  fold (driver_exactly d st1 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  result
}

fn rec driver_close_workflow
  (d:top_driver)
  (wait_for_peer:bool)
  (empty_payload:array U8.t)
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires top_driver_exactly d 'st0 'buffered buffered_len **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw 'old_raw **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'empty_payload_bytes == 0 /\
                 B.length 'old_raw == SZ.v raw_capacity /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 B.length 'buffered == SZ.v buffered_len /\
                 Seq.equal 'buffered
                   (Seq.slice 'old_raw 0 (SZ.v buffered_len)) /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 L.max_record_fragment_len <= SZ.v app_out_len)
  returns result: driver_workflow_result
  ensures exists* st1 raw_bytes network_out_bytes app_out_bytes.
           C.connection_exactly d.top_driver_core.driver_client st1 **
           pts_to empty_payload 'empty_payload_bytes **
           pts_to raw raw_bytes **
           pts_to network_out network_out_bytes **
           pts_to app_out app_out_bytes **
           pure (B.length raw_bytes == SZ.v raw_capacity /\
                 SZ.v result.driver_workflow_rx_len <= SZ.v raw_capacity /\
                 B.length network_out_bytes == SZ.v network_out_len /\
                 B.length app_out_bytes == SZ.v app_out_len /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 (exists st_close_notify.
                   client_driver_close_correct
                     'st0
                     st_close_notify
                     result.driver_workflow_status
                     wait_for_peer))
  decreases (SZ.v fuel)
{
  unfold (top_driver_exactly d 'st0 'buffered buffered_len);
  let close_result =
    driver_send_close_notify
      d.top_driver_core
      empty_payload
      network_out
      network_out_len
      app_out
      app_out_len;
  with st_after_close_notify network_out_after_close app_out_after_close.
    assert (driver_exactly d.top_driver_core st_after_close_notify 'buffered buffered_len **
            pts_to empty_payload 'empty_payload_bytes **
            pts_to network_out network_out_after_close **
            pts_to app_out app_out_after_close);
  assert (pure (st_after_close_notify.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  assert (pure (forall (i:nat{i < B.length (Ghost.reveal 'empty_payload_bytes)}).
    Seq.index (Ghost.reveal 'empty_payload_bytes) i == Seq.index B.empty i));
  Seq.lemma_eq_intro (Ghost.reveal 'empty_payload_bytes) B.empty;
  Seq.lemma_eq_elim (Ghost.reveal 'empty_payload_bytes) B.empty;
  lemma_local_event_wire_lengths
    'st0
    st_after_close_notify
    close_result.local_write_resp
    CT.LocalSendCloseNotify
    B.empty
    network_out_after_close
    app_out_after_close;
  assert (pure (Seq.equal
    st_after_close_notify.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (CT.response_network_out close_result.local_write_resp network_out_after_close))));
  assert (pure (client_driver_local_write_correct
    'st0
    st_after_close_notify
    close_result.local_write_resp
    CT.LocalSendCloseNotify
    B.empty
    'st0.CS.cs_wire_log.CL.raw_sent
    st_after_close_notify.CS.cs_wire_log.CL.raw_sent));
  let no_op_resp = {
    CT.network_out_len = 0sz;
    CT.app_out_len = 0sz;
    CT.status = CT.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    CT.response = no_op_resp;
    CT.consumed_len = 0sz;
  };
  let no_op_read = {
    network_read_len = 0sz;
    network_read_buffer_resp = no_op_buffer_resp;
    network_read_written = 0sz;
    network_read_prefix = Ghost.hide B.empty;
  };
  let no_op_buffered = {
    buffered_network_read = no_op_read;
    buffered_network_new_len = buffered_len;
  };
  let no_op_io = {
    buffered_network_io_read_len = 0sz;
    buffered_network_io_buffered = no_op_buffered;
  };
  let no_op_action = {
    CT.next_local_ready = false;
    CT.next_local_kind = CT.LocalFail;
    CT.next_local_payload = CT.LocalPayloadNone;
  };
  let no_op_local = {
    ready_local_action = no_op_action;
    ready_local_processed = false;
    ready_local_resp = close_result.local_write_resp;
    ready_local_written = close_result.local_write_written;
  };
  let close_ok = close_result.local_write_resp.CT.status = CT.StepOk;
  let close_wrote_all =
    close_result.local_write_written = close_result.local_write_resp.CT.network_out_len;
  assert (pure (close_wrote_all == true));
  let close_failed = (close_ok && close_wrote_all) = false;
  if close_failed {
   assert (pure (close_ok == false));
   assert (pure (close_result.local_write_resp.CT.status <> CT.StepOk));
   assert (pure (client_driver_close_status_correct
     wait_for_peer
     DriverWorkflowStepFailed
     close_result.local_write_resp));
   assert (pure (client_driver_close_correct
     'st0
     st_after_close_notify
     DriverWorkflowStepFailed
     wait_for_peer));
   assert (pure (exists st_close_notify.
     client_driver_close_correct
       'st0
       st_close_notify
       DriverWorkflowStepFailed
       wait_for_peer));
   unfold (driver_exactly d.top_driver_core st_after_close_notify 'buffered buffered_len);
   unfold (channel_open d.top_driver_core.driver_channel st_after_close_notify 'buffered buffered_len);
   with received sent.
     assert (IO.is_channel d.top_driver_core.driver_channel received sent **
             pure (client_driver_wire_logs_match st_after_close_notify received sent 'buffered buffered_len));
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    {
      driver_workflow_status = DriverWorkflowStepFailed;
      driver_workflow_rx_len = buffered_len;
      driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  } else if wait_for_peer {
    let waited =
      driver_await_peer_close_notify
        d.top_driver_core
        raw
        raw_capacity
        buffered_len
        network_out
        network_out_len
        app_out
        app_out_len
        fuel;
    with st_wait buffered_wait raw_wait network_out_wait app_out_wait.
      assert (driver_exactly d.top_driver_core st_wait buffered_wait waited.driver_workflow_rx_len **
              pts_to raw raw_wait **
              pts_to network_out network_out_wait **
              pts_to app_out app_out_wait);
    assert (pure (st_wait.CS.cs_model.CS.model_config ==
      st_after_close_notify.CS.cs_model.CS.model_config));
    assert (pure (st_wait.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    unfold (driver_exactly d.top_driver_core st_wait buffered_wait waited.driver_workflow_rx_len);
    unfold (channel_open d.top_driver_core.driver_channel st_wait buffered_wait waited.driver_workflow_rx_len);
    with received sent.
     assert (IO.is_channel d.top_driver_core.driver_channel received sent **
             pure (client_driver_wire_logs_match st_wait received sent buffered_wait waited.driver_workflow_rx_len));
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
    let wait_ok = waited.driver_workflow_status = DriverWorkflowOk;
    if wait_ok {
      assert (pure (close_ok == true));
      assert (pure (client_driver_close_status_correct
        wait_for_peer
        DriverWorkflowClosed
        close_result.local_write_resp));
      assert (pure (client_driver_close_correct
        'st0
        st_after_close_notify
        DriverWorkflowClosed
        wait_for_peer));
      assert (pure (exists st_close_notify.
        client_driver_close_correct
          'st0
          st_close_notify
          DriverWorkflowClosed
          wait_for_peer));
      {
        driver_workflow_status = DriverWorkflowClosed;
        driver_workflow_rx_len = waited.driver_workflow_rx_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = waited.driver_workflow_network;
      }
    } else {
      assert (pure (close_ok == true));
      assert (pure (client_driver_close_status_correct
        wait_for_peer
        waited.driver_workflow_status
        close_result.local_write_resp));
      assert (pure (client_driver_close_correct
        'st0
        st_after_close_notify
        waited.driver_workflow_status
        wait_for_peer));
      assert (pure (exists st_close_notify.
        client_driver_close_correct
          'st0
          st_close_notify
          waited.driver_workflow_status
          wait_for_peer));
      {
        driver_workflow_status = waited.driver_workflow_status;
        driver_workflow_rx_len = waited.driver_workflow_rx_len;
        driver_workflow_local = {
          driver_drain_last = no_op_local;
          driver_drain_exhausted = false;
        };
        driver_workflow_network = waited.driver_workflow_network;
      }
    }
  } else {
   unfold (driver_exactly d.top_driver_core st_after_close_notify 'buffered buffered_len);
   unfold (channel_open d.top_driver_core.driver_channel st_after_close_notify 'buffered buffered_len);
   with received sent.
     assert (IO.is_channel d.top_driver_core.driver_channel received sent **
             pure (client_driver_wire_logs_match st_after_close_notify received sent 'buffered buffered_len));
    IO.close d.top_driver_core.driver_channel;
    O.auth_context_free d.top_driver_auth;
   assert (pure (wait_for_peer == false));
   assert (pure (close_ok == true));
   assert (pure (client_driver_close_status_correct
     wait_for_peer
     DriverWorkflowClosed
     close_result.local_write_resp));
   assert (pure (client_driver_close_correct
     'st0
     st_after_close_notify
     DriverWorkflowClosed
     wait_for_peer));
   assert (pure (exists st_close_notify.
     client_driver_close_correct
       'st0
       st_close_notify
       DriverWorkflowClosed
       wait_for_peer));
   {
     driver_workflow_status = DriverWorkflowClosed;
     driver_workflow_rx_len = buffered_len;
     driver_workflow_local = {
        driver_drain_last = no_op_local;
        driver_drain_exhausted = false;
      };
      driver_workflow_network = no_op_io;
    }
  }
}

fn driver_close (d:driver)
  requires driver_exactly d 'st0 'buffered 'pending_len
  ensures C.connection_exactly d.driver_client 'st0
{
  unfold (driver_exactly d 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  unfold (channel_open d.driver_channel 'st0 (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len));
  with received sent.
    assert (IO.is_channel d.driver_channel received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) (Ghost.reveal 'pending_len)));
  IO.close d.driver_channel
}

inline_for_extraction
fn free_client_driver_buffers
  (d:client_driver)
  (buffered_len:SZ.t)
  requires (exists* buffered. client_driver_buffers d buffered buffered_len)
  ensures emp
{
  with buffered.
    assert (client_driver_buffers d buffered buffered_len);
  unfold (client_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
    assert (Box.pts_to d.client_driver_buffered_len buffered_len **
            V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.client_driver_raw #1.0R raw **
            V.pts_to d.client_driver_network_out #1.0R network_out **
            V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
            V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
            V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
            V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
            V.pts_to d.client_driver_app_out #1.0R app_out **
            V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
  V.free d.client_driver_empty_payload;
  V.free d.client_driver_raw;
  V.free d.client_driver_network_out;
  V.free d.client_driver_auth_leaf_der;
  V.free d.client_driver_auth_payload;
  V.free d.client_driver_auth_cv_input;
  V.free d.client_driver_auth_signature;
  V.free d.client_driver_app_out;
  V.free d.client_driver_local_app_out;
  Box.free d.client_driver_buffered_len;
}

inline_for_extraction
fn free_disconnected_client_driver
  (d:client_driver)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.client_driver_client 'st0 **
           client_driver_canonical_seed d **
           O.is_auth_context d.client_driver_auth **
           Box.pts_to d.client_driver_channel no_channel **
           (exists* buffered. client_driver_buffers d buffered buffered_len)
  ensures client_driver_closed d 'st0
{
  O.auth_context_free d.client_driver_auth;
  Box.free d.client_driver_channel;
  free_client_driver_buffers d buffered_len;
  fold (client_driver_closed d 'st0);
}

inline_for_extraction
fn close_failed_connect
  (d:client_driver)
  (ch:IO.channel)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.client_driver_client 'st0 **
           client_driver_canonical_seed d **
           O.is_auth_context d.client_driver_auth **
           channel_open ch 'st0 'buffered buffered_len **
           Box.pts_to d.client_driver_channel no_channel **
           client_driver_buffers d (Ghost.reveal 'buffered) buffered_len
  ensures client_driver_closed d 'st0
{
  unfold (channel_open ch 'st0 'buffered buffered_len);
  with received sent.
    assert (IO.is_channel ch received sent **
            pure (client_driver_wire_logs_match 'st0 received sent (Ghost.reveal 'buffered) buffered_len));
  IO.close ch;
  free_disconnected_client_driver d buffered_len;
}

noextract
fn connect_endpoint
  (d:client_driver)
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (fuel:SZ.t)
  requires client_driver_endpoint_live d 'st0 **
           pts_to connect_host 'connect_host_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len)
  returns result:option EP.client_endpoint_run_result
  ensures pts_to connect_host 'connect_host_bytes **
          (let cfg = client_driver_endpoint_config d in
           let frame = client_driver_endpoint_workflow_frame d in
           match result with
           | None ->
             client_driver_endpoint_live d 'st0
           | Some _ ->
             exists* st1 received1 sent1.
               client_driver_endpoint_connected d cfg frame st1 received1 sent1)
{
  let cfg = client_driver_endpoint_config d;
  let frame = client_driver_endpoint_workflow_frame d;
  unfold (client_driver_endpoint_live d 'st0);
  let ch_opt = IO.connect_tcp connect_host connect_host_len port;
  match ch_opt {
    None -> {
      fold (client_driver_endpoint_live d 'st0);
      None
    }
    Some ch -> {
      Box.(d.client_driver_channel := Some ch);
      unfold (client_driver_buffers d B.empty 0sz);
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
        assert (
          Box.pts_to d.client_driver_buffered_len 0sz **
          V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
          V.pts_to d.client_driver_raw #1.0R raw **
          V.pts_to d.client_driver_network_out #1.0R network_out **
          V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
          V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
          V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
          V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
          V.pts_to d.client_driver_app_out #1.0R app_out **
          V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
      V.to_array_pts_to d.client_driver_empty_payload;
      V.to_array_pts_to d.client_driver_app_out;
      V.to_array_pts_to d.client_driver_local_app_out;
      assert (pure (forall (i:nat{i < B.length empty_payload}).
        Seq.index empty_payload i == Seq.index B.empty i));
      Seq.lemma_eq_intro empty_payload B.empty;
      Seq.lemma_eq_elim empty_payload B.empty;
      rewrite
        (pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload)
        as
        (pts_to (V.vec_to_array d.client_driver_empty_payload) B.empty);
      assert (pure (EP.client_endpoint_config_wf cfg frame));
      rewrite
        (pts_to (V.vec_to_array d.client_driver_app_out) app_out)
        as
        (pts_to
          frame.EP.client_ep_query.CQueries.client_query_network_app_out
          app_out);
      rewrite
        (pts_to (V.vec_to_array d.client_driver_empty_payload) B.empty)
        as
        (pts_to
          frame.EP.client_ep_query.CQueries.client_query_local_payload
          B.empty);
      rewrite
        (pts_to (V.vec_to_array d.client_driver_local_app_out) local_app_out)
        as
        (pts_to
          frame.EP.client_ep_query.CQueries.client_query_local_app_out
          local_app_out);
      with app_out.
      fold (CQueries.client_network_persistent_resource frame.EP.client_ep_query);
      with local_app_out.
      fold (CQueries.client_local_persistent_resource frame.EP.client_ep_query);
      fold (CQueries.client_next_local_action_frame_ready
        (client_driver_canonical d)
        cfg
        frame.EP.client_ep_query
        'st0);
      rewrite (O.is_auth_context d.client_driver_auth)
        as (O.is_auth_context frame.EP.client_ep_auth);
      rewrite
        (V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der)
        as
        (V.pts_to frame.EP.client_ep_auth_leaf_der #1.0R auth_leaf_der);
      rewrite
        (V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input)
        as
        (V.pts_to frame.EP.client_ep_auth_cv_input #1.0R auth_cv_input);
      rewrite
        (V.pts_to d.client_driver_auth_signature #1.0R auth_signature)
        as
        (V.pts_to frame.EP.client_ep_auth_signature #1.0R auth_signature);
      rewrite
        (V.pts_to d.client_driver_auth_payload #1.0R auth_payload)
        as
        (V.pts_to frame.EP.client_ep_auth_payload #1.0R auth_payload);
      with auth_leaf_der auth_cv_input auth_signature.
      fold (EP.client_endpoint_auth_static_ready frame);
      with auth_payload.
      fold (EP.client_endpoint_auth_payload_ready frame);
      fold (EP.client_endpoint_auth_ready frame);
      fold (EP.client_endpoint_frame_ready
        (client_driver_canonical d)
        cfg
        frame
        'st0);
      rewrite
        (V.pts_to d.client_driver_raw #1.0R raw)
        as
        (V.pts_to frame.EP.client_ep_raw #1.0R raw);
      rewrite
        (V.pts_to d.client_driver_network_out #1.0R network_out)
        as
        (V.pts_to frame.EP.client_ep_network_out #1.0R network_out);
      let empty_received = B.empty;
      with empty_received raw network_out.
      fold (EP.client_endpoint_io_ready
        (client_driver_canonical d)
        ch
        frame
        B.empty
        B.empty
        'st0);
      let run_result =
        EP.client_endpoint_run_workflow
          (client_driver_canonical d)
          cfg
          frame
          ch
          d.client_driver_buffered_len
          false
          true
          false
          fuel
          (Ghost.hide B.empty)
          (Ghost.hide B.empty)
          'st0;
      with received1 sent1 st1 buffered_len1.
        assert (
          CP.client_invariant
            (client_driver_canonical d)
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1) **
          EP.client_endpoint_frame_ready
            (client_driver_canonical d)
            cfg
            frame
            (Ghost.reveal st1) **
          EP.client_endpoint_io_ready
            (client_driver_canonical d)
            ch
            frame
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1) **
          Box.pts_to d.client_driver_buffered_len buffered_len1);
      rewrite
        (EP.client_endpoint_frame_ready
          (client_driver_canonical d)
          cfg
          frame
          (Ghost.reveal st1))
        as
        (EP.client_endpoint_frame_ready
          (client_driver_canonical d)
          (client_driver_endpoint_config d)
          (client_driver_endpoint_workflow_frame d)
          (Ghost.reveal st1));
      rewrite
        (EP.client_endpoint_io_ready
          (client_driver_canonical d)
          ch
          frame
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1))
        as
        (EP.client_endpoint_io_ready
          (client_driver_canonical d)
          ch
          (client_driver_endpoint_workflow_frame d)
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1));
      with ch buffered_len1.
      fold (client_driver_endpoint_connected
        d
        (client_driver_endpoint_config d)
        (client_driver_endpoint_workflow_frame d)
        (Ghost.reveal st1)
        (Ghost.reveal received1)
        (Ghost.reveal sent1));
      Some run_result
    }
  }
}

fn connect
  (d:client_driver)
  (connect_host:array U8.t)
  (connect_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_live d 'st0 **
           pts_to connect_host 'connect_host_bytes **
           pure (B.length 'connect_host_bytes == SZ.v connect_host_len)
  returns status:driver_workflow_status
  ensures exists* st1.
          pts_to connect_host 'connect_host_bytes **
          (match status with
           | DriverWorkflowOk ->
             exists* received sent.
               client_driver_connected d st1 received sent **
               pure (client_driver_application_ready st1 /\
                     st1.CS.cs_model.CS.model_config ==
                       'st0.CS.cs_model.CS.model_config /\
                     client_driver_sent_log_exact st1 sent /\
                     client_driver_received_log_accounted st1 received /\
                     client_driver_received_log_exact_prefix st1 received /\
                     client_driver_received_no_read_ahead st1 received)
           | _ ->
             client_driver_closed d st1)
{
  unfold (client_driver_live d 'st0);
  with buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel no_channel **
            client_driver_buffers d B.empty buffered_len **
            pure (client_driver_wire_logs_match 'st0 B.empty B.empty B.empty 0sz));
  unfold (client_driver_buffers d B.empty buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  assert (pure (current_buffered_len == 0sz));
  fold (client_driver_buffers d B.empty buffered_len);
  let ch_opt = IO.connect_tcp connect_host connect_host_len port;
  match ch_opt {
    None -> {
      free_disconnected_client_driver d current_buffered_len;
      DriverWorkflowStepFailed
    }
    Some ch -> {
      assert (pure (client_driver_wire_logs_match 'st0 B.empty B.empty B.empty current_buffered_len));
      fold (channel_open ch 'st0 B.empty current_buffered_len);
      unfold (client_driver_buffers d B.empty buffered_len);
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out **
                V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
      V.to_array_pts_to d.client_driver_empty_payload;
      V.to_array_pts_to d.client_driver_raw;
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_auth_leaf_der;
      V.to_array_pts_to d.client_driver_auth_payload;
      V.to_array_pts_to d.client_driver_auth_cv_input;
      V.to_array_pts_to d.client_driver_auth_signature;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = ch;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      rewrite (channel_open ch 'st0 B.empty current_buffered_len) as
        (channel_open core.driver_channel 'st0 B.empty current_buffered_len);
      fold (driver_exactly core 'st0 B.empty current_buffered_len);
      rewrite (driver_exactly core 'st0 B.empty current_buffered_len) as
        (driver_exactly td.top_driver_core 'st0 B.empty current_buffered_len);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0 B.empty current_buffered_len);
      let result =
        driver_handshake
          td
          (V.vec_to_array d.client_driver_empty_payload)
          (V.vec_to_array d.client_driver_raw)
          driver_rx_capacity
          current_buffered_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_auth_leaf_der)
          driver_auth_leaf_der_capacity
          (V.vec_to_array d.client_driver_auth_payload)
          (V.vec_to_array d.client_driver_auth_cv_input)
          driver_certificate_verify_input_capacity
          (V.vec_to_array d.client_driver_auth_signature)
          driver_signature_capacity
          driver_public_key_payload_capacity
          driver_server_finished_payload_len
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity
          local_fuel
          fuel;
      with st1 buffered_after raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
        assert (top_driver_exactly td st1 buffered_after result.driver_workflow_rx_len **
                pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
                pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_leaf_der) auth_leaf_der_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_payload) auth_payload_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_cv_input) auth_cv_input_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_signature) auth_signature_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      unfold (top_driver_exactly td st1 buffered_after result.driver_workflow_rx_len);
      rewrite (driver_exactly td.top_driver_core st1 buffered_after result.driver_workflow_rx_len) as
        (driver_exactly core st1 buffered_after result.driver_workflow_rx_len);
      unfold (driver_exactly core st1 buffered_after result.driver_workflow_rx_len);
      V.to_vec_pts_to d.client_driver_empty_payload;
      V.to_vec_pts_to d.client_driver_raw;
      V.to_vec_pts_to d.client_driver_network_out;
      V.to_vec_pts_to d.client_driver_auth_leaf_der;
      V.to_vec_pts_to d.client_driver_auth_payload;
      V.to_vec_pts_to d.client_driver_auth_cv_input;
      V.to_vec_pts_to d.client_driver_auth_signature;
      V.to_vec_pts_to d.client_driver_app_out;
      Box.(d.client_driver_buffered_len := result.driver_workflow_rx_len);
      assert (pure (SZ.v result.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
      fold (client_driver_buffers d buffered_after result.driver_workflow_rx_len);
      rewrite (C.connection_exactly core.driver_client st1) as
        (C.connection_exactly d.client_driver_client st1);
      rewrite (channel_open core.driver_channel st1 buffered_after result.driver_workflow_rx_len) as
        (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
      rewrite (O.is_auth_context td.top_driver_auth) as
        (O.is_auth_context d.client_driver_auth);
      match result.driver_workflow_status {
        DriverWorkflowOk -> {
         unfold (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
         with received sent.
           assert (IO.is_channel ch received sent **
                   pure (client_driver_wire_logs_match st1 received sent buffered_after result.driver_workflow_rx_len));
         let retained_empty = result.driver_workflow_rx_len = 0sz;
         if retained_empty {
           assert (pure (client_driver_sent_log_exact st1 sent));
           lemma_client_driver_wire_logs_match_received_accounted
             st1
             received
             sent
             buffered_after
             result.driver_workflow_rx_len;
           assert (pure (client_driver_received_log_accounted st1 received));
           assert (pure (st1.CS.cs_model.CS.model_control == CS.ControlApplicationData));
           assert (pure (CT.connection_control_not_failed st1));
           lemma_client_driver_wire_logs_match_received_exact_prefix
             st1
             received
             sent
             buffered_after
             result.driver_workflow_rx_len;
           assert (pure (client_driver_received_log_exact_prefix st1 received));
           lemma_client_driver_wire_logs_match_received_no_read_ahead
             st1
             received
             sent
             buffered_after
             result.driver_workflow_rx_len;
           assert (pure (client_driver_received_no_read_ahead st1 received));
           rewrite (C.connection_exactly d.client_driver_client st1) as
             (CR.connection_exactly d.client_driver_client st1);
           let keys_installed =
             CQ.client_application_record_keys_installed_runtime
               d.client_driver_client;
           rewrite (CR.connection_exactly d.client_driver_client st1) as
             (C.connection_exactly d.client_driver_client st1);
           if keys_installed {
             assert (pure (CS.application_record_keys_installed_for_role
               CS.ClientEndpoint
               st1.CS.cs_model));
             CSL.lemma_client_application_ready_stable_x25519_key_share_projection
               st1;
             assert (pure (client_driver_application_ready st1));
             Box.(d.client_driver_channel := Some ch);
             fold (client_driver_connected d st1 received sent);
             DriverWorkflowOk
           } else {
             fold (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
             close_failed_connect d ch result.driver_workflow_rx_len;
             DriverWorkflowStepFailed
           }
         } else {
           fold (channel_open ch st1 buffered_after result.driver_workflow_rx_len);
           close_failed_connect d ch result.driver_workflow_rx_len;
           DriverWorkflowStepFailed
         }
       }
        DriverWorkflowNeedMoreInput -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowNeedMoreInput
        }
        DriverWorkflowStepFailed -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowStepFailed
        }
        DriverWorkflowExhausted -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowExhausted
        }
        DriverWorkflowClosed -> {
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowClosed
        }
        DriverWorkflowPayloadTooLarge -> {
          (* Unreachable: the handshake workflow never produces this status,
             which is specific to [send]'s own payload-length gate. Handled
             here only so the match is total over [driver_workflow_status]. *)
          close_failed_connect d ch result.driver_workflow_rx_len;
          DriverWorkflowPayloadTooLarge
        }
      }
    }
  }
}

fn send
  (d:client_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len)
  returns status:driver_workflow_status
  ensures exists* st1 received1 sent1.
          pts_to payload 'payload_bytes **
          client_driver_connected d st1 received1 sent1 **
          pure (client_driver_send_correct
                  'st0
                  st1
                  status
                  (Ghost.reveal 'payload_bytes)
                  (Ghost.reveal 'sent0)
                  sent1 /\
                  st1.CS.cs_model.CS.model_config ==
                    'st0.CS.cs_model.CS.model_config /\
                  client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                  client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                 client_driver_sent_log_exact st1 sent1 /\
                 client_driver_received_log_accounted st1 received1)
{
  unfold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
  with ch buffered buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0) **
            client_driver_buffers d buffered buffered_len **
            pure (client_driver_wire_logs_match
                    'st0
                    (Ghost.reveal 'received0)
                    (Ghost.reveal 'sent0)
                    buffered
                    buffered_len));
  assert (pure (client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0)));
  lemma_client_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    buffered
    buffered_len;
  assert (pure (client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0)));
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  assert_norm (SM.max_application_data_fragment_len == 16384);
  let too_large = SZ.gt payload_len 16384sz;
  if too_large {
    (* TLS 1.3 caps a single application-data record's plaintext at 16384
       bytes.  Reject the oversized payload up front, authoritatively, and
       leave the connection exactly as it was so the caller may retry with a
       smaller chunk. *)
    assert (pure (SZ.v payload_len > SM.max_application_data_fragment_len));
    assert (pure (B.length (Ghost.reveal 'payload_bytes) > SM.max_application_data_fragment_len));
    assert (pure (client_driver_payload_too_large (Ghost.reveal 'payload_bytes)));
    assert (pure (client_driver_send_correct
      'st0
      'st0
      DriverWorkflowPayloadTooLarge
      (Ghost.reveal 'payload_bytes)
      (Ghost.reveal 'sent0)
      (Ghost.reveal 'sent0)));
    fold (client_driver_buffers d buffered current_buffered_len);
    fold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
    DriverWorkflowPayloadTooLarge
  } else {
    assert (pure (SZ.v payload_len <= SM.max_application_data_fragment_len));
    assert (pure (CT.local_input_wf
      'st0
      CT.LocalSendApplicationData
      (Ghost.reveal 'payload_bytes)));
  match current_channel {
    None -> {
      assert (pure False);
      fold (client_driver_buffers d buffered current_buffered_len);
      fold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
      DriverWorkflowStepFailed
    }
    Some concrete_ch -> {
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out **
                V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = concrete_ch;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      assert (pure (concrete_ch == ch));
      assert (pure (client_driver_wire_logs_match
        'st0
        (Ghost.reveal 'received0)
        (Ghost.reveal 'sent0)
        buffered
        current_buffered_len));
      fold (channel_open ch 'st0 buffered current_buffered_len);
      rewrite (channel_open ch 'st0 buffered current_buffered_len) as
        (channel_open core.driver_channel 'st0 buffered current_buffered_len);
      fold (driver_exactly core 'st0 buffered current_buffered_len);
      rewrite (driver_exactly core 'st0 buffered current_buffered_len) as
        (driver_exactly td.top_driver_core 'st0 buffered current_buffered_len);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0 buffered current_buffered_len);
      let result =
        top_driver_send_application_data
          td
          payload
          payload_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity;
      with st1 network_out_bytes app_out_bytes.
        assert (top_driver_exactly td st1 buffered current_buffered_len **
                pts_to payload 'payload_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      unfold (top_driver_exactly td st1 buffered current_buffered_len);
      rewrite (driver_exactly td.top_driver_core st1 buffered current_buffered_len) as
        (driver_exactly core st1 buffered current_buffered_len);
      unfold (driver_exactly core st1 buffered current_buffered_len);
      V.to_vec_pts_to d.client_driver_network_out;
      V.to_vec_pts_to d.client_driver_app_out;
      rewrite (C.connection_exactly core.driver_client st1) as
        (C.connection_exactly d.client_driver_client st1);
      rewrite (channel_open core.driver_channel st1 buffered current_buffered_len) as
        (channel_open ch st1 buffered current_buffered_len);
      rewrite (O.is_auth_context td.top_driver_auth) as
        (O.is_auth_context d.client_driver_auth);
      fold (client_driver_buffers d buffered current_buffered_len);
      unfold (channel_open ch st1 buffered current_buffered_len);
      with received1 sent1.
        assert (IO.is_channel ch received1 sent1 **
                pure (client_driver_wire_logs_match st1 received1 sent1 buffered current_buffered_len));
      lemma_local_event_wire_lengths
        'st0
        st1
        result.local_write_resp
        CT.LocalSendApplicationData
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        app_out_bytes;
      assert (pure (Seq.equal
        (Ghost.reveal 'sent0)
        'st0.CS.cs_wire_log.CL.raw_sent));
      assert (pure (Seq.equal sent1 st1.CS.cs_wire_log.CL.raw_sent));
      assert (pure (client_driver_sent_log_exact st1 sent1));
      lemma_client_driver_wire_logs_match_received_accounted
        st1
        received1
        sent1
        buffered
        current_buffered_len;
      assert (pure (client_driver_received_log_accounted st1 received1));
      assert (pure (Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          'st0.CS.cs_wire_log.CL.raw_sent
          (CT.response_network_out result.local_write_resp network_out_bytes))));
      Seq.lemma_eq_elim
        (Ghost.reveal 'sent0)
        'st0.CS.cs_wire_log.CL.raw_sent;
      Seq.lemma_eq_elim
        sent1
        st1.CS.cs_wire_log.CL.raw_sent;
      assert (pure (Seq.equal
        sent1
        (B.append
          (Ghost.reveal 'sent0)
          (CT.response_network_out result.local_write_resp network_out_bytes))));
      assert (pure (client_driver_local_write_correct
        'st0
        st1
        result.local_write_resp
        CT.LocalSendApplicationData
        (Ghost.reveal 'payload_bytes)
        (Ghost.reveal 'sent0)
        sent1));
      assert (pure (result.local_write_written ==
        result.local_write_resp.CT.network_out_len));
      fold (client_driver_connected d st1 received1 sent1);
      let ok = result.local_write_resp.CT.status = CT.StepOk;
      let wrote_all = result.local_write_written = result.local_write_resp.CT.network_out_len;
      assert (pure (wrote_all == true));
      if (ok && wrote_all) {
        assert (pure (ok == true));
        assert (pure (result.local_write_resp.CT.status == CT.StepOk));
        assert (pure (client_driver_send_status_correct
          DriverWorkflowOk
          result.local_write_resp));
        assert (pure (client_driver_send_correct
          'st0
          st1
          DriverWorkflowOk
          (Ghost.reveal 'payload_bytes)
          (Ghost.reveal 'sent0)
          sent1));
        DriverWorkflowOk
      } else {
        assert (pure (ok == false));
        assert (pure (not (result.local_write_resp.CT.status == CT.StepOk)));
        assert (pure (client_driver_send_status_correct
          DriverWorkflowStepFailed
          result.local_write_resp));
        assert (pure (client_driver_send_correct
          'st0
          st1
          DriverWorkflowStepFailed
          (Ghost.reveal 'payload_bytes)
          (Ghost.reveal 'sent0)
          sent1));
        DriverWorkflowStepFailed
      }
    }
  }
  }
}

noextract
let client_driver_endpoint_send_event
  (payload:B.bytes)
  : CTypes.client_local_event =
  CTypes.ClientAPI {
    CTypes.client_local_kind = CT.LocalSendApplicationData;
    CTypes.client_local_payload = payload;
  }

noextract
let client_driver_endpoint_close_event
  : CTypes.client_local_event =
  CTypes.ClientAPI {
    CTypes.client_local_kind = CT.LocalSendCloseNotify;
    CTypes.client_local_payload = B.empty;
  }

noextract
let client_endpoint_send_frame_remainder
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  : slprop =
  CQueries.client_network_persistent_resource frame.EP.client_ep_query **
  pts_to frame.EP.client_ep_query.CQueries.client_query_local_payload B.empty **
  EP.client_endpoint_auth_ready frame **
  pure (SZ.v frame.EP.client_ep_query.CQueries.client_query_local_payload_len == 0 /\
        EP.client_endpoint_config_wf cfg frame)

noextract
fn prepare_endpoint_send_api_ready
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (payload_bytes:B.bytes)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (transport_received0:Ghost.erased B.bytes)
  (transport_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires EP.client_endpoint_frame_ready
             (client_driver_canonical d)
             cfg
             frame
             (Ghost.reveal st0) **
           EP.client_endpoint_io_ready
             (client_driver_canonical d)
             ch
             frame
             (Ghost.reveal transport_received0)
             (Ghost.reveal transport_sent0)
             (Ghost.reveal st0) **
           pts_to payload payload_bytes **
           pure (B.length payload_bytes == SZ.v payload_len /\
                 Seq.equal (Ghost.reveal canonical_sent0) (Ghost.reveal transport_sent0) /\
                 CT.local_input_wf
                   (Ghost.reveal st0)
                   CT.LocalSendApplicationData
                   payload_bytes)
  returns local_frame:CP.tls_client_local_frame
  ensures EP.client_api_local_action_ready
            (client_driver_canonical d)
            ch
            frame
            (Ghost.reveal canonical_received0)
            (Ghost.reveal canonical_sent0)
            (Ghost.reveal st0)
            (client_driver_endpoint_send_event payload_bytes)
            local_frame **
          client_endpoint_send_frame_remainder cfg frame **
          pure (
            local_frame.CP.tls_client_local_payload == payload /\
            local_frame.CP.tls_client_local_payload_len == payload_len /\
            local_frame.CP.tls_client_local_app_out ==
              frame.EP.client_ep_query.CQueries.client_query_local_app_out /\
            local_frame.CP.tls_client_local_app_out_len ==
              frame.EP.client_ep_query.CQueries.client_query_local_app_out_len)
{
  let ev = client_driver_endpoint_send_event payload_bytes;
  unfold (EP.client_endpoint_frame_ready
    (client_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st0));
  unfold (CQueries.client_next_local_action_frame_ready
    (client_driver_canonical d)
    cfg
    frame.EP.client_ep_query
    (Ghost.reveal st0));
  unfold (CQueries.client_network_persistent_resource
    frame.EP.client_ep_query);
  with network_current. _;
  unfold (CQueries.client_local_persistent_resource
    frame.EP.client_ep_query);
  with local_current. _;
  let old_local_out = Ghost.hide local_current;
  let local_frame : CP.tls_client_local_frame = {
    CP.tls_client_local_payload = payload;
    CP.tls_client_local_payload_len = payload_len;
    CP.tls_client_local_app_out =
      frame.EP.client_ep_query.CQueries.client_query_local_app_out;
    CP.tls_client_local_app_out_len =
      frame.EP.client_ep_query.CQueries.client_query_local_app_out_len;
    CP.tls_client_local_old_app_out = old_local_out;
  };
  unfold (EP.client_endpoint_io_ready
    (client_driver_canonical d)
    ch
    frame
    (Ghost.reveal transport_received0)
    (Ghost.reveal transport_sent0)
    (Ghost.reveal st0));
  with raw_received raw_bytes network_out_bytes. _;
  rewrite
    (IO.is_channel ch raw_received (Ghost.reveal transport_sent0))
    as
    (IO.is_channel ch raw_received (Ghost.reveal canonical_sent0));
  rewrite
    (pts_to payload payload_bytes)
    as
    (pts_to
      local_frame.CP.tls_client_local_payload
      payload_bytes);
  rewrite
    (pts_to
      frame.EP.client_ep_query.CQueries.client_query_local_app_out
      local_current)
    as
    (pts_to
      local_frame.CP.tls_client_local_app_out
      (Ghost.reveal old_local_out));
  fold (CP.client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st0)
    (V.vec_to_array frame.EP.client_ep_network_out)
    frame.EP.client_ep_network_out_len
    network_out_bytes);
  fold (EP.client_api_local_action_ready
    (client_driver_canonical d)
    ch
    frame
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    ev
    local_frame);
  fold (CQueries.client_network_persistent_resource
    frame.EP.client_ep_query);
  fold (client_endpoint_send_frame_remainder cfg frame);
  rewrite
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame)
    as
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      (client_driver_endpoint_send_event payload_bytes)
      local_frame);
  local_frame
}

noextract
fn send_endpoint
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (payload_bytes:B.bytes)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires client_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st0)
              (Ghost.reveal canonical_received0)
              (Ghost.reveal canonical_sent0) **
           pts_to payload payload_bytes **
           pure (B.length payload_bytes == SZ.v payload_len /\
                 CT.connection_control_not_failed (Ghost.reveal st0) /\
                 CT.local_input_wf
                   (Ghost.reveal st0)
                   CT.LocalSendApplicationData
                   payload_bytes)
  returns result:CPI.process_result
  ensures exists* (canonical_received1:Ghost.erased B.bytes)
                  (canonical_sent1:Ghost.erased B.bytes)
                  (st1:Ghost.erased CS.connection_state).
           client_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st1)
             (Ghost.reveal canonical_received1)
             (Ghost.reveal canonical_sent1) **
           pts_to payload payload_bytes **
           pure (exists (old_out:B.bytes)
                        (out_contents:B.bytes)
                        (wire_outputs:list CW.wire_message)
                        (local_outputs:list EAPI.local_output).
             CPI.local_process_correct
               (EC.client_system #CTypes.client_local_event
                 (Ghost.reveal
                   (client_driver_canonical d).CP.canonical_client_initial))
               (client_driver_endpoint_send_event payload_bytes)
               old_out
               out_contents
               frame.EP.client_ep_network_out_len
               (Ghost.reveal canonical_received0)
               (Ghost.reveal canonical_sent0)
               (Ghost.reveal st0)
               result
               (Ghost.reveal canonical_received1)
               (Ghost.reveal canonical_sent1)
               (Ghost.reveal st1)
               wire_outputs
               local_outputs)
{
  let ev = client_driver_endpoint_send_event payload_bytes;
  unfold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st0)
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0));
  with ch buffered_len. _;
  expose_client_invariant_pure
    (client_driver_canonical d)
    canonical_received0
    canonical_sent0
    st0;
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite
    (EP.client_endpoint_io_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0))
    as
    (EP.client_endpoint_io_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0));
  let local_frame =
    prepare_endpoint_send_api_ready
      d
      cfg
      frame
      concrete_ch
      payload
      payload_len
      payload_bytes
      canonical_received0
      canonical_sent0
      canonical_received0
      canonical_sent0
      st0;
  rewrite
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      (client_driver_endpoint_send_event payload_bytes)
      local_frame)
    as
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame);
  let result =
    EP.client_run_api_local_action
      (client_driver_canonical d)
      frame
      concrete_ch
      ev
      local_frame
      canonical_received0
      canonical_sent0
      st0;
  with received1 sent1 st1 old_out out_contents wire_outputs local_outputs.
    assert (
      CP.client_invariant
        (client_driver_canonical d)
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      EP.client_endpoint_io_ready
        (client_driver_canonical d)
        concrete_ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      CP.client_local_frame_post
        ev
        local_frame
        result
        (Ghost.reveal old_out)
        (Ghost.reveal out_contents)
        (Ghost.reveal st0)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputs)
        (Ghost.reveal local_outputs));
  assert (pure (ev == client_driver_endpoint_send_event payload_bytes));
  assert (pure (CPI.local_process_correct
    (EC.client_system #CTypes.client_local_event
      (Ghost.reveal
        (client_driver_canonical d).CP.canonical_client_initial))
    (client_driver_endpoint_send_event payload_bytes)
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    frame.EP.client_ep_network_out_len
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)));
  expose_client_invariant_pure
    (client_driver_canonical d)
    received1
    sent1
    st1;
  unfold (CP.client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with app_out. _;
  rewrite
    (pts_to
      local_frame.CP.tls_client_local_payload
      payload_bytes)
    as
    (pts_to payload payload_bytes);
  rewrite
    (pts_to
      local_frame.CP.tls_client_local_app_out
      app_out)
    as
    (pts_to
      frame.EP.client_ep_query.CQueries.client_query_local_app_out
      app_out);
  unfold (client_endpoint_send_frame_remainder cfg frame);
  fold (CQueries.client_local_persistent_resource
    frame.EP.client_ep_query);
  fold (CQueries.client_network_persistent_resource
    frame.EP.client_ep_query);
  fold (CQueries.client_next_local_action_frame_ready
    (client_driver_canonical d)
    cfg
    frame.EP.client_ep_query
    (Ghost.reveal st1));
  fold (EP.client_endpoint_frame_ready
    (client_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st1));
  unfold (EP.client_endpoint_io_ready
    (client_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  with raw_received1 raw_bytes1 network_out_bytes1. _;
  fold (EP.client_endpoint_io_ready
    (client_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  rewrite
    (Box.pts_to d.client_driver_channel (Some ch))
    as
    (Box.pts_to d.client_driver_channel (Some concrete_ch));
  with concrete_ch buffered_len.
  fold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st1)
    (Ghost.reveal received1)
    (Ghost.reveal sent1));
  assert (pure (exists (old_out0:B.bytes)
                       (out_contents0:B.bytes)
                       (wire_outputs0:list CW.wire_message)
                       (local_outputs0:list EAPI.local_output).
    CPI.local_process_correct
      (EC.client_system #CTypes.client_local_event
        (Ghost.reveal
          (client_driver_canonical d).CP.canonical_client_initial))
      (client_driver_endpoint_send_event payload_bytes)
      old_out0
      out_contents0
      frame.EP.client_ep_network_out_len
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs0
      local_outputs0));
  result
}

noextract
fn receive_endpoint
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (fuel:SZ.t)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires client_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st0)
              (Ghost.reveal canonical_received0)
              (Ghost.reveal canonical_sent0)
  returns result:EP.client_endpoint_run_result
  ensures exists* (canonical_received1:Ghost.erased B.bytes)
                 (canonical_sent1:Ghost.erased B.bytes)
                 (st1:Ghost.erased CS.connection_state).
           client_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st1)
             (Ghost.reveal canonical_received1)
             (Ghost.reveal canonical_sent1)
{
  unfold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st0)
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0));
  with ch buffered_len. _;
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite
    (EP.client_endpoint_io_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0))
    as
    (EP.client_endpoint_io_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0));
  let result =
    EP.client_endpoint_run_workflow
      (client_driver_canonical d)
      cfg
      frame
      concrete_ch
      d.client_driver_buffered_len
      true
      false
      false
      fuel
      canonical_received0
      canonical_sent0
      st0;
  with received1 sent1 st1 buffered_len1. _;
  rewrite
    (Box.pts_to d.client_driver_channel (Some ch))
    as
    (Box.pts_to d.client_driver_channel (Some concrete_ch));
  with concrete_ch buffered_len1.
  fold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st1)
    (Ghost.reveal received1)
    (Ghost.reveal sent1));
  result
}

noextract
fn prepare_endpoint_close_api_ready
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (transport_received0:Ghost.erased B.bytes)
  (transport_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires EP.client_endpoint_frame_ready
             (client_driver_canonical d)
             cfg
             frame
             (Ghost.reveal st0) **
           EP.client_endpoint_io_ready
             (client_driver_canonical d)
             ch
             frame
             (Ghost.reveal transport_received0)
             (Ghost.reveal transport_sent0)
             (Ghost.reveal st0) **
           pts_to payload B.empty **
           pure (SZ.v payload_len == 0 /\
                 Seq.equal (Ghost.reveal canonical_sent0) (Ghost.reveal transport_sent0) /\
                 CT.local_input_wf
                   (Ghost.reveal st0)
                   CT.LocalSendCloseNotify
                   B.empty)
  returns local_frame:CP.tls_client_local_frame
  ensures EP.client_api_local_action_ready
            (client_driver_canonical d)
            ch
            frame
            (Ghost.reveal canonical_received0)
            (Ghost.reveal canonical_sent0)
            (Ghost.reveal st0)
            client_driver_endpoint_close_event
            local_frame **
          client_endpoint_send_frame_remainder cfg frame **
          pure (
            local_frame.CP.tls_client_local_payload == payload /\
            local_frame.CP.tls_client_local_payload_len == payload_len /\
            local_frame.CP.tls_client_local_app_out ==
              frame.EP.client_ep_query.CQueries.client_query_local_app_out /\
            local_frame.CP.tls_client_local_app_out_len ==
              frame.EP.client_ep_query.CQueries.client_query_local_app_out_len)
{
  let ev = client_driver_endpoint_close_event;
  assert (pure (B.length B.empty == SZ.v payload_len));
  unfold (EP.client_endpoint_frame_ready
    (client_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st0));
  unfold (CQueries.client_next_local_action_frame_ready
    (client_driver_canonical d)
    cfg
    frame.EP.client_ep_query
    (Ghost.reveal st0));
  unfold (CQueries.client_network_persistent_resource
    frame.EP.client_ep_query);
  with network_current. _;
  unfold (CQueries.client_local_persistent_resource
    frame.EP.client_ep_query);
  with local_current. _;
  let old_local_out = Ghost.hide local_current;
  let local_frame : CP.tls_client_local_frame = {
    CP.tls_client_local_payload = payload;
    CP.tls_client_local_payload_len = payload_len;
    CP.tls_client_local_app_out =
      frame.EP.client_ep_query.CQueries.client_query_local_app_out;
    CP.tls_client_local_app_out_len =
      frame.EP.client_ep_query.CQueries.client_query_local_app_out_len;
    CP.tls_client_local_old_app_out = old_local_out;
  };
  unfold (EP.client_endpoint_io_ready
    (client_driver_canonical d)
    ch
    frame
    (Ghost.reveal transport_received0)
    (Ghost.reveal transport_sent0)
    (Ghost.reveal st0));
  with raw_received raw_bytes network_out_bytes. _;
  rewrite
    (IO.is_channel ch raw_received (Ghost.reveal transport_sent0))
    as
    (IO.is_channel ch raw_received (Ghost.reveal canonical_sent0));
  rewrite
    (pts_to payload B.empty)
    as
    (pts_to
      local_frame.CP.tls_client_local_payload
      B.empty);
  rewrite
    (pts_to
      frame.EP.client_ep_query.CQueries.client_query_local_app_out
      local_current)
    as
    (pts_to
      local_frame.CP.tls_client_local_app_out
      (Ghost.reveal old_local_out));
  fold (CP.client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st0)
    (V.vec_to_array frame.EP.client_ep_network_out)
    frame.EP.client_ep_network_out_len
    network_out_bytes);
  fold (EP.client_api_local_action_ready
    (client_driver_canonical d)
    ch
    frame
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    ev
    local_frame);
  fold (CQueries.client_network_persistent_resource
    frame.EP.client_ep_query);
  fold (client_endpoint_send_frame_remainder cfg frame);
  rewrite
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame)
    as
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      client_driver_endpoint_close_event
      local_frame);
  local_frame
}

noextract
fn close_endpoint
  (d:client_driver)
  (cfg:CQueries.client_next_local_action_config)
  (frame:EP.client_endpoint_frame)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires client_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st0)
              (Ghost.reveal canonical_received0)
              (Ghost.reveal canonical_sent0) **
           pts_to payload B.empty **
           pure (SZ.v payload_len == 0 /\
                 CT.connection_control_not_failed (Ghost.reveal st0) /\
                 CT.local_input_wf
                   (Ghost.reveal st0)
                   CT.LocalSendCloseNotify
                   B.empty)
  returns result:CPI.process_result
  ensures exists* (canonical_received1:Ghost.erased B.bytes)
                 (canonical_sent1:Ghost.erased B.bytes)
                 (st1:Ghost.erased CS.connection_state).
           client_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st1)
             (Ghost.reveal canonical_received1)
             (Ghost.reveal canonical_sent1) **
           pts_to payload B.empty **
           pure (exists (old_out:B.bytes)
                        (out_contents:B.bytes)
                        (wire_outputs:list CW.wire_message)
                        (local_outputs:list EAPI.local_output).
             CPI.local_process_correct
               (EC.client_system #CTypes.client_local_event
                 (Ghost.reveal
                  (client_driver_canonical d).CP.canonical_client_initial))
               client_driver_endpoint_close_event
               old_out
               out_contents
               frame.EP.client_ep_network_out_len
               (Ghost.reveal canonical_received0)
               (Ghost.reveal canonical_sent0)
               (Ghost.reveal st0)
               result
               (Ghost.reveal canonical_received1)
               (Ghost.reveal canonical_sent1)
               (Ghost.reveal st1)
               wire_outputs
               local_outputs)
{
  let ev = client_driver_endpoint_close_event;
  unfold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st0)
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0));
  with ch buffered_len. _;
  expose_client_invariant_pure
    (client_driver_canonical d)
    canonical_received0
    canonical_sent0
    st0;
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite
    (EP.client_endpoint_io_ready
      (client_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0))
    as
    (EP.client_endpoint_io_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0));
  let local_frame =
    prepare_endpoint_close_api_ready
      d
      cfg
      frame
      concrete_ch
      payload
      payload_len
      canonical_received0
      canonical_sent0
      canonical_received0
      canonical_sent0
      st0;
  rewrite
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      client_driver_endpoint_close_event
      local_frame)
    as
    (EP.client_api_local_action_ready
      (client_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame);
  let result =
    EP.client_run_api_local_action
      (client_driver_canonical d)
      frame
      concrete_ch
      ev
      local_frame
      canonical_received0
      canonical_sent0
      st0;
  with received1 sent1 st1 old_out out_contents wire_outputs local_outputs.
    assert (
      CP.client_invariant
        (client_driver_canonical d)
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      EP.client_endpoint_io_ready
        (client_driver_canonical d)
        concrete_ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      CP.client_local_frame_post
        ev
        local_frame
        result
        (Ghost.reveal old_out)
        (Ghost.reveal out_contents)
        (Ghost.reveal st0)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputs)
        (Ghost.reveal local_outputs));
  assert (pure (ev == client_driver_endpoint_close_event));
  assert (pure (CPI.local_process_correct
    (EC.client_system #CTypes.client_local_event
      (Ghost.reveal
        (client_driver_canonical d).CP.canonical_client_initial))
    client_driver_endpoint_close_event
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    frame.EP.client_ep_network_out_len
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)));
  expose_client_invariant_pure
    (client_driver_canonical d)
    received1
    sent1
    st1;
  unfold (CP.client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with app_out. _;
  rewrite
    (pts_to
      local_frame.CP.tls_client_local_payload
      B.empty)
    as
    (pts_to payload B.empty);
  rewrite
    (pts_to
      local_frame.CP.tls_client_local_app_out
      app_out)
    as
    (pts_to
      frame.EP.client_ep_query.CQueries.client_query_local_app_out
      app_out);
  unfold (client_endpoint_send_frame_remainder cfg frame);
  fold (CQueries.client_local_persistent_resource
    frame.EP.client_ep_query);
  fold (CQueries.client_network_persistent_resource
    frame.EP.client_ep_query);
  fold (CQueries.client_next_local_action_frame_ready
    (client_driver_canonical d)
    cfg
    frame.EP.client_ep_query
    (Ghost.reveal st1));
  fold (EP.client_endpoint_frame_ready
    (client_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st1));
  unfold (EP.client_endpoint_io_ready
    (client_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  with raw_received1 raw_bytes1 network_out_bytes1. _;
  fold (EP.client_endpoint_io_ready
    (client_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  rewrite
    (Box.pts_to d.client_driver_channel (Some ch))
    as
    (Box.pts_to d.client_driver_channel (Some concrete_ch));
  with concrete_ch buffered_len.
  fold (client_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st1)
    (Ghost.reveal received1)
    (Ghost.reveal sent1));
  assert (pure (exists (old_out0:B.bytes)
                       (out_contents0:B.bytes)
                       (wire_outputs0:list CW.wire_message)
                       (local_outputs0:list EAPI.local_output).
    CPI.local_process_correct
      (EC.client_system #CTypes.client_local_event
        (Ghost.reveal
          (client_driver_canonical d).CP.canonical_client_initial))
      client_driver_endpoint_close_event
      old_out0
      out_contents0
      frame.EP.client_ep_network_out_len
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs0
      local_outputs0));
  result
}

fn receive
  (d:client_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0 **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns result:client_receive_result
  ensures exists* st1 received1 sent1 out_bytes.
          client_driver_connected d st1 received1 sent1 **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.client_receive_len <= SZ.v out_len /\
          st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config /\
          client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
          client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                client_driver_sent_log_exact st1 sent1 /\
                client_driver_received_log_accounted st1 received1 /\
                (exists obs app_out.
                  client_driver_receive_correct
                   'st0
                   st1
                    result
                    obs
                    app_out
                    out_bytes))
{
  unfold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
  with ch buffered buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0) **
            client_driver_buffers d buffered buffered_len **
            pure (client_driver_wire_logs_match
                    'st0
                    (Ghost.reveal 'received0)
                    (Ghost.reveal 'sent0)
                    buffered
                    buffered_len));
  assert (pure (client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0)));
  lemma_client_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    buffered
    buffered_len;
  assert (pure (client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0)));
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  match current_channel {
    None -> {
      assert (pure False);
      fold (client_driver_buffers d buffered current_buffered_len);
      fold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
      {
        client_receive_status = DriverWorkflowStepFailed;
        client_receive_len = 0sz;
      }
    }
    Some concrete_ch -> {
      with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
        assert (Box.pts_to d.client_driver_buffered_len buffered_len **
                V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
                V.pts_to d.client_driver_raw #1.0R raw **
                V.pts_to d.client_driver_network_out #1.0R network_out **
                V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
                V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
                V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
                V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
                V.pts_to d.client_driver_app_out #1.0R app_out **
                V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
      V.to_array_pts_to d.client_driver_empty_payload;
      V.to_array_pts_to d.client_driver_raw;
      V.to_array_pts_to d.client_driver_network_out;
      V.to_array_pts_to d.client_driver_auth_leaf_der;
      V.to_array_pts_to d.client_driver_auth_payload;
      V.to_array_pts_to d.client_driver_auth_cv_input;
      V.to_array_pts_to d.client_driver_auth_signature;
      V.to_array_pts_to d.client_driver_app_out;
      let core = {
        driver_client = d.client_driver_client;
        driver_channel = concrete_ch;
      };
      let td = {
        top_driver_core = core;
        top_driver_auth = d.client_driver_auth;
      };
      rewrite (C.connection_exactly d.client_driver_client 'st0) as
        (C.connection_exactly core.driver_client 'st0);
      assert (pure (concrete_ch == ch));
      assert (pure (client_driver_wire_logs_match
        'st0
        (Ghost.reveal 'received0)
        (Ghost.reveal 'sent0)
        buffered
        current_buffered_len));
      fold (channel_open ch 'st0 buffered current_buffered_len);
      rewrite (channel_open ch 'st0 buffered current_buffered_len) as
        (channel_open core.driver_channel 'st0 buffered current_buffered_len);
      fold (driver_exactly core 'st0 buffered current_buffered_len);
      rewrite (driver_exactly core 'st0 buffered current_buffered_len) as
        (driver_exactly td.top_driver_core 'st0 buffered current_buffered_len);
      rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
      fold (top_driver_exactly td 'st0 buffered current_buffered_len);
      let workflow =
        driver_receive_application_data
          td
          (V.vec_to_array d.client_driver_empty_payload)
          (V.vec_to_array d.client_driver_raw)
          driver_rx_capacity
          current_buffered_len
          (V.vec_to_array d.client_driver_network_out)
          driver_network_out_capacity
          (V.vec_to_array d.client_driver_auth_leaf_der)
          driver_auth_leaf_der_capacity
          (V.vec_to_array d.client_driver_auth_payload)
          (V.vec_to_array d.client_driver_auth_cv_input)
          driver_certificate_verify_input_capacity
          (V.vec_to_array d.client_driver_auth_signature)
          driver_signature_capacity
          driver_public_key_payload_capacity
          driver_server_finished_payload_len
          (V.vec_to_array d.client_driver_app_out)
          driver_app_out_capacity
          local_fuel
          fuel;
      with st1 workflow_buffered raw_bytes network_out_bytes auth_leaf_der_bytes auth_payload_bytes auth_cv_input_bytes auth_signature_bytes app_out_bytes.
        assert (top_driver_exactly td st1 workflow_buffered workflow.driver_workflow_rx_len **
                pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
                pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
                pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_leaf_der) auth_leaf_der_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_payload) auth_payload_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_cv_input) auth_cv_input_bytes **
                pts_to (V.vec_to_array d.client_driver_auth_signature) auth_signature_bytes **
                pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      let response =
        workflow.driver_workflow_network.buffered_network_io_buffered.buffered_network_read.network_read_buffer_resp.CT.response;
      let copy_len = response.CT.app_out_len;
      let app_fits = SZ.lte copy_len out_len;
      let app_src_fits = SZ.lte copy_len driver_app_out_capacity;
      let workflow_ok = workflow.driver_workflow_status = DriverWorkflowOk;
      if (workflow_ok && app_fits && app_src_fits) {
        A.pts_to_len (V.vec_to_array d.client_driver_app_out);
        A.pts_to_len out;
        assert (pure (SZ.v copy_len <= SZ.v out_len));
        assert (pure (SZ.v copy_len <= B.length app_out_bytes));
        assert (pure (A.length (V.vec_to_array d.client_driver_app_out) == B.length app_out_bytes));
        assert (pure (A.length out == SZ.v out_len));
        assert (pure (SZ.v copy_len <= A.length (V.vec_to_array d.client_driver_app_out)));
        assert (pure (SZ.v copy_len <= A.length out));
        let _ = A.memcpy_l copy_len (V.vec_to_array d.client_driver_app_out) out;
        with out_bytes.
          assert (pts_to out out_bytes);
        A.pts_to_len out;
        assert (pure (B.length out_bytes == SZ.v out_len));
        assert (pure (SZ.v copy_len <= B.length app_out_bytes));
        assert (pure (Seq.equal
          (CT.response_app_out response app_out_bytes)
          (Seq.slice app_out_bytes 0 (SZ.v copy_len))));
        Seq.lemma_len_slice out_bytes 0 (SZ.v copy_len);
        Seq.lemma_len_slice app_out_bytes 0 (SZ.v copy_len);
        assert (pure (Seq.equal
          (Seq.slice out_bytes 0 (SZ.v copy_len))
          (Seq.slice app_out_bytes 0 (SZ.v copy_len))));
        let receive_result = {
          client_receive_status = DriverWorkflowOk;
          client_receive_len = copy_len;
        };
        assert (pure (client_driver_receive_copyout_correct
          receive_result
          response
          app_out_bytes
          out_bytes));
        assert (pure (client_driver_receive_status_correct
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (client_driver_receive_correct
          'st0
          st1
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (exists obs app_out.
          client_driver_receive_correct
            'st0
            st1
            receive_result
            obs
            app_out
            out_bytes));
        unfold (top_driver_exactly td st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (driver_exactly td.top_driver_core st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
        unfold (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
        V.to_vec_pts_to d.client_driver_empty_payload;
        V.to_vec_pts_to d.client_driver_raw;
        V.to_vec_pts_to d.client_driver_network_out;
        V.to_vec_pts_to d.client_driver_auth_leaf_der;
        V.to_vec_pts_to d.client_driver_auth_payload;
        V.to_vec_pts_to d.client_driver_auth_cv_input;
        V.to_vec_pts_to d.client_driver_auth_signature;
        V.to_vec_pts_to d.client_driver_app_out;
        Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
        assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
        rewrite (C.connection_exactly core.driver_client st1) as
          (C.connection_exactly d.client_driver_client st1);
        rewrite (channel_open core.driver_channel st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (O.is_auth_context td.top_driver_auth) as
          (O.is_auth_context d.client_driver_auth);
        fold (client_driver_buffers d workflow_buffered workflow.driver_workflow_rx_len);
        unfold (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        with received1 sent1.
          assert (IO.is_channel ch received1 sent1 **
                  pure (client_driver_wire_logs_match st1 received1 sent1 workflow_buffered workflow.driver_workflow_rx_len));
        assert (pure (client_driver_sent_log_exact st1 sent1));
        lemma_client_driver_wire_logs_match_received_accounted
          st1
          received1
          sent1
          workflow_buffered
          workflow.driver_workflow_rx_len;
        assert (pure (client_driver_received_log_accounted st1 received1));
        fold (client_driver_connected d st1 received1 sent1);
        receive_result
      } else {
        with out_bytes.
          assert (pts_to out out_bytes);
        assert (pure (B.length out_bytes == SZ.v out_len));
        let receive_result = {
          client_receive_status =
            if workflow_ok then DriverWorkflowStepFailed else workflow.driver_workflow_status;
          client_receive_len = 0sz;
        };
        assert (pure (client_driver_receive_status_correct
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (client_driver_receive_correct
          'st0
          st1
          receive_result
          (client_driver_workflow_observation workflow)
          app_out_bytes
          out_bytes));
        assert (pure (exists obs app_out.
          client_driver_receive_correct
            'st0
            st1
            receive_result
            obs
            app_out
            out_bytes));
        unfold (top_driver_exactly td st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (driver_exactly td.top_driver_core st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
        unfold (driver_exactly core st1 workflow_buffered workflow.driver_workflow_rx_len);
        V.to_vec_pts_to d.client_driver_empty_payload;
        V.to_vec_pts_to d.client_driver_raw;
        V.to_vec_pts_to d.client_driver_network_out;
        V.to_vec_pts_to d.client_driver_auth_leaf_der;
        V.to_vec_pts_to d.client_driver_auth_payload;
        V.to_vec_pts_to d.client_driver_auth_cv_input;
        V.to_vec_pts_to d.client_driver_auth_signature;
        V.to_vec_pts_to d.client_driver_app_out;
        Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
        assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
        rewrite (C.connection_exactly core.driver_client st1) as
          (C.connection_exactly d.client_driver_client st1);
        rewrite (channel_open core.driver_channel st1 workflow_buffered workflow.driver_workflow_rx_len) as
          (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        rewrite (O.is_auth_context td.top_driver_auth) as
          (O.is_auth_context d.client_driver_auth);
        fold (client_driver_buffers d workflow_buffered workflow.driver_workflow_rx_len);
        unfold (channel_open ch st1 workflow_buffered workflow.driver_workflow_rx_len);
        with received1 sent1.
          assert (IO.is_channel ch received1 sent1 **
                  pure (client_driver_wire_logs_match st1 received1 sent1 workflow_buffered workflow.driver_workflow_rx_len));
        assert (pure (client_driver_sent_log_exact st1 sent1));
        lemma_client_driver_wire_logs_match_received_accounted
          st1
          received1
          sent1
          workflow_buffered
          workflow.driver_workflow_rx_len;
        assert (pure (client_driver_received_log_accounted st1 received1));
        fold (client_driver_connected d st1 received1 sent1);
        receive_result
      }
    }
  }
}

fn close
  (d:client_driver)
  (wait_for_peer:bool)
  (fuel:SZ.t)
  requires client_driver_connected d 'st0 'received0 'sent0
  returns status:driver_workflow_status
  ensures exists* st1.
          client_driver_closed d st1 **
          pure (st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0) /\
                client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0) /\
                (exists st_close_notify.
            client_driver_close_correct
              'st0
              st_close_notify
              status
              wait_for_peer))
{
  unfold (client_driver_connected d 'st0 (Ghost.reveal 'received0) (Ghost.reveal 'sent0));
  with ch buffered buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0) **
            client_driver_buffers d buffered buffered_len **
            pure (client_driver_wire_logs_match
                    'st0
                    (Ghost.reveal 'received0)
                    (Ghost.reveal 'sent0)
                    buffered
                    buffered_len));
  assert (pure (client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0)));
  lemma_client_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    buffered
    buffered_len;
  assert (pure (client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0)));
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (concrete_ch == ch));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  with empty_payload raw network_out auth_leaf_der auth_payload auth_cv_input auth_signature app_out local_app_out.
    assert (Box.pts_to d.client_driver_buffered_len buffered_len **
            V.pts_to d.client_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.client_driver_raw #1.0R raw **
            V.pts_to d.client_driver_network_out #1.0R network_out **
            V.pts_to d.client_driver_auth_leaf_der #1.0R auth_leaf_der **
            V.pts_to d.client_driver_auth_payload #1.0R auth_payload **
            V.pts_to d.client_driver_auth_cv_input #1.0R auth_cv_input **
            V.pts_to d.client_driver_auth_signature #1.0R auth_signature **
            V.pts_to d.client_driver_app_out #1.0R app_out **
            V.pts_to d.client_driver_local_app_out #1.0R local_app_out);
  V.to_array_pts_to d.client_driver_empty_payload;
  V.to_array_pts_to d.client_driver_raw;
  V.to_array_pts_to d.client_driver_network_out;
  V.to_array_pts_to d.client_driver_app_out;
  let core = {
    driver_client = d.client_driver_client;
    driver_channel = concrete_ch;
  };
  let td = {
    top_driver_core = core;
    top_driver_auth = d.client_driver_auth;
  };
  rewrite (C.connection_exactly d.client_driver_client 'st0) as
    (C.connection_exactly core.driver_client 'st0);
  assert (pure (client_driver_wire_logs_match
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0)
    buffered
    current_buffered_len));
  fold (channel_open ch 'st0 buffered current_buffered_len);
  rewrite (channel_open ch 'st0 buffered current_buffered_len) as
    (channel_open core.driver_channel 'st0 buffered current_buffered_len);
  fold (driver_exactly core 'st0 buffered current_buffered_len);
  rewrite (driver_exactly core 'st0 buffered current_buffered_len) as
    (driver_exactly td.top_driver_core 'st0 buffered current_buffered_len);
  rewrite (O.is_auth_context d.client_driver_auth) as (O.is_auth_context td.top_driver_auth);
  fold (top_driver_exactly td 'st0 buffered current_buffered_len);
  let workflow =
    driver_close_workflow
      td
      wait_for_peer
      (V.vec_to_array d.client_driver_empty_payload)
      (V.vec_to_array d.client_driver_raw)
      driver_rx_capacity
      current_buffered_len
      (V.vec_to_array d.client_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.client_driver_app_out)
      driver_app_out_capacity
      fuel;
  with st1 raw_bytes network_out_bytes app_out_bytes.
    assert (C.connection_exactly td.top_driver_core.driver_client st1 **
            pts_to (V.vec_to_array d.client_driver_empty_payload) empty_payload **
            pts_to (V.vec_to_array d.client_driver_raw) raw_bytes **
            pts_to (V.vec_to_array d.client_driver_network_out) network_out_bytes **
            pts_to (V.vec_to_array d.client_driver_app_out) app_out_bytes);
  assert (pure (st1.CS.cs_model.CS.model_config ==
    'st0.CS.cs_model.CS.model_config));
  rewrite (C.connection_exactly td.top_driver_core.driver_client st1) as
    (C.connection_exactly d.client_driver_client st1);
  V.to_vec_pts_to d.client_driver_empty_payload;
  V.to_vec_pts_to d.client_driver_raw;
  V.to_vec_pts_to d.client_driver_network_out;
  V.to_vec_pts_to d.client_driver_app_out;
  Box.(d.client_driver_channel := no_channel);
  Box.free d.client_driver_channel;
  Box.(d.client_driver_buffered_len := workflow.driver_workflow_rx_len);
  assert (pure (SZ.v workflow.driver_workflow_rx_len <= SZ.v driver_rx_capacity));
  let close_buffered =
    Ghost.hide (Seq.slice raw_bytes 0 (SZ.v workflow.driver_workflow_rx_len));
  Seq.lemma_len_slice raw_bytes 0 (SZ.v workflow.driver_workflow_rx_len);
  fold (client_driver_buffers d (Ghost.reveal close_buffered) workflow.driver_workflow_rx_len);
  free_client_driver_buffers d workflow.driver_workflow_rx_len;
  fold (client_driver_closed d st1);
  assert (pure (client_driver_sent_log_exact 'st0 (Ghost.reveal 'sent0)));
  assert (pure (client_driver_received_log_accounted 'st0 (Ghost.reveal 'received0)));
  assert (pure (exists st_close_notify.
    client_driver_close_correct
      'st0
      st_close_notify
      workflow.driver_workflow_status
      wait_for_peer));
  workflow.driver_workflow_status
}

(**
  Safely disposes a connected transport after a workflow failure.  This is
  deliberately independent of the TLS control state: callers use it when a
  receive or send workflow has reported a non-retryable status and therefore
  cannot establish the application-ready precondition of [close].
**)
fn abort
  (d:client_driver)
  requires client_driver_connected d 'st0 'received0 'sent0
  ensures client_driver_closed d 'st0
{
  unfold (client_driver_connected
    d
    'st0
    (Ghost.reveal 'received0)
    (Ghost.reveal 'sent0));
  with ch buffered buffered_len.
    assert (C.connection_exactly d.client_driver_client 'st0 **
            client_driver_canonical_seed d **
            O.is_auth_context d.client_driver_auth **
            Box.pts_to d.client_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0) **
            client_driver_buffers d buffered buffered_len **
            pure (client_driver_wire_logs_match
              'st0
              (Ghost.reveal 'received0)
              (Ghost.reveal 'sent0)
              buffered
              buffered_len));
  let current_channel = Box.(!d.client_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (concrete_ch == ch));
  rewrite
    (IO.is_channel ch (Ghost.reveal 'received0) (Ghost.reveal 'sent0))
    as
    (IO.is_channel
      concrete_ch
      (Ghost.reveal 'received0)
      (Ghost.reveal 'sent0));
  unfold (client_driver_buffers d buffered buffered_len);
  let current_buffered_len = Box.(!d.client_driver_buffered_len);
  assert (pure (current_buffered_len == buffered_len));
  fold (client_driver_buffers d buffered current_buffered_len);
  Box.(d.client_driver_channel := no_channel);
  fold (channel_open concrete_ch 'st0 buffered current_buffered_len);
  close_failed_connect d concrete_ch current_buffered_len;
}
