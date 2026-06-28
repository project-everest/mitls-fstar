module TLS13.Impl.Client.Endpoint

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CP = TLS13.Impl.Client.CanonicalProtocol
module CQ = Common.ConnectionStateQuery
module CPI = Common.ProtocolImplementation
module CQueries = TLS13.Impl.Client.CanonicalQueries
module CS = TLS13.Spec.ConnectionState
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module CT = TLS13.Impl.Client.Types
module PE = Common.ProtocolEndpoint
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Common.TCP
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

noeq
type client_endpoint_frame = {
  client_ep_query: CQueries.client_next_local_action_frame;
  client_ep_raw_len: SZ.t;
  client_ep_raw: V.vec U8.t;
  client_ep_network_out_len: SZ.t;
  client_ep_network_out: V.vec U8.t;
}

let client_endpoint_config_wf
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  : prop =
  frame.client_ep_network_out_len == cfg.CQueries.client_query_network_out_len

let client_endpoint_frame_ready
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  : slprop =
  CQueries.client_next_local_action_frame_ready
    cc
    cfg
    frame.client_ep_query
    st **
  pure (client_endpoint_config_wf cfg frame)

let client_endpoint_io_ready
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  : slprop =
  exists* raw_received raw_bytes network_out_bytes.
    TCP.is_channel ch raw_received sent **
    V.pts_to frame.client_ep_raw #1.0R raw_bytes **
    V.pts_to frame.client_ep_network_out #1.0R network_out_bytes **
    pure (
      B.length raw_bytes == SZ.v frame.client_ep_raw_len /\
      B.length network_out_bytes == SZ.v frame.client_ep_network_out_len)

let client_endpoint_action_frame
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (action:PE.endpoint_action
    CP.tls_client_network_bridge_frame
    CTypes.client_local_event
    CP.tls_client_local_frame)
  : slprop =
  (match action with
  | PE.EndpointNeedInput network_frame ->
    CQueries.client_next_local_action_frame_post
      cc
      cfg
      frame.client_ep_query
      st
      (CQ.NextNeedInput network_frame)
  | PE.EndpointLocal ev local_frame ->
    CQueries.client_next_local_action_frame_post
      cc
      cfg
      frame.client_ep_query
      st
      (CQ.NextLocal ev local_frame)
  | PE.EndpointDone
  | PE.EndpointFailed ->
    CQueries.client_next_local_action_frame_ready cc cfg frame.client_ep_query st) **
  pure (client_endpoint_config_wf cfg frame)

let client_endpoint_network_continuation
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (network_frame:CP.tls_client_network_bridge_frame)
  : slprop =
  CQueries.client_next_local_action_network_continuation
    cc
    cfg
    frame.client_ep_query
    st
    network_frame **
  pure (client_endpoint_config_wf cfg frame)

let client_endpoint_local_continuation
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:CS.connection_state)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  : slprop =
  CQueries.client_next_local_action_local_continuation
    cc
    cfg
    frame.client_ep_query
    st
    ev
    local_frame **
  pure (client_endpoint_config_wf cfg frame)

fn client_endpoint_next_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  CP.client_invariant cc (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  client_endpoint_frame_ready cc cfg frame (Ghost.reveal st)
returns action:PE.endpoint_action
  CP.tls_client_network_bridge_frame
  CTypes.client_local_event
  CP.tls_client_local_frame
ensures
  CP.client_invariant cc (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) **
  client_endpoint_action_frame cc cfg frame (Ghost.reveal st) action
{
  unfold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st));
  let cq_action =
    CQueries.run_client_next_local_action
      cc
      cfg
      frame.client_ep_query
      received
      sent
      st;
  match cq_action {
    CQ.NextNeedInput network_frame -> {
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        (PE.EndpointNeedInput network_frame));
      PE.EndpointNeedInput network_frame
    }
    CQ.NextLocal ev local_frame -> {
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        (PE.EndpointLocal ev local_frame));
      PE.EndpointLocal ev local_frame
    }
    CQ.NextExternal ext -> {
      CQueries.cancel_client_next_action cc cfg frame.client_ep_query st (CQ.NextExternal ext);
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointFailed);
      PE.EndpointFailed
    }
    CQ.NextDone -> {
      CQueries.cancel_client_next_action cc cfg frame.client_ep_query st CQ.NextDone;
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointDone);
      PE.EndpointDone
    }
    CQ.NextFailed -> {
      CQueries.cancel_client_next_action cc cfg frame.client_ep_query st CQ.NextFailed;
      fold (client_endpoint_action_frame
        cc
        cfg
        frame
        (Ghost.reveal st)
        PE.EndpointFailed);
      PE.EndpointFailed
    }
  }
}

fn client_endpoint_cancel_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (st:Ghost.erased CS.connection_state)
  (action:PE.endpoint_action
    CP.tls_client_network_bridge_frame
    CTypes.client_local_event
    CP.tls_client_local_frame)
requires client_endpoint_action_frame cc cfg frame (Ghost.reveal st) action
ensures client_endpoint_frame_ready cc cfg frame (Ghost.reveal st)
{
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) action);
  match action {
    PE.EndpointNeedInput network_frame -> {
      CQueries.cancel_client_next_action
        cc
        cfg
        frame.client_ep_query
        st
        (CQ.NextNeedInput network_frame);
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
    PE.EndpointLocal ev local_frame -> {
      CQueries.cancel_client_next_action
        cc
        cfg
        frame.client_ep_query
        st
        (CQ.NextLocal ev local_frame);
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
    PE.EndpointDone -> {
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
    PE.EndpointFailed -> {
      fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st))
    }
  }
}

noeq
type client_network_io = {
  client_nio_input: array U8.t;
  client_nio_input_len: SZ.t;
  client_nio_output: array U8.t;
  client_nio_output_len: SZ.t;
  client_nio_input_contents: Ghost.erased B.bytes;
  client_nio_old_output: Ghost.erased B.bytes;
  client_nio_raw_received: Ghost.erased B.bytes;
}

let client_network_io_continuation
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  (nio:client_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) sent **
  pure (
    nio.client_nio_input == V.vec_to_array frame.client_ep_raw /\
    nio.client_nio_output == V.vec_to_array frame.client_ep_network_out /\
    nio.client_nio_output_len == frame.client_ep_network_out_len /\
    B.length (Ghost.reveal nio.client_nio_input_contents) == SZ.v frame.client_ep_raw_len /\
    B.length (Ghost.reveal nio.client_nio_old_output) == SZ.v nio.client_nio_output_len)

let client_network_input (nio:client_network_io) : array U8.t =
  nio.client_nio_input

let client_network_input_len (nio:client_network_io) : SZ.t =
  nio.client_nio_input_len

let client_network_output (nio:client_network_io) : array U8.t =
  nio.client_nio_output

let client_network_output_len (nio:client_network_io) : SZ.t =
  nio.client_nio_output_len

let client_network_input_contents (nio:client_network_io) : Ghost.erased B.bytes =
  nio.client_nio_input_contents

let client_network_old_output (nio:client_network_io) : Ghost.erased B.bytes =
  nio.client_nio_old_output

fn client_prepare_network
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (network_frame:CP.tls_client_network_bridge_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame) **
  client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns nio:client_network_io
ensures
  client_network_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio **
  PE.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)) **
  CP.client_network_bridge_frame_pre
    network_frame
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)) **
  client_endpoint_network_continuation cc cfg frame (Ghost.reveal st) network_frame **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      (client_network_output_len nio))
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  V.to_array_pts_to frame.client_ep_raw;
  let nread = TCP.read_full ch (V.vec_to_array frame.client_ep_raw) frame.client_ep_raw_len;
  with raw_after chunk. _;
  let rawe = Ghost.hide (Seq.append raw_received chunk);
  assert (pure (Ghost.reveal rawe == Seq.append raw_received chunk));
  rewrite
    (TCP.is_channel ch (Seq.append raw_received chunk) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent));
  V.to_array_pts_to frame.client_ep_network_out;
  let inpute = Ghost.hide raw_after;
  let old_oute = Ghost.hide network_out_bytes;
  let nio = {
    client_nio_input = V.vec_to_array frame.client_ep_raw;
    client_nio_input_len = nread;
    client_nio_output = V.vec_to_array frame.client_ep_network_out;
    client_nio_output_len = frame.client_ep_network_out_len;
    client_nio_input_contents = inpute;
    client_nio_old_output = old_oute;
    client_nio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) (Ghost.reveal sent));
  fold (client_network_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) nio);
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointNeedInput network_frame));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_raw) raw_after)
    as
    (pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_network_out) network_out_bytes)
    as
    (pts_to (client_network_output nio) (Ghost.reveal (client_network_old_output nio)));
  fold (CQ.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  CQueries.prepare_client_next_action_network
    cc
    cfg
    frame.client_ep_query
    network_frame
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    st
    (client_network_input_contents nio)
    (client_network_old_output nio);
  unfold (CQ.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  fold (PE.network_buffers
    (client_network_input nio)
    (client_network_input_len nio)
    (client_network_output nio)
    (client_network_output_len nio)
    (Ghost.reveal (client_network_input_contents nio))
    (Ghost.reveal (client_network_old_output nio)));
  fold (client_endpoint_network_continuation cc cfg frame (Ghost.reveal st) network_frame);
  nio
}

fn client_finish_network_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (network_frame:CP.tls_client_network_bridge_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased B.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (consumed:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_endpoint_network_continuation cc cfg frame (Ghost.reveal st0) network_frame **
  CP.client_network_bridge_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1)
{
  unfold (client_endpoint_network_continuation cc cfg frame (Ghost.reveal st0) network_frame);
  CQueries.finish_client_next_action_network
    cc
    cfg
    frame.client_ep_query
    network_frame
    result
    input_contents
    input_len
    old_out
    out_contents
    st0
    st1
    consumed
    wire_outputs
    local_outputs;
  fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1))
}

fn client_finish_network_io
  (cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (nio:client_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased B.bytes)
  (sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (received1:Ghost.erased B.bytes)
  (sent1:Ghost.erased B.bytes)
  (st1:Ghost.erased CS.connection_state)
  (out_contents:Ghost.erased B.bytes)
  (consumed:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_network_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio **
  pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)) **
  pts_to (client_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CP.client_protocol_implementation.CPI.pi_system cc)
      (Ghost.reveal (client_network_input_contents nio))
      (client_network_input_len nio)
      (Ghost.reveal (client_network_old_output nio))
      (Ghost.reveal out_contents)
      (client_network_output_len nio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal consumed)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (client_network_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CP.client_protocol_implementation.CPI.pi_system cc)
    (Ghost.reveal (client_network_input_contents nio))
    (client_network_input_len nio)
    (Ghost.reveal (client_network_old_output nio))
    (Ghost.reveal out_contents)
    (client_network_output_len nio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  let nwritten = TCP.write ch (client_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.client_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.client_nio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (client_network_input nio) (Ghost.reveal (client_network_input_contents nio)))
    as
    (pts_to (V.vec_to_array frame.client_ep_raw) (Ghost.reveal (client_network_input_contents nio)));
  rewrite
    (pts_to (client_network_output nio) (Ghost.reveal out_contents))
    as
    (pts_to (V.vec_to_array frame.client_ep_network_out) (Ghost.reveal out_contents));
  V.to_vec_pts_to frame.client_ep_raw;
  V.to_vec_pts_to frame.client_ep_network_out;
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

noeq
type client_local_io = {
  client_lio_output: array U8.t;
  client_lio_output_len: SZ.t;
  client_lio_old_output: Ghost.erased B.bytes;
  client_lio_raw_received: Ghost.erased B.bytes;
}

let client_local_io_continuation
  (_cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (_received:B.bytes)
  (sent:B.bytes)
  (_st:CS.connection_state)
  (_ev:CTypes.client_local_event)
  (lio:client_local_io)
  : slprop =
  exists* raw_bytes.
    TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) sent **
    V.pts_to frame.client_ep_raw #1.0R raw_bytes **
    pure (
      lio.client_lio_output == V.vec_to_array frame.client_ep_network_out /\
      lio.client_lio_output_len == frame.client_ep_network_out_len /\
      B.length (Ghost.reveal lio.client_lio_old_output) == SZ.v lio.client_lio_output_len /\
      B.length raw_bytes == SZ.v frame.client_ep_raw_len)

let client_local_output (lio:client_local_io) : array U8.t =
  lio.client_lio_output

let client_local_output_len (lio:client_local_io) : SZ.t =
  lio.client_lio_output_len

let client_local_old_output (lio:client_local_io) : Ghost.erased B.bytes =
  lio.client_lio_old_output

fn client_prepare_local
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ch:TCP.channel)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame) **
  client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
returns lio:client_local_io
ensures
  client_local_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio **
  PE.local_output_buffer
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)) **
  CP.client_local_frame_pre
    ev
    local_frame
    (Ghost.reveal st)
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)) **
  client_endpoint_local_continuation cc cfg frame (Ghost.reveal st) ev local_frame
{
  unfold (client_endpoint_io_ready cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  with raw_received raw_bytes network_out_bytes. _;
  let rawe = Ghost.hide raw_received;
  let old_oute = Ghost.hide network_out_bytes;
  V.to_array_pts_to frame.client_ep_network_out;
  let lio = {
    client_lio_output = V.vec_to_array frame.client_ep_network_out;
    client_lio_output_len = frame.client_ep_network_out_len;
    client_lio_old_output = old_oute;
    client_lio_raw_received = rawe;
  };
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) (Ghost.reveal sent));
  fold (client_local_io_continuation cc ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) ev lio);
  unfold (client_endpoint_action_frame cc cfg frame (Ghost.reveal st) (PE.EndpointLocal ev local_frame));
  rewrite
    (pts_to (V.vec_to_array frame.client_ep_network_out) network_out_bytes)
    as
    (pts_to (client_local_output lio) (Ghost.reveal (client_local_old_output lio)));
  fold (CQ.local_output_buffer
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)));
  CQueries.prepare_client_next_action_local
    cc
    cfg
    frame.client_ep_query
    ev
    local_frame
    (client_local_output lio)
    (client_local_output_len lio)
    st
    (client_local_old_output lio);
  unfold (CQ.local_output_buffer
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)));
  fold (PE.local_output_buffer
    (client_local_output lio)
    (client_local_output_len lio)
    (Ghost.reveal (client_local_old_output lio)));
  fold (client_endpoint_local_continuation cc cfg frame (Ghost.reveal st) ev local_frame);
  lio
}

fn client_finish_local_action
  (cc:CP.canonical_client)
  (cfg:CQueries.client_next_local_action_config)
  (frame:client_endpoint_frame)
  (ev:CTypes.client_local_event)
  (local_frame:CP.tls_client_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased B.bytes)
  (out_contents:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (st1:Ghost.erased CS.connection_state)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_endpoint_local_continuation cc cfg frame (Ghost.reveal st0) ev local_frame **
  CP.client_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1)
{
  unfold (client_endpoint_local_continuation cc cfg frame (Ghost.reveal st0) ev local_frame);
  CQueries.finish_client_next_action_local
    cc
    cfg
    frame.client_ep_query
    ev
    local_frame
    result
    old_out
    out_contents
    st0
    st1
    wire_outputs
    local_outputs;
  fold (client_endpoint_frame_ready cc cfg frame (Ghost.reveal st1))
}

fn client_finish_local_io
  (cc:CP.canonical_client)
  (ch:TCP.channel)
  (frame:client_endpoint_frame)
  (lio:client_local_io)
  (ev:CTypes.client_local_event)
  (result:CPI.process_result)
  (received0:Ghost.erased B.bytes)
  (sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  (received1:Ghost.erased B.bytes)
  (sent1:Ghost.erased B.bytes)
  (st1:Ghost.erased CS.connection_state)
  (out_contents:Ghost.erased B.bytes)
  (wire_outputs:Ghost.erased (list CW.wire_message))
  (local_outputs:Ghost.erased (list CTypes.local_output))
requires
  client_local_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio **
  pts_to (client_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CP.client_protocol_implementation.CPI.pi_system cc)
      ev
      (Ghost.reveal (client_local_old_output lio))
      (Ghost.reveal out_contents)
      (client_local_output_len lio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1)
{
  unfold (client_local_io_continuation cc ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) ev lio);
  with raw_bytes. _;
  CPI.lemma_local_process_sent_output_prefix
    (CP.client_protocol_implementation.CPI.pi_system cc)
    ev
    (Ghost.reveal (client_local_old_output lio))
    (Ghost.reveal out_contents)
    (client_local_output_len lio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  let nwritten = TCP.write ch (client_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.client_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal lio.client_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.client_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.client_lio_raw_received) (Ghost.reveal sent1));
  rewrite
    (pts_to (client_local_output lio) (Ghost.reveal out_contents))
    as
    (pts_to (V.vec_to_array frame.client_ep_network_out) (Ghost.reveal out_contents));
  V.to_vec_pts_to frame.client_ep_network_out;
  fold (client_endpoint_io_ready cc ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1))
}

noextract
let client_protocol_endpoint
  : PE.protocol_endpoint
      CP.canonical_client
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      CTypes.local_output
      CP.client_protocol_implementation
  =
  {
    PE.pe_channel = TCP.channel;
    PE.pe_config = CQueries.client_next_local_action_config;
    PE.pe_frame = client_endpoint_frame;
    PE.pe_frame_ready = client_endpoint_frame_ready;
    PE.pe_io_ready = client_endpoint_io_ready;
    PE.pe_action_frame = client_endpoint_action_frame;
    PE.pe_network_continuation = client_endpoint_network_continuation;
    PE.pe_local_continuation = client_endpoint_local_continuation;
    PE.pe_next_action = client_endpoint_next_action;
    PE.pe_cancel_action = client_endpoint_cancel_action;
    PE.pe_finish_network_action = client_finish_network_action;
    PE.pe_finish_local_action = client_finish_local_action;
    PE.pe_network_io = client_network_io;
    PE.pe_network_io_continuation = client_network_io_continuation;
    PE.pe_network_input = client_network_input;
    PE.pe_network_input_len = client_network_input_len;
    PE.pe_network_output = client_network_output;
    PE.pe_network_output_len = client_network_output_len;
    PE.pe_network_input_contents = client_network_input_contents;
    PE.pe_network_old_output = client_network_old_output;
    PE.pe_prepare_network = client_prepare_network;
    PE.pe_finish_network_io = client_finish_network_io;
    PE.pe_local_io = client_local_io;
    PE.pe_local_io_continuation = client_local_io_continuation;
    PE.pe_local_output = client_local_output;
    PE.pe_local_output_len = client_local_output_len;
    PE.pe_local_old_output = client_local_old_output;
    PE.pe_prepare_local = client_prepare_local;
    PE.pe_finish_local_io = client_finish_local_io;
  }
